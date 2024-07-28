{-# LANGUAGE StrictData #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
-- | Translation of Robert Sedgewick and Kevin Wayne's @IndexMinPQ.java@ to Haskell
--   with the addition of automatic growing.
--
--   Growing happens on an `insert` of an index that would otherwise fail with an
--   /index >= capacity/-error. The capacity is adjusted so the insert of the
--   index suceeds, but the new capacity is always at least doubled.
--
-- https://algs4.cs.princeton.edu/44sp/IndexMinPQ.java.html
module Data.IndexMinPQ
( IndexMinPQ
, newIndexMinPQ, newIndexMinPQTrace
, isEmpty
, insert
, minKey
, delMin
, delMinKey
, keyOf
, contains
, decreaseKey
, emptyAsSortedList
)
where

import Data.Graph.Prelude
import qualified Data.Primitive as MV
import qualified Data.Vector.Generic.Mutable as Vec
import qualified Data.Vector.Unboxed.Mutable as UVec
import qualified Data.Vector.Mutable as BVec
import Debug.Trace (traceM)
import qualified Control.Exception as Ex
import qualified System.IO.Unsafe as Unsafe
import Data.List (intercalate)


instance MonadFail (ST s) where
  fail = error $ "IndexMinPQ Failed"

-- | Indexed min priority queue.
--
-- See https://algs4.cs.princeton.edu/44sp/IndexMinPQ.java.html.
data IndexMinPQ s key = IndexMinPQ
  { indexMinPQ_maxN :: MV.MutVar s Int
    -- ^ maximum number of elements on PQ
  , indexMinPQ_n :: MV.MutVar s Int
    -- ^ number of elements on PQ
  , indexMinPQ_arrays :: MV.MutVar s (IndexMinPQArrays s key)
    -- ^ all the arrays
  , indexMinPQ_trace :: String -> ST s ()
    -- ^ print debug/trace info
  , indexMinPQ_traceInfo :: IndexMinPQ s key -> ST s String
    -- ^ additional debug info to print
  , indexMinPQ_traceShowKey :: key -> String
    -- ^ show a 'key' for tracing purposes
  }

data IndexMinPQArrays s key = IndexMinPQArrays
  { indexMinPQArrays_pq :: UVec.STVector s Int
    -- ^ binary heap using 1-based indexing
  , indexMinPQArrays_qp :: UVec.STVector s Int
    -- ^ inverse of pq - qp[pq[i]] = pq[qp[i]] = i
  , indexMinPQArrays_keys :: BVec.STVector s key
    -- ^ keys[i] = priority of i
    --
    --   NOTE: must be non-strict (since we store /bottom/ for non-existing keys).
  }

-- | Getter for @pq@ array
array_pq :: IndexMinPQ s key -> ST s (UVec.STVector s Int)
array_pq pq = indexMinPQArrays_pq <$> MV.readMutVar (indexMinPQ_arrays pq)

-- | Getter for @qp@ array
array_qp :: IndexMinPQ s key -> ST s (UVec.STVector s Int)
array_qp pq = indexMinPQArrays_qp <$> MV.readMutVar (indexMinPQ_arrays pq)

-- | Getter for @keys@ array
array_keys :: IndexMinPQ s key -> ST s (BVec.STVector s key)
array_keys pq = indexMinPQArrays_keys <$> MV.readMutVar (indexMinPQ_arrays pq)

-- | Grow 'IndexMinPQArrays' by the given number of elements
growArrays
  :: Int -- ^ maxN: old maximum queue size
  -> IndexMinPQArrays s key -- ^ old arrays
  -> Int -- ^ the number of elements to grow by
  -> ST s (IndexMinPQArrays s key) -- ^ new arrays
growArrays maxN arrays growSize = do
  when (growSize < 0) $
    fail $ "growArrays: bad growSize: " <> show growSize
  newPq <- safeGrow (indexMinPQArrays_pq arrays) (const 0)
  newQp <- safeGrow (indexMinPQArrays_qp arrays) $ const (-1)
  newKeys <- safeGrow (indexMinPQArrays_keys arrays) mkKeysError
  pure $ IndexMinPQArrays newPq newQp newKeys
  where
    uninitializedIndexRange = [maxN + 1 .. maxN + growSize] -- the newly created index range

    -- grow and initialize the new indices to the specified value
    safeGrow vector initVal = do
      newArray <- Vec.unsafeGrow vector growSize
      forM_ uninitializedIndexRange $ \i -> Vec.write newArray i (initVal i)
      pure newArray

assertFail
  :: String
  -> ST s a
assertFail =
  fail

debugTrace
  :: IndexMinPQ s key
  -> String
  -> ST s ()
debugTrace pq msg = do
  dbgInfo <- indexMinPQ_traceInfo pq pq
  indexMinPQ_trace pq $ msg <> ": " <> dbgInfo

debugShowState
  :: Show key
  => IndexMinPQ s key
  -> ST s String
debugShowState pq = do
  n <- MV.readMutVar (indexMinPQ_n pq)
  arrays <- MV.readMutVar (indexMinPQ_arrays pq)
  pq' <- showArray n (indexMinPQArrays_pq arrays)
  qp <- showArray n (indexMinPQArrays_qp arrays)
  keys <- showArrayWithBottoms n (indexMinPQArrays_keys arrays)
  maxN <- MV.readMutVar $ indexMinPQ_maxN pq
  pure $ unwords
    [ "IndexMinPQ {"
    , record "maxN" (show maxN)
    , record "n" (show n)
    , record "pq" pq'
    , record "qp" qp
    , record "keys" keys
    , "}"
    ]
  where
    record name val = name <> "=" <> val

newIndexMinPQ :: Int -> ST s (IndexMinPQ s key)
newIndexMinPQ = newIndexMinPQ' (const "") (const $ pure "") (const $ pure ())

newIndexMinPQTrace :: Show key => Int -> ST s (IndexMinPQ s key)
newIndexMinPQTrace = newIndexMinPQ' show debugShowState traceM

newIndexMinPQ'
  :: (key -> String) -- ^ show a 'key'
  -> (IndexMinPQ s key -> ST s String) -- ^ Produce a string that's added to the trace
  -> (String -> ST s ()) -- ^ Actually output the trace
  -> Int -- ^ initial queue size
  -> ST s (IndexMinPQ s key)
newIndexMinPQ' showKey traceInfo trace maxN = do
  -- Translation of IndexMinPQ constructor
  when (maxN < 0) $
    fail $ "newIndexMinPQ: Invalid maxN: " <> show maxN
  maxNVar <- MV.newMutVar maxN
  n <- MV.newMutVar 0
  pq <- Vec.replicate (maxN + 1) 0
  qp <- Vec.replicate (maxN + 1) (-1)
  keys <- Vec.generate (maxN + 1) mkKeysError
  arrays <- MV.newMutVar $ IndexMinPQArrays pq qp keys
  let queue = IndexMinPQ
        { indexMinPQ_trace = trace
        , indexMinPQ_traceInfo = traceInfo
        , indexMinPQ_traceShowKey = showKey
        , indexMinPQ_maxN = maxNVar
        , indexMinPQ_n = n
        , indexMinPQ_arrays = arrays
        }
  debugTrace queue $ "Created new IndexMinPQ of size " <> show maxN
  pure queue

isEmpty
  :: IndexMinPQ s key
  -> ST s Bool
isEmpty pq =
  (== 0) <$> MV.readMutVar (indexMinPQ_n pq)

insert
  :: (Ord key)
  => IndexMinPQ s key
  -> Int
  -> key
  -> ST s ()
insert pq i key = do
  growIfNeeded pq i
  validateIndex pq i
  whenM (contains pq i) $
    fail $ "index is already in the priority queue: " <> show i
  n <- modifyMutVar (indexMinPQ_n pq) (+ 1) -- n++
  arrays <- MV.readMutVar (indexMinPQ_arrays pq)
  write arrays indexMinPQArrays_qp i n -- qp[i] = n
  write arrays indexMinPQArrays_pq n i -- pq[n] = i
  write arrays indexMinPQArrays_keys i key -- keys[i] = key
  swim pq n -- swim(n)
  debugTrace pq $ "insert i=" <> show i <> " key=" <> showKey key
  where
    showKey = indexMinPQ_traceShowKey pq

minIndex
  :: IndexMinPQ s key
  -> ST s Int
minIndex pq = do
  assertQueueNotEmpty pq
  array_pq pq >>= (`Vec.read` 1)  -- return pq[1]

minKey
  :: IndexMinPQ s key
  -> ST s key
minKey pq = do
  minKeyIndex <- minIndex pq -- pq[1]
  array_keys pq >>= (`Vec.read` minKeyIndex) -- keys[pq[1]]

delMin
  :: (Ord key)
  => IndexMinPQ s key
  -> ST s Int
delMin pq = do
  min' <- minIndex pq -- int min = pq[1]
  prevN <- MV.atomicModifyMutVar' (indexMinPQ_n pq) (\n -> (n-1, n)) -- decrement "n", return original "n"
  exch pq 1 prevN -- exch(1, n--) -- NOTE: the unincremented "n" is passed to "exch" since the postfix decrement operator is used
  sink pq 1 -- sink(1)
  arrays <- MV.readMutVar (indexMinPQ_arrays pq)
  unlessM ((== min') <$> Vec.read (indexMinPQArrays_pq arrays) prevN) $ do
    debugTrace pq "debug info for below assertion failure"
    assertFail "Assertion failed: min == pq[n+1]"  -- assert min == pq[n+1]
  write arrays indexMinPQArrays_qp min' (-1) -- qp[min] = -1
  write arrays indexMinPQArrays_keys min' $ mkKeysError min' -- keys[min] = null
  write arrays indexMinPQArrays_pq prevN (-1) -- pq[n+1] = -1
  debugTrace pq "delMin"
  pure min'

-- | Same as 'delMin' but also return the associated key
delMinKey
  :: (Ord key)
  => IndexMinPQ s key
  -> ST s (Int, key)
delMinKey pq = do
  key <- minKey pq
  i <- delMin pq
  pure (i, key)

-- | Get the key for the given index.
--
--  Throws an error if the index does not exist.
keyOf
  :: IndexMinPQ s key
  -> Int
  -> ST s key
keyOf pq i = do
    unlessM (contains pq i) $
      fail $ "no such index: " <> show i
    array_keys pq >>= (`Vec.read` i)

contains
  :: IndexMinPQ s key
  -> Int
  -> ST s Bool
contains pq i = do
  validateIndex pq i
  (/= -1) <$> (array_qp pq >>= (`Vec.read` i)) -- return qp[i] != -1;

decreaseKey
  :: (Ord key)
  => IndexMinPQ s key
  -> Int
  -> key
  -> ST s ()
decreaseKey pq i key = do
  validateIndex pq i
  iKey <- keyOf pq i
  when (iKey == key) $ -- if (keys[i].compareTo(key) == 0)
    fail $ "Calling decreaseKey() with a key equal to the key in the priority queue. i=" <> show i <> ", key=" <> showKey key
  when (key > iKey) $ -- if (keys[i].compareTo(key) < 0)
    fail $ "Calling decreaseKey() with a key strictly greater than the key in the priority queue: i=" <> show i <> ", key=" <> showKey key <> ", iKey=" <> showKey iKey
  arrays <- MV.readMutVar (indexMinPQ_arrays pq)
  write arrays indexMinPQArrays_keys i key -- keys[i] = key
  Vec.read (indexMinPQArrays_qp arrays) i >>= swim pq -- swim(qp[i])
  debugTrace pq $ "decreaseKey " <> show i <> " " <> showKey key
  where
    showKey = indexMinPQ_traceShowKey pq

-- | Empty the queue and return the elements as a sorted list (increasing order)
emptyAsSortedList
  :: (Ord key)
  => IndexMinPQ s key
  -> ST s [(Int, key)]
emptyAsSortedList pq =
  go
  where
    go = do
      n <- MV.readMutVar (indexMinPQ_n pq)
      if n == 0
        then pure []
        else do
          iAndKey <- delMinKey pq
          (iAndKey :) <$> go

-- ***************************************************************************
-- * General helper functions.
-- ***************************************************************************

-- ^ Check if it's necessary to grow the arrays based on the index
growIfNeeded
  :: IndexMinPQ s key
  -> Int -- ^ Index
  -> ST s ()
growIfNeeded pq i = do
  maxN <- MV.readMutVar $ indexMinPQ_maxN pq
  when (i >= maxN) $
    grow maxN
  where
    grow maxN = do
      MV.writeMutVar (indexMinPQ_maxN pq) newSize
      arrays <- MV.readMutVar arraysVar
      newArrays <- growArrays maxN arrays growBySize
      MV.writeMutVar arraysVar newArrays
      debugTrace pq $ "Grew queue to size " <> show newSize <> ": i=" <> show i <> ", maxN=" <> show maxN
      where
        -- for performance, we want to at least double the size of the arrays when we resize them
        minGrowBySize = max maxN 1 -- gracefully handle the case where maxN=0
        growBySize = max (i + 1 - maxN) minGrowBySize
        newSize = maxN + growBySize
        arraysVar = indexMinPQ_arrays pq

validateIndex
  :: IndexMinPQ s key
  -> Int
  -> ST s ()
validateIndex pq i = do
  when (i < 0) $
    fail $ "index is negative: " ++ show i
  maxN <- MV.readMutVar $ indexMinPQ_maxN pq
  when (i >= maxN) $
    fail $ "index >= capacity: " ++ show i

assertQueueNotEmpty
  :: IndexMinPQ s key
  -> ST s ()
assertQueueNotEmpty pq =
  whenM ((== 0) <$> MV.readMutVar (indexMinPQ_n pq)) $
    fail "Priority queue underflow"

-- | The bottom value stored in unused indices of 'state_keys'.
--
-- In the Java version /null/ is used. But we use a value
-- with the same effect (a crash) but with a more descriptive
-- crash message.
mkKeysError :: Int -> key
mkKeysError i =
  error $ "BUG: 'state_keys' does not contain key for index: " <> show i

greater
  :: Ord key
  => IndexMinPQ s key
  -> Int
  -> Int
  -> ST s Bool
greater pq i j = do
  arrays <- MV.readMutVar (indexMinPQ_arrays pq)
  pqI <- Vec.read (indexMinPQArrays_pq arrays) i
  pqJ <- Vec.read (indexMinPQArrays_pq arrays) j
  pqIKey <- Vec.read (indexMinPQArrays_keys arrays) pqI
  pqJKey <- Vec.read (indexMinPQArrays_keys arrays) pqJ
  pure $ pqIKey > pqJKey

exch
  :: IndexMinPQ s key
  -> Int
  -> Int
  -> ST s ()
exch pq i j = do
  arrays <- MV.readMutVar (indexMinPQ_arrays pq)
  swap <- Vec.read (indexMinPQArrays_pq arrays) i -- int swap = pq[i];
  oldPqJ <- Vec.read (indexMinPQArrays_pq arrays) j -- "save the old pq[j] because we need to use it twice"
  write arrays indexMinPQArrays_pq i oldPqJ -- pq[i] = pq[j];
  write arrays indexMinPQArrays_pq j swap -- pq[j] = swap;
  write arrays indexMinPQArrays_qp oldPqJ i -- qp[oldPqJ] = i;
  write arrays indexMinPQArrays_qp swap j -- qp[swap] = j;
  debugTrace pq $ "exch " <> show i <> " " <> show j

--  ***************************************************************************
--  * Heap helper functions.
--  ***************************************************************************

swim
  :: (Ord key)
  => IndexMinPQ s key
  -> Int
  -> ST s ()
swim pq k =
  when (k > 1) $ do
    let halfOfK = k `div` 2
    whenM (greater pq halfOfK k) $ do
      exch pq k halfOfK -- exch(k, k/2);
      swim pq halfOfK -- k = k/2 (also acts as the "while" by recursing)

sink
  :: (Ord key)
  => IndexMinPQ s key
  -> Int
  -> ST s ()
sink pq k' = do
  go k'
  debugTrace pq $ "sink " <> show k'
  where
    go k = do
      n <- MV.readMutVar (indexMinPQ_n pq)
      when (2*k <= n) $ do
        let j = 2*k -- int j = 2*k
        jIsGreaterThanJPlusOne <- greater pq j (j+1)
        if (j < n && jIsGreaterThanJPlusOne) -- if (j < n && greater(j, j+1))
          then exchAndRecurse k (j+1)
          else exchAndRecurse k j

    -- does everything after the line
    --   if (j < n && greater(j, j+1)) j++;
    -- with either the original/unincremented "j" or the incremented "j"
    exchAndRecurse k j =
      whenM (greater pq k j) $ do -- if (!greater(k, j)) break;
        exch pq k j -- exch(k, j)
        go j -- k = j (also acts as the "while" by recursing)

--  ***************************************************************************
--  * Haskell helper functions.
--  ***************************************************************************

-- | Write a value to an array
write
  :: (Vec.MVector v a)
  => IndexMinPQArrays s key -- ^ Queue arrays
  -> (IndexMinPQArrays s key -> v s a) -- ^ Specific array
  -> Int -- ^ Index
  -> a -- ^ Value
  -> ST s ()
write pq arr =
  Vec.write (arr pq)

modifyMutVar
  :: PrimMonad m
  => MV.MutVar (PrimState m) a
  -> (a -> a)
  -> m a
modifyMutVar mv f =
  MV.atomicModifyMutVar' mv (\n -> let !n' = f n in (n', n'))

-- | Show the given number of elements from an array starting at index 1
showArray
  :: ( Vec.MVector v a
     , PrimMonad m
     , Show a
     )
  => Int -- ^ Number of elements to show (starting from index 1)
  -> v (PrimState m) a
  -> m String
showArray n array =
  show <$> Vec.foldr (:) [] (Vec.slice 1 n array)

-- | Show the given number of elements from an array starting at index 1,
--   with 'error' being shown as "null"
showArrayWithBottoms
  :: ( Vec.MVector v a
     , PrimMonad m
     , Show a
     )
  => Int -- ^ Number of elements to show (starting from index 1)
  -> v (PrimState m) a
  -> m String
showArrayWithBottoms n array = fmap showStrLst $
  map showBottomAsNull <$> Vec.foldr (:) [] (Vec.slice 1 n array)
  where
    showStrLst :: [String] -> String
    showStrLst lst = '[' : intercalate "," lst ++ "]"

    showBottomAsNull :: Show a => a -> String
    showBottomAsNull a = Unsafe.unsafePerformIO $
      showIt <$> Ex.try (Ex.evaluate a)
      where
        showIt :: Show b => Either Ex.ErrorCall b -> String
        showIt = either (const "null") show
