{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

-- | Translation of Sedgewick & Wayne's @EdgeWeightedDigraph.java@ to Haskell (https://algs4.cs.princeton.edu/44sp/EdgeWeightedDigraph.java.html).
--
--  Note that this supports only a single edge between two given vertices. In order to support multiple edges between two given vertices, you must change the graph's edge type to support it -- e.g. by using an edge type @NonEmpty e@ instead of @e@, and merging all edges that the same source and destination vertex into this non-empty list (which is what 'fromEdgesMulti' does).
module Data.Graph.Digraph
( -- * Graph
  Digraph
, fromEdges
, fromIdxEdges
, toEdges
, fromEdgesMulti
, updateEdge
, insertEdge
, removeEdge
, vertexCount
, edgeCount, edgeCountMulti
, vertices
, vertexLabels
, veticesAndLabels
, outgoingEdges
, outgoingEdges'
, foldEdges
, outgoingIncomingCount
, mapEdgeMeta
, lookupVertex
, lookupVertexId
, lookupEdge
, freeze
, thaw
, flipGraphEdges
, IDigraph
  -- * Edge/vertex
, VertexId
, vidInt
  -- NB: Export setter for the 'eMeta' record field
  --  but only getters for the remaining record fields
, IdxEdge
, eMeta
, eFrom
, eTo
, eFromIdx
, eToIdx
, flipEdge
  -- * Util
, graphToDot, graphToDotMulti, DotString(..)
  -- * Internal
, emptyClone
  -- * Re-exports
, E.DirectedEdge(..)
)
where

import Data.Graph.Prelude
import Protolude (NFData(rnf), Generic, Set, swap)
import qualified Data.Graph.Edge as E
import qualified Data.Graph.Util as U

import qualified Data.Array.ST as Arr
import qualified Data.Array.IArray as IArr
import qualified Data.HashTable.ST.Basic as HT
import Data.Ix (Ix(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as Set
import Data.List (sortOn)
import qualified Data.Text.Lazy as LT
import qualified Data.Map.Strict as Map

------------------------------------------------------------------
------------------  Edge with indexed vertices  ------------------
------------------------------------------------------------------

-- | An edge with indexed vertices
data IdxEdge v meta = IdxEdge
    { eMeta     :: !meta
    , _eFrom    :: !v
    , _eTo      :: !v
    , _eFromIdx :: {-# UNPACK #-} !VertexId
    , _eToIdx   :: {-# UNPACK #-} !VertexId
    } deriving (Eq, Show, Ord, Functor, Generic)

instance (NFData v, NFData meta) => NFData (IdxEdge v meta)

instance (Eq v, Hashable v) => E.DirectedEdge (IdxEdge v meta) v meta where
   fromNode = _eFrom
   toNode = _eTo
   metaData = eMeta

-- | Swap the from/to vertices of the edge.
--
--   E.g. the edge @"a"->"b"@ will become the edge @"b"->"a"@.
flipEdge
    :: IdxEdge v meta
    -> IdxEdge v meta
flipEdge edge =
    edge
    { _eFrom = _eTo edge
    , _eTo = _eFrom edge
    , _eFromIdx = _eToIdx edge
    , _eToIdx = _eFromIdx edge
    }

newtype VertexId = VertexId { _vidInt :: Int }
    deriving (Eq, Show, Ord, Hashable, Ix, NFData)

vidInt :: VertexId -> Int
vidInt = _vidInt

eFrom :: IdxEdge v meta -> v
eFrom = _eFrom

eTo :: IdxEdge v meta -> v
eTo = _eTo

eFromIdx :: IdxEdge v meta -> VertexId
eFromIdx = _eFromIdx

eToIdx :: IdxEdge v meta -> VertexId
eToIdx = _eToIdx


------------------------------------------------------------------
----------------------------  Graph  -----------------------------
------------------------------------------------------------------

data Digraph s v meta = Digraph
    { -- | vertex count
      digraphVertexCount :: {-# UNPACK #-} !Int
      -- | srcVertexId -> (dstVertexId -> srcToDstEdge)
      --
      -- NOTE: A 'HT.HashTable' is used instead of another array to avoid n² memory usage (where n = vertex count)
    , digraphVertexArray :: {-# UNPACK #-} !(Arr.STArray s VertexId (HT.HashTable s VertexId (IdxEdge v meta)))
      -- | v -> vertexId
    , digraphVertexIndex :: {-# UNPACK #-} !(HT.HashTable s v VertexId)
      -- | vertexId -> v
    , digraphVertexIdIndex :: {-# UNPACK #-} !(Arr.STArray s VertexId v)
    }

fromEdges
    :: forall v edge meta s.
       (Eq v, Ord v, Hashable v, E.DirectedEdge edge v meta)
    => [edge]
    -> ST s (Digraph s v meta)
fromEdges edges = do
    -- Create vertex->index map
    indexMap <- HT.newSized vertexCount' :: ST s (HT.HashTable s v VertexId)
    -- Initialize vertex-index map
    forM_ indexMapAssocs (uncurry $ HT.insert indexMap)
    -- Populate vertex array
    idxEdges <- mapM (createIdxEdge indexMap) edges
    indexMap' <- Arr.thaw indexMapI
    fromIdxEdges_ vertexCount' indexMap indexMap' idxEdges
  where
    vertexCount' = length uniqueVertices
    uniqueVertices = U.nubOrd $ map E.fromNode edges ++ map E.toNode edges
    indexMapAssocs = zip uniqueVertices (map VertexId [0..])
    indexMapI :: IArr.Array VertexId v
    indexMapI = IArr.array (VertexId 0, VertexId $ vertexCount' - 1) (map swap indexMapAssocs)

-- | An optimization of 'fromEdges' for 'IdxEdge' edges
fromIdxEdges
    :: forall s v meta.
       (Hashable v, Ord v)
    => [IdxEdge v meta]
    -> ST s (Digraph s v meta)
fromIdxEdges idxEdges = do
    -- Create vertex->index map
    indexMap <- HT.newSized vertexCount' :: ST s (HT.HashTable s v VertexId)
    -- Initialize vertex-index map
    forM_ uniqueVertices (uncurry $ HT.insert indexMap)
    indexMap' <- Arr.thaw indexMapI
    fromIdxEdges_ vertexCount' indexMap indexMap' idxEdges
  where
    vertexCount'
        | null idxEdges = 0
        | otherwise = 1 + vidInt (maximum $ map snd uniqueVertices)
    uniqueVertices = U.nubOrd $
        map (\e -> (eFrom e, eFromIdx e)) idxEdges ++
        map (\e -> (eTo e, eToIdx e)) idxEdges
    indexMapI :: IArr.Array VertexId v
    indexMapI = IArr.array (VertexId 0, VertexId $ vertexCount' - 1) (map swap uniqueVertices)

fromIdxEdges_
    :: Int
    -> HT.HashTable s v VertexId -- [(v, VertexId)]
    -> Arr.STArray s VertexId v
    -> [IdxEdge v meta]
    -> ST s (Digraph s v meta)
fromIdxEdges_ vertexCount' indexMap indexMap' idxEdges = do
    -- Initialize vertex array
    outEdgeMapList <- replicateM vertexCount' HT.new
    vertexArray <- Arr.newListArray (VertexId 0, VertexId (vertexCount' - 1)) outEdgeMapList
    -- Populate vertex array
    mapM_ (insertIdxEdge vertexArray) idxEdges
    return $ Digraph vertexCount' vertexArray indexMap indexMap'

toEdges
    :: (Ord meta, Ord v)
    => Digraph s v meta
    -> ST s (Set (IdxEdge v meta))
toEdges dg = do
    Arr.getElems (digraphVertexArray dg) >>= fmap (Set.fromList . concat) . traverse valueSet

-- | Fold over the edges in the graph, including the src and dst VertexId of each edge.
foldEdges
    :: Digraph s v meta
    -> (VertexId -> VertexId -> IdxEdge v meta -> b -> ST s b)
       -- ^ arguments: @srcVid dstVid edge state@
    -> b
       -- ^ initial state
    -> ST s b
foldEdges dg f initState = do
    srcEdgeTableList <- Arr.getAssocs (digraphVertexArray dg)
    srcDstEdgeList <- concat <$> traverse
        (\(srcVid, hashMap) -> map (srcVid,) <$> keyValueSet hashMap)
        srcEdgeTableList
    foldM (\state (srcVid, (dstVid, edge)) -> f srcVid dstVid edge state) initState srcDstEdgeList

-- | Count the number of outgoing and incoming edges for each vertex in the graph
outgoingIncomingCount
    :: Digraph s v meta
    -> ST s (Map.Map VertexId Word, Map.Map VertexId Word)
    -- ^ (outgoingCountMap, incomingCountMap),
    --
    -- ie. map of vertex to (number of edges /from/ this vertex, number of edges /to/ this vertex)
outgoingIncomingCount dg =
    foldEdges dg folder (Map.empty, Map.empty)
  where
    folder srcVid dstVid _ (outgoing, incoming) =
        pure (insertOrAddOne srcVid outgoing, insertOrAddOne dstVid incoming)

    insertOrAddOne k = Map.insertWith (+) k 1

-- | One or more edges with the same src and dst vertex
data NonEmptyEdges v meta = NonEmptyEdges
    { _NonEmptyEdges_from :: !v
    , _NonEmptyEdges_to :: !v
    , _NonEmptyEdges_meta :: !(NE.NonEmpty meta)
    }

instance (Eq v, Hashable v) => E.DirectedEdge (NonEmptyEdges v meta) v (NE.NonEmpty meta) where
    fromNode = _NonEmptyEdges_from
    toNode   = _NonEmptyEdges_to
    metaData = _NonEmptyEdges_meta

-- | Create a graph that supports multiple edges that share src vertex and dst vertex
fromEdgesMulti
    :: forall s edge v meta.
       (Eq v, Ord v, Hashable v, E.DirectedEdge edge v meta)
    => Set edge
    -> ST s (Digraph s v (NE.NonEmpty meta))
fromEdgesMulti =
    fromEdges
        . map groupedEdgesToNonEmptyEdges
        . groupOn fromTo
  where
    fromTo e = (E.fromNode e, E.toNode e)

    groupOn :: (Ord b) => (a -> b) -> Set a -> [NE.NonEmpty a]
    groupOn f = NE.groupBy (\a1 a2 -> f a1 == f a2) . sortOn f . Set.toList

    -- Invariant: all the edges in the input list share src node and dst node
    groupedEdgesToNonEmptyEdges :: NE.NonEmpty edge -> NonEmptyEdges v meta
    groupedEdgesToNonEmptyEdges edges =
        let edge = NE.head edges
        in NonEmptyEdges (E.fromNode edge) (E.toNode edge) (fmap E.metaData edges)

-- | Return a copy of the input graph where 'flipEdge' has been applied to all edges in the graph
flipGraphEdges
    :: Digraph s v meta
    -> ST s (Digraph s v meta)
flipGraphEdges g = do
    vertexList <- vertices g
    edges <- forM vertexList (outgoingEdges g)
    fromIdxEdges_ (digraphVertexCount g) (digraphVertexIndex g) (digraphVertexIdIndex g) (map flipEdge $ concat edges)

-- | An immutable form of 'Digraph'
data IDigraph v meta =
    IDigraph
        !Int
        -- ^ Vertex count
        !(IArr.Array VertexId (Map.Map VertexId (IdxEdge v meta)))
        -- ^ Outgoing edges array
        !(Map.Map v VertexId)
        -- ^ vertex-to-VertexId map
            deriving (Eq, Show)

instance (NFData v, NFData meta) => NFData (IDigraph v meta) where
    rnf (IDigraph vc vertexArray indexMap) =
        rnf vc `seq`
        rnf (IArr.assocs vertexArray) `seq`
        rnf indexMap

-- | Convert a mutable graph into an immutable graph.
freeze
    :: Ord v
    => Digraph s v meta
    -> ST s (IDigraph v meta)
freeze (Digraph vc vertexArray indexMap _) = do
    vertexArray' <- mapM hashTableToMap =<< Arr.freeze vertexArray
    indexMap' <- hashTableToMap indexMap
    return $ IDigraph vc vertexArray' indexMap'

-- | Convert an immutable graph into an mutable graph.
thaw
    :: forall s v meta.
       (Eq v, Hashable v)
    => IDigraph v meta
    -> ST s (Digraph s v meta)
thaw (IDigraph vc frozenArray indexKv) = do
    htArray <- mapM fromMap frozenArray
    vertexArray <- Arr.thaw htArray
    indexMap <- fromMap indexKv
    indexMap' <- Arr.thaw indexMapI
    return $ Digraph vc vertexArray indexMap indexMap'
  where
    indexMapI :: IArr.Array VertexId v
    indexMapI = IArr.array (VertexId 0, VertexId $ vc - 1) (map swap $ Map.assocs indexKv)

    fromMap map' = do
        ht <- HT.newSized (Map.size map')
        foldM (\ht' (k,v) -> HT.insert ht' k v >> return ht') ht (Map.assocs map')

-- | Return a copy of the input graph that has the same vertices
--   but with all edges removed.
emptyClone
    :: forall s v meta.
       Digraph s v meta
    -> ST s (Digraph s v meta)
emptyClone (Digraph vc _ indexMap indexMap') = do
    emptyMaps <- sequence $ replicate vc HT.new
    newVertexArray <- Arr.newListArray (VertexId 0, VertexId (vc - 1)) emptyMaps
    -- Keeping the same 'indexMap' is safe since it is not modified after graph creation
    return $ Digraph vc newVertexArray indexMap indexMap'

-- | Map the metadata of an edge
mapEdgeMeta
    :: ( Hashable v
       , Ord meta
       , Ord v
       )
    => (meta -> ST s meta')
    -> Digraph s v meta
    -> ST s (Digraph s v meta')
mapEdgeMeta f dg = do
    -- TODO: optimize
    edges <- toEdges dg
    edges' <- mapM mapFun (Set.toList edges)
    fromEdges edges'
  where
    mapFun idxEdge = do
        meta' <- f (eMeta idxEdge)
        pure $ idxEdge{ eMeta = meta' }

createIdxEdge
    :: E.DirectedEdge edge v meta
    => HT.HashTable s v VertexId
    -> edge
    -> ST s (IdxEdge v meta)
createIdxEdge indexMap edge = do
    fromIdx <- lookup' from
    toIdx <- lookup' to
    let idxEdge = IdxEdge { eMeta = E.metaData edge, _eFrom = from, _eTo = to, _eFromIdx = fromIdx, _eToIdx = toIdx }
    pure idxEdge
  where
    from = E.fromNode edge
    to = E.toNode edge
    lookup' = fmap (fromMaybe (error "BUG: lookup indexMap")) . HT.lookup indexMap

-- | Look up vertex by 'VertexId'
lookupVertexId
    :: (Eq v, Hashable v)
    => Digraph s v meta
    -> VertexId
    -> ST s (Maybe v)
lookupVertexId dg vertex =
    digraphVertexIdIndex dg !? vertex
  where
    (!?) :: (Arr.MArray a e m, Ix i) => a i e -> i -> m (Maybe e)
    (!?) arr i = do
        b <- Arr.getBounds arr
        if inRange b i
            then Just <$> Arr.readArray arr i
            else pure Nothing

-- | Look up vertex by label
lookupVertex
    :: (Eq v, Hashable v)
    => Digraph s v meta
    -> v
    -> ST s (Maybe VertexId)
lookupVertex (Digraph _ _ indexMap _) vertex = do
    HT.lookup indexMap vertex

-- | Look up edge by (src, dst) vertex labels
lookupEdge
    :: (Eq v, Hashable v)
    => Digraph s v meta
    -> (v, v) -- ^ (src, dst)
    -> ST s (Maybe (IdxEdge v meta))
lookupEdge dg (src, dst) = do
    mSrcIdx <- lookupVertex dg src
    mDstIdx <- lookupVertex dg dst
    fmap (join . join) $
        forM mSrcIdx $ \srcIdx -> do
            forM mDstIdx $ \dstIdx -> do
                Arr.readArray (digraphVertexArray dg) srcIdx >>= (`HT.lookup` dstIdx)

insertIdxEdge
    :: Arr.STArray s VertexId (HT.HashTable s VertexId (IdxEdge v meta))
    -> IdxEdge v meta
    -> ST s ()
insertIdxEdge vertexArray idxEdge@IdxEdge{..} = do
    outEdgeMap <- Arr.readArray vertexArray _eFromIdx
    HT.insert outEdgeMap _eToIdx idxEdge

-- Overwrite an existing edge in the graph
updateEdge
    :: Digraph s v meta
    -> IdxEdge v meta
    -> ST s ()
updateEdge (Digraph _ vertexArray _ _) = insertIdxEdge vertexArray

-- Insert/overwrite an existing edge in the graph
insertEdge
    :: Digraph s v meta
    -> IdxEdge v meta
    -> ST s ()
insertEdge = updateEdge

-- -- | Remove an existing edge from the graph
removeEdge
    :: Digraph s v meta
    -> IdxEdge v a
    -> ST s ()
removeEdge (Digraph _ vertexArray _ _) IdxEdge{..} = do
    outEdgeMap <- Arr.readArray vertexArray _eFromIdx
    HT.delete outEdgeMap _eToIdx

-- -- | Count of the number of vertices in the graph
vertexCount
    :: Digraph s v meta
    -> ST s Word
vertexCount (Digraph vc _ _ _) = return $ fromIntegral vc

-- | Count of the number of edges in the graph
edgeCount
    :: Digraph s v meta
    -> ST s Word
edgeCount =
    edgeCountGeneric HT.size

-- | Count the number of edges in the graph, with a single 'NE.NonEmpty'
--   edge counting as the /length/ of the non-empty list.
--
--   Useful for graphs created with 'fromEdgesMulti'.
edgeCountMulti
    :: Digraph s v (NE.NonEmpty meta)
    -> ST s Word
edgeCountMulti = do
    edgeCountGeneric $ \ht -> do
        idxEdgeList <- valueSet ht
        pure $ sum $ map (NE.length . eMeta) idxEdgeList

edgeCountGeneric
    :: (HT.HashTable s VertexId (IdxEdge v meta) -> ST s Int)
    -> Digraph s v meta
    -> ST s Word
edgeCountGeneric countM dg@(Digraph _ vertexArray _ _) = do
    vertexIdList <- vertices dg
    outEdgeMapList <- mapM (Arr.readArray vertexArray) vertexIdList
    countList <- mapM countM outEdgeMapList
    return $ fromIntegral $ sum countList

-- | All the vertices in the graph
vertices
    :: Digraph s v meta
    -> ST s [VertexId]
vertices (Digraph vc _ _ _) =
    return vertexIdList
  where
    vertexIdList = map VertexId [0..vc-1]
    -- NB: If @vc@ equals zero (in case of an empty list passed to 'fromEdges')
    --  and it had the type 'Word', then @vc-1@ would evaluate to 'maxBound'.
    -- Thus @[0..vc-1]@ would produce a list of length 2^32 or 2^64 (depending
    --  on CPU word size).

-- | All the vertex labels in the graph
vertexLabels
    :: Digraph s v meta
    -> ST s [v]
vertexLabels (Digraph _ _ indexMap _) =
    keySet indexMap

-- | All the vertices in the graph including vertex labels
veticesAndLabels
    :: Digraph s v meta
    -> ST s [(v, VertexId)]
veticesAndLabels (Digraph _ _ indexMap _) =
    keyValueSet indexMap

-- | All edges going out of the given vertex
outgoingEdges
    :: Digraph s v meta
    -> VertexId
    -> ST s [IdxEdge v meta]
outgoingEdges (Digraph _ vertexArray _ _) vid = do
    outEdgeMap <- Arr.readArray vertexArray vid
    valueSet outEdgeMap

-- | Same as 'outgoingEdges' but takes vertex label as input.
--  Returns 'Nothing' in case the given vertex label does not exist
outgoingEdges'
    :: (Eq v, Hashable v)
    => Digraph s v meta
    -> v
    -> ST s (Maybe [IdxEdge v meta])
outgoingEdges' dg v = do
    vidM <- lookupVertex dg v
    maybe (return Nothing) (fmap Just . outgoingEdges dg) vidM

-- | The types of strings supported by the DOT language.
--
--   Cf. https://graphviz.org/doc/info/lang.html
data DotString
    = DotString_DoubleQuoted LT.Text
    -- ^ A double-quoted string.
    --   When rendering to the DOT language, the provided string is surrounded by double quotes
    --   and any double quotes in the provided string are escaped.
    | DotString_Raw LT.Text
    -- ^ A "raw" string: you are responsible for properly quoting the string.
    --   Used for e.g. HTML strings.
        deriving (Eq, Ord, Show)

renderDotString :: DotString -> LT.Text
renderDotString (DotString_DoubleQuoted txt) =
    let escape = LT.replace "\"" "\\\"\\"
        quote txt' = "\"" <> txt' <> "\""
    in quote $ escape txt
renderDotString (DotString_Raw txt) = txt

-- | TODO: better name
graphToDot
    :: (v -> Map.Map LT.Text DotString)
    -- ^ Vertex attributes. A map from attribute name to value.
    -> (IdxEdge v meta -> Set.Set (Map.Map LT.Text DotString))
    -- ^ Edge attributes. A map from attribute name to value.
    --
    -- This is a 'Set.Set' because a 'Digraph' supports only a single edge between two specific vertices.
    -- So if you use e.g. a 'NE.NonEmpty' of edges as the graph metadata to get around this,
    -- then you'll want this function to produce one label for each edge in this non-empty list.
    -> DotString
    -- ^ Graph name
    -> Digraph s v meta
    -> ST s LT.Text
graphToDot mkVertexAttrs mkEdgeAttrs gLabel g = do
    res <- veticesAndLabels g
    nodesAndEdges <- forM res $ \(v, vid) -> do
        edges <- outgoingEdges g vid
        pure ((v, vid), edges)
    pure $ mkGraph nodesAndEdges
  where
    showVertexId = LT.pack . show . vidInt

    mkNode (v, idx) = statement $ LT.unwords
        [ showVertexId idx
        , mkLabels (mkVertexAttrs v)
        ]

    mkEdge idxEdge edgeLabels =
        statement $ LT.unwords
            [ showVertexId $ eFromIdx idxEdge
            , "->"
            , showVertexId $ eToIdx idxEdge
            , mkLabels edgeLabels
            ]

    mkEdges idxEdge =
        map (mkEdge idxEdge) (Set.toList $ mkEdgeAttrs idxEdge)

    mkNodeAndEdges (vertex, idxEdges) =
          mkNode vertex
        : concatMap mkEdges idxEdges

    mkGraph nodesAndEdges = mkDigraph $ LT.unlines $
          statement (mkAttr "label" gLabel)
        : concatMap mkNodeAndEdges nodesAndEdges

    mkDigraph txt = "digraph {\n" <> txt <> "\n}"

    mkLabels :: Map.Map LT.Text DotString -> LT.Text
    mkLabels lblMap =
        let renderLabel = uncurry mkAttr
        in bracketize $ LT.intercalate ", " $ renderLabel <$> Map.toList lblMap

    mkAttr name value = name <> " = " <> renderDotString value
    bracketize txt = "[" <> txt <> "]"
    statement txt = txt <> ";"

-- | Same as 'graphToDot' but specialized to graphs that use a 'NE.NonEmpty' as graph metadata,
--   as produced by e.g. 'fromEdgesMulti'.
graphToDotMulti
    :: forall v meta s.
       (v -> Map.Map LT.Text DotString)
    -> (IdxEdge v meta -> Map.Map LT.Text DotString)
    -> DotString
    -> Digraph s v (NE.NonEmpty meta)
    -> ST s LT.Text
graphToDotMulti mkVertexLabel mkEdgeLabel =
    graphToDot mkVertexLabel mkEdgeLabel'
  where
    conv :: IdxEdge v (NE.NonEmpty meta) -> NE.NonEmpty (IdxEdge v meta)
    conv edge =
        let nonEmptyMetas = eMeta edge
            mkEdge meta = edge{ eMeta = meta }
        in mkEdge <$> nonEmptyMetas

    mkEdgeLabel' = Set.fromList . map mkEdgeLabel . NE.toList . conv

-- | Set of map keys
keySet
    :: HT.HashTable s k v
    -> ST s [k]
keySet =
    HT.foldM (\accum (k, _) -> return $ k : accum) []

-- | Set of map values
valueSet
    :: HT.HashTable s k v
    -> ST s [v]
valueSet =
    HT.foldM (\accum (_, v) -> return $ v : accum) []

-- | Set of map values
keyValueSet
    :: HT.HashTable s k v
    -> ST s [(k,v)]
keyValueSet =
    HT.foldM (\accum kv -> return $ kv : accum) []

-- | Convert a 'HT.HashTable' to a 'Map.Map',
hashTableToMap
    :: Ord k
    => HT.HashTable s k v
    -> ST s (Map.Map k v)
hashTableToMap =
    HT.foldM (\(!accum) (k, v) -> return $ Map.insert k v accum) Map.empty
