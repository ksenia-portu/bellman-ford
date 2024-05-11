{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Dijkstra.Spec
( spec
)
where

import           Data.Graph.Prelude
import           Types.Edge
import           Types.Graph
import qualified Data.Graph.Digraph                 as Lib
import qualified Data.Graph.BellmanFord.Double      as BellmanFord
import qualified Data.Graph.Dijkstra                as Dijkstra

import qualified Control.Monad.Reader               as R
import qualified Control.Monad.ST                   as ST
import qualified Test.Hspec.SmallCheck              ()
import           Test.Hspec.Expectations.Pretty
import qualified Test.Tasty                         as Tasty
import qualified Test.QuickCheck as QC
import qualified Util.QuickSmall as QS
import Data.Bifunctor (bimap)

pathTo :: String -> Dijkstra.Dijkstra s String Double (Maybe [Lib.IdxEdge String Double])
pathTo = error "TODO"

spec :: Tasty.TestTree
spec = Tasty.testGroup "Dijkstra" . (: []) $
    Tasty.testGroup "same result as BellmanFord" $
        [ Tasty.testGroup "all paths from source" $
            mkTests
                dijkstraStr
                (pathTo . snd)
        , Tasty.testGroup "only source to target" $
            mkTests
                (const $ pure ())
                (\srcDst -> dijkstraSourceSinkStr srcDst >> pathTo (snd srcDst))
        ]
    where
        dijkstraStr
            :: (Show meta, Eq meta)
            => String
            -> Dijkstra.Dijkstra s String meta ()
        dijkstraStr str =
            withVid str Dijkstra.dijkstra

        dijkstraSourceSinkStr
            :: (Show meta, Eq meta)
            => (String, String)
            -> Dijkstra.Dijkstra s String meta ()
        dijkstraSourceSinkStr (str1, str2) = do
            withVid str1 $ \vid1 ->
                withVid str2 $ \vid2 ->
                    Dijkstra.dijkstraSourceSink (vid1, vid2)

        withVid str f = do
            g <- Dijkstra.getGraph
            mVid <- R.lift $ Lib.lookupVertex g str
            f $ fromMaybe (error $ "no such vertex ID: " <> show str) mVid

        mkTests
            :: ( v ~ String
               , meta ~ Double
               )
            => (forall s. String -> Dijkstra.Dijkstra s v meta ()) -- ^ arg: src
            -> (forall s. (String, String) -> Dijkstra.Dijkstra s v meta (Maybe [Lib.IdxEdge v meta])) -- ^ arg: (src, dst)
            -> [Tasty.TestTree]
        mkTests dijkstraInitSrc dijkstraSpTo =
            [ QS.testPropertyQC "for arbitrary graph" $ do
                edges <- arbitraryGraph QC.getNonNegative
                sameResultAsBellmanFord dijkstraInitSrc dijkstraSpTo (+) 0 edges
            ]

sameResultAsBellmanFord
    :: ( v ~ String
       , meta ~ Double
       )
    => (forall s. String -> Dijkstra.Dijkstra s v meta ())
    -- ^ Do initialization for new source vertex (arg: src)
    -> (forall s. (String, String) -> Dijkstra.Dijkstra s v meta (Maybe [Lib.IdxEdge v meta]))
    -- ^ Return a shortest path from src to dst (arg: (src, dst))
    -> (Double -> Double -> Double)
    -> Double
    -> [TestEdge Double]
    -> QC.Gen QC.Property
sameResultAsBellmanFord dijkstraInitSrc dijkstraSpTo combine zero edges = do
    shuffledEdges <- QC.shuffle edges
    let result = ST.runST $ do
            graph <- Lib.fromEdges shuffledEdges
            graphCopy <- copy graph
            vertices <- Lib.vertexLabels graph
            forM vertices $ \source -> do
                dijstraPaths <- Dijkstra.runDijkstra graph combine zero $ do
                    dijkstraInitSrc source
                    forM vertices $ \target -> do
                        mRes <- dijkstraSpTo (source, target)
                        forM mRes $ \res -> pure (source, target, res)
                bfPaths <- BellmanFord.runBF graphCopy combine zero $ do
                    BellmanFord.bellmanFord source
                    forM vertices $ \target -> do
                        mRes <- BellmanFord.pathTo target
                        forM mRes $ \res -> pure (source, target, res)
                pure (dijstraPaths, bfPaths)
    pure $ QC.property $ forM_ result $ \(dijstraPaths, bfPaths) -> do
        let resultPairs = zip dijstraPaths bfPaths
        unless (length resultPairs == length dijstraPaths) $
            fail $ "BUG: sameResultAsBellmanFord: non-equal resultPairs length: " <> show (dijstraPaths, bfPaths)
        forM resultPairs $ \(dijkstraPath, bfPath) -> do
            let pathWeight' mPath =
                    let getPath (_, _, edgeList) = edgeList
                    in pathWeight . getPath <$> mPath
            -- We may find two different paths, but the "length" (cumulative weight) of the two paths must be equal (except floating point errors)
            let pathLengths = bimap pathWeight' pathWeight' $ (dijkstraPath, bfPath)
            unless (uncurry mDoubleEqual pathLengths) $
                expectationFailure $ unlines
                    [ unwords
                        [ "Shortest paths not of equal length. Dijkstra length:"
                        , show (pathWeight' dijkstraPath) <> ","
                        , "Bellman-Ford length:"
                        , show $ pathWeight' bfPath
                        ]
                    , displayPath "BellmanFord" bfPath
                    , displayPath "Dijkstra" dijkstraPath
                    ]
    where
        displayPath name mPath =
            let mkDescr (src, dst, path) = unlines $
                    let fromTo = src <> "->" <> dst
                    in unwords ["Edges on", name, "path (" <> fromTo <> "): "] : map show path
            in maybe "Nothing" mkDescr mPath

        copy g = Lib.freeze g >>= Lib.thaw

        pathWeight = sum . map Lib.eMeta

        mDoubleEqual ma mb =
            case (ma, mb) of
                (Just a, Just b) -> abs (a - b) < epsilon
                (Nothing, Nothing) -> True
                _ -> False

        epsilon :: Double
        epsilon = 1.0e-13
