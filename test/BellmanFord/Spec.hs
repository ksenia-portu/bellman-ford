{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module BellmanFord.Spec
( spec
)
where

import           Data.Graph.Prelude
import           Edge.Types
import qualified Data.Graph.Digraph                 as Lib
import qualified Data.Graph.BellmanFord             as Lib

import qualified Control.Monad.ST                   as ST
import qualified Test.Hspec.SmallCheck              ()
import           Test.Hspec.Expectations            (Expectation)
import qualified Test.Tasty                         as Tasty
import           Test.Tasty.SmallCheck              as SC


spec :: Tasty.TestTree
spec = Tasty.testGroup "BellmanFord" $
    [ Tasty.testGroup "additive (all weights)"
        [ SC.testProperty "passes 'check'" $ \edges ->
            bellmanFord (+) (edges :: [TestEdge])
        ]
    , Tasty.testGroup "multiplicative (positive weights)"
        [ SC.testProperty "passes 'check'" $ \edges ->
            bellmanFord (*) (map positiveWeight edges :: [TestEdge])
        ]
    , Tasty.testGroup "additive (all weights) -log weight"
        [ SC.testProperty "passes 'check'" $ \edges ->
            bellmanFord (+) (map NegLog edges :: [NegLog TestEdge])
        ]
    ]

bellmanFord
    :: (Lib.WeightedEdge e v Double, Eq e, Show e)
    => (Double -> Double -> Double)
    -> [e]
    -> Expectation
bellmanFord combine edges = do
    graph <- Lib.fromEdges edges
    vertices <- Lib.vertexLabels graph
    ST.stToIO $ forM_ vertices $ \source -> do
        Lib.runBF graph (\weight edge -> weight `combine` Lib.weight edge) $
            Lib.bellmanFord source
