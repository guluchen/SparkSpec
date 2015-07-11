module Main where

import Data.Time.Clock.POSIX
import System.Random
import Spark

threeCircle = Graph {
  vertexRdd = [[(0, Nothing)], [(1, Nothing), (2, Nothing)]],
  edgeRdd = [[(0, 1, Nothing)], [(1, 2, Nothing), (2, 0, Nothing)]]
}

fourCircle = Graph {
  vertexRdd = [[(0, Nothing), (1, Nothing), (2, Nothing)], [(3, Nothing)]],
  edgeRdd = [[(0, 1, Nothing), (1, 2, Nothing), (2, 3, Nothing)],
             [(3, 0, Nothing)]]
}

inDegrees :: RandomGen g => g -> GraphRDD a b -> (VertexRDD Int, g)
inDegrees g graphRdd = 
  let sendMsg _ _ dst _ _ = [(dst, 1)]
  in aggregateMessages g sendMsg (+) graphRdd

outDegrees :: RandomGen g => g -> GraphRDD a b -> (VertexRDD Int, g)
outDegrees g graphRdd = 
  let sendMsg src _ _ _ _ = [(src, 1)]
  in aggregateMessages g sendMsg (+) graphRdd

main = 
  do seed <- round `fmap` getPOSIXTime
     let (out1, g') = inDegrees (mkStdGen seed) threeCircle
         (out2, _ ) = outDegrees g' fourCircle
     print out1
     print out2
