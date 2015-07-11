module Main where

import Data.Maybe
import Data.List
import Data.Set
import Data.Time.Clock.POSIX
import System.Random
import Debug.Trace
import Spark
import qualified Data.Set as Set



connectedComponent :: RandomGen g => g -> GraphRDD a b -> (GraphRDD Int b, g)
connectedComponent g graphRdd = 
  let newG = mapVertices (\i _ -> i) graphRdd
      initMsg = maxBound :: Int
      vprog _ attr msg = min attr msg
      sendMsg src srcA dst dstA _ =
        if srcA < dstA then [(dst, srcA)]
        else if dstA < srcA then [(src, dstA)]
        else []
      in pregel g initMsg vprog sendMsg min newG
         

fourClique = Graph {
  vertexRdd = [[(0, 1), (1, 2), (2, 3)], [(3, 4)]],
  edgeRdd = [[(0, 1, Nothing), (0, 2, Nothing), (0, 3, Nothing), (1, 0, Nothing),(1, 2, Nothing),(1, 3, Nothing), (2, 1, Nothing), (2, 3, Nothing),(2, 0, Nothing)], [(3, 1, Nothing),(3, 2, Nothing),(3, 0, Nothing)]]
}

main = 
  do seed <- round `fmap` getPOSIXTime
     let (out1, g') = connectedComponent (mkStdGen seed) fourClique
     print (vertexRdd fourClique)
     print (vertexRdd out1)
