module Main where

import Data.Maybe
import Data.List
import Data.Set
import Data.Time.Clock.POSIX
import System.Random
import Debug.Trace
import Spark
import qualified Data.Set as Set

triangleCounting :: RandomGen g => g -> GraphRDD a b -> (VertexRDD Int, g)
triangleCounting g graphRdd = 
  let sendMsg src _ dst _ _ = [ (dst, singleton src), (src, singleton dst)]
      (msgs, g') = aggregateMessages g sendMsg (Set.union) graphRdd
      msg = concat msgs
      inMsgs i = hasKey i msg
      updt i attr =
        if inMsgs i then
          Set.delete i (fromJust ( lookup i msg))
        else
          Set.empty
      newG = mapVertices updt graphRdd
      sendMsg2 src srcAttr dst dstAttr _ = 
        let num = Data.Set.size (Data.Set.intersection srcAttr dstAttr) in
            [(dst, num),(src,num)]
      (msgs2, g'')  = aggregateMessages g' sendMsg2 (+) newG
      result = mapVertexRDD (\x y -> quot y 2) msgs2
      in (result,g'')


fourClique = Graph {
  vertexRdd = [[(0, Nothing), (1, Nothing), (2, Nothing)], [(3, Nothing)]],
  edgeRdd = [[(0, 1, Nothing), (0, 2, Nothing), (0, 3, Nothing), (1, 0, Nothing),(1, 2, Nothing),(1, 3, Nothing), (2, 1, Nothing), (2, 3, Nothing),(2, 0, Nothing)], [(3, 1, Nothing),(3, 2, Nothing),(3, 0, Nothing)]]
}

main = 
  do seed <- round `fmap` getPOSIXTime
     let (out1, g') = triangleCounting (mkStdGen seed) fourClique
     print out1


