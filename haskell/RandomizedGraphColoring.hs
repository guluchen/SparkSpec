module Main where

import Data.Maybe
import Data.List
import System.Random
import Data.Time.Clock.POSIX
import Spark

type Color = Int

-- convert directed to undirected graphs by adding reverse edges

fromDGToUG :: EdgeRDD b -> EdgeRDD b
fromDGToUG eRdd =
  map (concatMap (\(s, d, a) -> [(s, d, a), (d, s, a)])) eRdd

-- compute the maximal degree of a graph

maxDegreeOf :: RandomGen g => g -> GraphRDD a b -> (Int, g)
maxDegreeOf g graphRdd =
  let (dRdd, g') = aggregateMessages g 
                     (\_ _ dstId _ _ -> [(dstId, 1)]) (+) graphRdd
  in (foldl max 0 (map snd (concat dRdd)), g')

-- sample a color by a distribution

colorSampler :: [Double] -> Double -> Color
colorSampler dist p = 
  let f (color, mass) weight =
        (if m < p then succ color else color, m)
        where m = mass + weight
  in fst (foldl f (1, 0.0) dist)

-- random coloring

coloring :: RandomGen g => g -> GraphRDD Color b -> Double -> Int ->
            (GraphRDD Color b, g)
coloring g graphRdd beta numColors =
  let initColorDist = map (\_ -> 1.0 / fromIntegral numColors) [1..numColors]
      (seed, g') = random g
      distG = mapVertices
                (\i _ -> 
                   let (p, g) = random (mkStdGen (i * seed))
                   in (colorSampler initColorDist p, initColorDist, True, g))
                graphRdd
      sendMsg srcId (srcCol, _, srcAct, _) dstId (dstCol, _, dstAct, _) _ =
        if srcCol == dstCol then [(srcId, True), (dstId, True)]
        else (if srcAct then [(srcId, False)] else []) ++
             (if dstAct then [(dstId, False)] else [])
      vprog i (c, dist, _, g) active =
        let dist' = snd (foldl helper (1, []) dist)
              where helper (i, res) weight =
                      let decay = weight * (1 - beta)
                          d = if c == i 
                              then decay
                              else decay + beta / fromIntegral (numColors - 1)
                          e = if c == i then 1.0 else 0.0
                      in (succ i, if active then res ++ [d] else res ++ [e])
            (p, g') = random g
            c' = if active then colorSampler dist' p else c
        in (c', dist', active, g')
      (distG', g'') = pregel g' True vprog sendMsg (||) distG
   in (mapVertices (\_ (c, _, _, _) -> c) distG', g'')
                                          

-- a graph whose vertices are colored 1

graphRdd = Graph { vertexRdd = vRdd, edgeRdd = eRdd }
           where eRdd = [[(2, 1, Nothing), (3, 2, Nothing), 
                          (3, 1, Nothing), (7, 6, Nothing)],
                         [(7, 5, Nothing), (4, 2, Nothing), 
                          (7, 4, Nothing), (5, 1, Nothing)],
                         [(6, 5, Nothing), (6, 3, Nothing)]]
                 vRdd = [map (\i -> (i, 1)) [1..7]]

-- a complete n-graph with random paritioning

completeRdd :: RandomGen g => g -> Int -> (GraphRDD Color (Maybe b), g)
completeRdd g n = (Graph { vertexRdd = vRdd, edgeRdd = eRdd }, g'')
  where (vRdd, g') = repartitionR g (map (\i -> (i, 1)) [1..n])
        upto i edgs = foldl 
          (\res j -> (i, j, Nothing):res) edgs [1..(pred i)]
        edges m = foldl (\edgs i -> upto i edgs) [] [2..m]
        (eRdd, g'') = repartitionR g' (edges n)

main = 
  do seed <- round `fmap` getPOSIXTime
     let beta = 0.5
         (graphRdd, g) = completeRdd (mkStdGen seed) 20
--         g = mkStdGen seed
         (degree, g') = maxDegreeOf g graphRdd
         (outG, _) = coloring g' graphRdd beta (succ degree)
     print (vertexRdd outG)

