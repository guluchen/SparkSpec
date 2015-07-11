module Spark where

import Data.List
import Data.Maybe
import System.Random
import System.Random.Shuffle

type Partition a = [a]

type RDD a = [Partition a]

shuffleR :: RandomGen g => g -> [a] -> ([a], g)
shuffleR g [] = ([], g)
shuffleR g xs =
  let loop acc 0 g = (reverse acc, g)
      loop acc n g = let (r, g') = randomR (0, n) g
                     in loop (r:acc) (pred n) g'
      make_rs n g = loop [] n g
      (rs, g') = make_rs (length xs - 1) g 
  in (shuffle xs rs, g')

mapR :: RandomGen g => g -> (a -> b) -> [a] -> ([b], g)
mapR g f xs = shuffleR g (map f xs)

concatMapR :: RandomGen g => g -> (a -> [b]) -> [a] -> ([b], g)
concatMapR g f xs = (concat yss, g')
                    where (yss, g') = mapR g f xs

reducel :: (a -> a -> a) -> [a] -> a
reducel f (x:xs) = foldl f x xs

aggregate :: RandomGen g => 
             g -> b -> (b -> a -> b) -> (b -> b -> b) -> RDD a -> (b, g)
aggregate g z seq comb rdd =
    let (presults, g') = mapR g (foldl seq z) rdd in
    (foldl comb z presults, g')

reduce :: RandomGen g => g -> (a -> a -> a) -> RDD a -> (a, g)
reduce g comb rdd =
    let (presults, g') = mapR g (reducel comb) rdd in
    (reducel comb presults, g')

splitR :: RandomGen g =>
          g -> [a] -> ([a], [a], g)
splitR g xs =
  let (cut, g') = randomR (0, length xs) g
      (ls, rs) = splitAt cut xs
  in (ls, rs, g')

repartitionR :: RandomGen g => g -> [a] -> ([[a]], g)
repartitionR g [] = ([], g)
repartitionR g xs =
  let (ys, g') = shuffleR g xs
      f x (cur, g, acc) =
        let (cut, g') = random g
        in if cut then ([x], g', cur:acc)
            else (x:cur, g', acc)
      (p, g'', ps) = foldr f ([last ys], g', []) 
                      (reverse (tail (reverse ys)))
  in (p:ps, g'')

divideR :: RandomGen g =>
           g -> [a] -> ([a], a, a, [a], g)
divideR g xs =
  let (cut, g') = randomR (0, length xs - 2) g 
      (ls, l:r:rs) = splitAt cut xs
  in (ls, l, r, rs, g')

applyR :: RandomGen g =>
          g -> (b -> b -> b) -> Partition b -> (b, g)
applyR g comb [r] = (r, g)
applyR g comb [r, r'] = (comb r r', g)
applyR g comb rs = 
  let (ls', l', r', rs', g') = divideR g rs
  in applyR g' comb (ls' ++ [comb l' r'] ++ rs')

treeAggregate :: RandomGen g =>
                 g -> b -> (b -> a -> b) -> (b -> b -> b) -> RDD a -> (b, g)
treeAggregate g z seq comb rdd =
  let (presults, g') = mapR g (foldl seq z) rdd
  in applyR g' comb presults

treeReduce :: RandomGen g =>
              g -> (a -> a -> a) -> RDD a -> (a, g)
treeReduce g comb rdd =
  let (presults, g') = mapR g (reducel comb) rdd
  in applyR g' comb presults

type PairRDD a b = RDD (a, b)

hasKey :: Eq a => a -> Partition (a, b) -> Bool
hasKey key ps = case lookup key ps of
                  Just _  -> True   
                  Nothing -> False

hasValue :: Eq a => a -> b -> Partition (a, b) -> b
hasValue key val ps = case lookup key ps of
                        Just v -> v
                        Nothing -> val

addTo :: Eq a => a -> b -> Partition (a, b) -> Partition (a, b)
addTo key val ps = foldl (\r (k, v) -> if key == k then r else (k, v):r) 
                         [(key, val)] ps

aggregateByKey :: (Eq a, RandomGen g) => 
                  g -> c -> (c -> b -> c) -> (c -> c -> c) ->
                  PairRDD a b -> (PairRDD a c, g)
aggregateByKey g z mergeComb mergeValue pairRdd =
    let mergeBy f r (k, v) = 
            addTo k (f (hasValue k z r) v) r
        (preAgg, g') = 
            concatMapR g (foldl (mergeBy mergeComb) []) pairRdd
    in repartitionR g' (foldl (mergeBy mergeValue) [] preAgg)

aggregateWithKey :: (Eq a, RandomGen g) => g -> a -> c -> (c -> b -> c) -> 
                    (c -> c -> c) -> PairRDD a b -> (c, g)
aggregateWithKey g key z mergeComb mergeValue pairRdd =
  let select (k, _) = key == k
      vrdd = filter (not . null) 
             (map ((map snd) . (filter select)) pairRdd) in
  aggregate g z mergeComb mergeValue vrdd

reduceByKey :: (Eq a, RandomGen g) => 
               g -> (b -> b -> b) -> PairRDD a b -> (PairRDD a b, g)
reduceByKey g mergeValue pairRdd =
    let merge r (k, v) =
          case lookup k r of
            Just v' -> addTo k (mergeValue v' v) r
            Nothing -> addTo k v r
        (preAggrs, g') =
            concatMapR g (foldl merge []) pairRdd in
    repartitionR g' (foldl merge [] preAggrs)

reduceWithKey :: (Eq a, RandomGen g) => 
                 g -> a -> (b -> b -> b) -> PairRDD a b -> (b, g)
reduceWithKey g key mergeValue pairRdd =
  let select (k, _) = key == k
      vrdd = filter (not . null)
             (map ((map snd) . (filter select)) pairRdd) in
  reduce g mergeValue vrdd

type VertexId = Int
type VertexRDD a = PairRDD VertexId a
type EdgeRDD b = RDD (VertexId, VertexId, b)
data GraphRDD a b = Graph { vertexRdd :: VertexRDD a,
                            edgeRdd :: EdgeRDD b }

aggregateMessagesWithActiveVertices :: RandomGen g =>
  g -> (VertexId -> a -> VertexId -> a -> b -> [(VertexId, c)]) ->
  (c -> c -> c) -> [VertexId] -> GraphRDD a b -> 
  (VertexRDD c, g)
aggregateMessagesWithActiveVertices g sendMsg mergeMsg active graphRdd =
  let 
    isActive (srcId, dstId, _) = 
      srcId `elem` active || dstId `elem` active
    vAttrs = concat (vertexRdd graphRdd)
    f edge =
      if isActive edge then
        let (srcId, dstId, edgeAttr) = edge
            srcAttr = fromJust (lookup srcId vAttrs)
            dstAttr = fromJust (lookup dstId vAttrs) in
        sendMsg srcId srcAttr dstId dstAttr edgeAttr
      else []
    pairRdd = map (concatMap f) (edgeRdd graphRdd)
  in reduceByKey g mergeMsg pairRdd

aggregateMessages :: RandomGen g =>
  g -> (VertexId -> a -> VertexId -> a -> b -> [(VertexId, c)]) ->
  (c -> c -> c) -> GraphRDD a b -> (VertexRDD c, g)
aggregateMessages g sendMsg mergeMsg graphRdd =
  let vertices = concatMap (map fst) (vertexRdd graphRdd)
  in aggregateMessagesWithActiveVertices g
       sendMsg mergeMsg vertices graphRdd

mapVertexRDD :: (VertexId -> a -> b) -> VertexRDD a -> VertexRDD b
mapVertexRDD f vRdd = 
  map (map (\(i, attr) -> (i, f i attr))) vRdd

mapVertices :: (VertexId -> a -> c) -> GraphRDD a b -> GraphRDD c b
mapVertices updater gRdd =
  Graph {
    vertexRdd = mapVertexRDD updater (vertexRdd gRdd),
    edgeRdd = edgeRdd gRdd }

joinGraph :: (VertexId -> a -> c -> a) 
             -> GraphRDD a b -> VertexRDD c -> GraphRDD a b
joinGraph joiner gRdd vRdd =
  let assoc = concat vRdd
      updt i attr =
        case lookup i assoc of
          Just v  -> joiner i attr v
          Nothing -> attr
  in mapVertices updt gRdd

pregel :: RandomGen g => g -> c -> (VertexId -> a -> c -> a) ->
 (VertexId -> a -> VertexId -> a -> b -> [(VertexId, c)])
 -> (c -> c -> c) -> GraphRDD a b -> (GraphRDD a b, g)
pregel g initMsg vprog sendMsg mergeMsg graphRdd =
  let
    initG = let f i attr = vprog i attr initMsg in
      mapVertices f graphRdd
    (initVRdd, g') = aggregateMessages g sendMsg mergeMsg initG
    loop g curG [] = (curG, g)
    loop g curG vRdd =
      let
        curG' = joinGraph vprog curG vRdd
        active = concatMap (map fst) vRdd
        (vRdd', g') = aggregateMessagesWithActiveVertices g
                         sendMsg mergeMsg active curG'
      in loop g' curG' vRdd'
  in loop g' initG initVRdd

