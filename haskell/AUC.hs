module Main where

import Data.List
import System.Random
import Spark

type Point = (Double, Double)

samplePoints :: (Double -> Double) -> Double -> Double 
                -> Int -> Partition Point
samplePoints f start end numSamples =
  let intervals = take (numSamples - 1)
        (repeat ((end - start) / (fromIntegral numSamples)))
      xs = map ((+) start) (map sum (inits intervals))
      ys = map f xs
  in zip xs ys

x3Rdd :: Int -> Int -> RDD Point
x3Rdd numSamples numPartitions =
  let x3 x = x ** 3.0
      interval = (2.0 - (-2.0)) / (fromIntegral numPartitions)
      nSamples = quot numSamples numPartitions
      last = samplePoints x3
               ( 2.0 - interval)
               ( 2.0 + (interval / fromIntegral nSamples))
               (succ nSamples)
      f i acc = (samplePoints x3 (-2.0 + (fromIntegral i) * interval) 
                                 (-2.0 + (fromIntegral (succ i)) * interval) 
                                 nSamples):acc
  in foldr f [last] [0..numPartitions-2]

x59Rdd :: Int -> Int -> RDD Point
x59Rdd numSamples numPartitions =
  let x59 x = x ** 59.0
      interval = (2.0 - (-2.0)) / (fromIntegral numPartitions)
      nSamples = quot numSamples numPartitions
      last = samplePoints x59 
               ( 2.0 - interval)
               ( 2.0 + (interval / fromIntegral nSamples))
               (succ nSamples)
      f i acc = (samplePoints x59 (-2.0 + (fromIntegral i) * interval) 
                                  (-2.0 + (fromIntegral (succ i)) * interval) 
                                  nSamples):acc
  in foldr f [last] [0..numPartitions-2]

trapezoid :: (Point, Point) -> Double
trapezoid ((ax, ay), (bx, by)) = (bx - ax) * (by + ay) / 2

sliding :: RDD a -> RDD (a, a)
sliding rdd =
  let f p (p', acc) = (p, (zip p (tail (p ++ p'))):acc)
  in snd (foldr f ([], []) rdd)

areaUnderCurve :: RandomGen g => g -> RDD Point -> (Double, g)
areaUnderCurve g rdd =
  let seqOp c p = c + trapezoid p
      combOp = (+)
  in aggregate g 0.0 seqOp combOp (sliding rdd)

main =
  print (fst (foldl f ([], mkStdGen 17) [1..50]))
  where rdd = x59Rdd 8000 100
        f (acc, g) _ = 
          let (r, g') = areaUnderCurve g rdd
          in (r:acc, g')
