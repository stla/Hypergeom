{-# LANGUAGE ScopedTypeVariables #-}
module Hypergeom where
import           Data.Array
import           Math.Combinat.Partitions.Integer.IntList (_dualPartition,
                                                           _isPartition)

_betaratio :: Fractional a => [Int] -> [Int] -> Int -> a -> a
_betaratio kappa mu k alpha = alpha * prod1 * prod2 * prod3
  where
  t = fromIntegral k - alpha * fromIntegral (mu !! (k-1))
  u = zipWith (\s kap -> t + 1 - fromIntegral s + alpha * fromIntegral kap)
               [1 .. k] (take k kappa)
  v = zipWith (\s m -> t - fromIntegral s + alpha * fromIntegral m)
               [1 .. k-1] (take (k-1) mu)
  mu' = take (mu!!(k-1)-1) (_dualPartition mu)
  w = zipWith (\s m -> fromIntegral m - t - alpha * fromIntegral s)
               [1 .. mu!!(k-1)-1] mu'
  prod1 = product $ map (\x -> x / (x+alpha-1)) u
  prod2 = product $ map (\x -> (x+alpha)/x) v
  prod3 = product $ map (\x -> (x+alpha)/x) w

_T :: Fractional a => a -> [a] -> [a] -> [Int] -> a
_T alpha a b kappa =
  if null kappa || kappa !! 0 == 0 then 1
    else prod1 * prod2 * prod3
    where
    kappai = last kappa
    kappai' = fromIntegral kappai
    i = fromIntegral $ length kappa
    c = kappai' - 1 - (i -1)/alpha
    d = kappai' * alpha -  i
    s = map fromIntegral [1 .. kappai - 1]
    kappa' = map fromIntegral $ take kappai (_dualPartition kappa)
    e = zipWith (\x y -> d - x*alpha + y) s kappa'
    g = map (+1) e
    s' = map fromIntegral [1 .. length kappa - 1]
    f = zipWith (\x y -> y*alpha - x - d) s' (map fromIntegral kappa)
    h = map (+ alpha) f
    l = zipWith (*) h f
    prod1 = product (map (+ c) a) / product (map (+ c) b)
    prod2 = product $ zipWith (\x y -> (y-alpha)*x/y/(x+alpha)) e g
    prod3 = product $ zipWith3 (\x y z -> (z-x)/(z+y)) f h l

hypergeoI :: forall a. Fractional a => Int -> a -> [a] -> [a] -> Int -> a -> a
hypergeoI m alpha a b n x =
  1 + summation 0 1 m []
  where
  summation :: Fractional a => Int -> a -> Int -> [Int] -> a
  summation i z j kappa = go 1 z 0
    where
    go :: Int -> a -> a -> a
    go kappai zz s
      | i == 0 && kappai > j || i>0 && kappai > min (kappa!!(i-1)) j = s
      | otherwise = go (kappai + 1) z' s''
      where
      kappa' = kappa ++ [kappai]
      t = _T alpha a b (filter (> 0) kappa')
      z' = zz * x * (fromIntegral (n-i) + alpha * (fromIntegral kappai-1)) * t
      s' = if j > kappai && i <= n
        then s + summation (i+1) z' (j-kappai) kappa'
        else s
      s'' = s' + z'
