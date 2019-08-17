{-# LANGUAGE ScopedTypeVariables #-}
module Hypergeom where
import           Data.Array
import           Math.Combinat.Partitions.Integer.IntList (_dualPartition,
                                                           _isPartition,
                                                           _partitionsWithKParts)
import Data.Sequence (Seq, update, (|>))
import qualified Data.Sequence as S
import Data.List (nub, sort, sortOn, findIndex, elemIndex)

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

dico :: Int -> Int -> [Maybe Int]
dico m n = map (\x -> elemIndex (x ++ [1]) parts') (filter (\y -> length y < n) parts')
  where
  parts =
     nub $ concatMap (\i -> (concatMap (\j -> _partitionsWithKParts (min j i) i) [1 .. n] )) [1 .. m]
  parts' = sortOn length $ sort parts
      -- D <- rep(NA_integer_, Pmn)
      -- Last <- t(as.integer(c(0,m,m))) # il faut m > n (sinon l = 0 et Last est vide)
      -- fin <- 0L
      -- for(. in 1L:n){
      --   NewLast <- matrix(NA_integer_, nrow = 0L, ncol = 3L)
      --   for(i in 1L:nrow(Last)){
      --     manque <- Last[i,2L]
      --     l <- min(manque, Last[i,3L])
      --     if(l > 0L){
      --       D[Last[i,1L]+1L] <- fin + 1L
      --       s <- 1L:l
      --       NewLast <- rbind(NewLast, cbind(fin+s, manque-s, s))
      --       fin <- fin + l
      --     }
      --   }
      --   Last <- NewLast
      -- }
-- dico' :: Int -> Int -> Seq (Maybe Int)
-- dico' m n = go 1 [0] [m] [m] 0 (S.fromList (replicate 15 Nothing))
--   where
--   go :: Int -> [Int] -> [Int] -> [Int] -> Int -> Seq Int -> Seq Int
--   go k a' b' c' end' d'
--     | k == n = d'
--     | otherwise = inner 0 a' b' c' end' d'
--       where
--       inner :: Int -> [Int] -> [Int] -> [Int] -> Int -> Seq Int -> Seq Int
--       inner i a b c end d
--         | i == length a = d
--         | otherwise = if b!!i > 0
--           then let l = min ((b!!i) (c!!i)) in
--           let dd = update (a!!i) (end+1) d in
--           inner (i+1) (a ++ [end + 1 .. end + l]) (b ++ map (\x -> b!!i - x) [1 .. l]) (c ++ [1 .. l]) (end +l) dd
--           else inner (i+1) a b c end d
-- dico' :: Int -> Int -> Seq (Maybe Int)
-- dico' m n = go 1 (S.fromList (replicate 15 Nothing)) -- 15 to be replaced
--   where
--   go :: Int -> Seq (Maybe Int) -> Seq (Maybe Int)
--   go k d'
--     | k == n-1 = d'
--     | otherwise = go (k+1) (inner 0 [0] [m] [m] 0 d')
--       where
--       inner :: Int -> [Int] -> [Int] -> [Int] -> Int -> Seq (Maybe Int) -> Seq (Maybe Int)
--       inner i a b c end d
--         | i == length a = d
--         | otherwise = if b!!i > 0
--           then let l = min (b!!i) (c!!i) in
--           let dd = update (a!!i) (Just $ end+1) d in
--           inner (i+1) (a ++ [end + 1 .. end + l]) (b ++ map (\x -> b!!i - x) [1 .. l]) (c ++ [1 .. l]) (end + l) dd
--           else inner (i+1) a b c end d
-- a008284_row n = a008284_tabl !! (n-1)
a008284 :: [[Int]]
a008284 = [1] : f [[1]]
  where
  f xss = ys : f (ys : xss)
    where
    ys = map sum (zipWith take [1..] xss) ++ [1]

_P :: Int -> Int -> Int
_P m n = sum (concatMap (take (min m n)) (take m a008284))

dico' :: Int -> Int -> Seq (Maybe Int)
dico' m n = go 1 S.empty
  where
  pmn = Just $ _P m n
  go :: Int -> Seq (Maybe Int) -> Seq (Maybe Int)
  go k d'
    | k == n-1 = d'
    | otherwise = go (k+1) (inner 0 [0] [m] [m] 0 d' Nothing)
      where
      inner :: Int -> [Int] -> [Int] -> [Int] -> Int -> Seq (Maybe Int)
            -> Maybe Int -> Seq (Maybe Int)
      inner i a b c end d dlast
        | dlast == pmn = d
        | otherwise = let bi = b!!i in
          if bi > 0
            then let l = min bi (c!!i) in
              let ddlast = Just $ end + 1 in
              let dd = d |> ddlast in
              let range1l = [1 .. l] in
              inner (i+1) (a ++ [end + 1 .. end + l])
                          (b ++ map (\x -> bi - x) range1l)
                          (c ++ range1l) (end + l) dd ddlast
            else inner (i+1) a b c end (d |> Nothing) Nothing
