{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Hypergeom10 where
import           Control.Lens                             hiding ((|>))
import           Control.Monad                            (when)
import           Data.Array.Unboxed
import           Data.Array.IO
import           Data.List                                (elemIndex)
import           Data.Maybe
import           Data.Sequence                            (Seq, (|>))
import qualified Data.Sequence                            as S
import           Math.Combinat.Partitions.Integer.IntList (_dualPartition)

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

-- hypergeoI :: forall a. Fractional a => Int -> a -> [a] -> [a] -> Int -> a -> a
-- hypergeoI m alpha a b n x =
--   1 + summation 0 1 m []
--   where
--   summation :: Fractional a => Int -> a -> Int -> [Int] -> a
--   summation i z j kappa = go 1 z 0
--     where
--     go :: Int -> a -> a -> a
--     go kappai zz s
--       | i == 0 && kappai > j || i>0 && kappai > min (kappa!!(i-1)) j = s
--       | otherwise = go (kappai + 1) z' s''
--       where
--       kappa' = kappa ++ [kappai]
--       t = _T alpha a b (filter (> 0) kappa')
--       z' = zz * x * (fromIntegral (n-i) + alpha * (fromIntegral kappai-1)) * t
--       s' = if j > kappai && i <= n
--         then s + summation (i+1) z' (j-kappai) kappa'
--         else s
--       s'' = s' + z'

a008284 :: [[Int]]
a008284 = [1] : f [[1]]
  where
  f xss = ys : f (ys : xss)
    where
    ys = map sum (zipWith take [1..] xss) ++ [1]

_P :: Int -> Int -> Int
_P m n = sum (concatMap (take (min m n)) (take m a008284))

_dico :: Int -> Int -> Seq (Maybe Int)
_dico pmn m = go False S.empty
  where
  go :: Bool -> Seq (Maybe Int) -> Seq (Maybe Int)
  go k !d'
    | k = d' 
    | otherwise = inner 0 [0] [m] [m] 0 d' Nothing
      where
      inner :: Int -> [Int] -> [Int] -> [Int] -> Int -> Seq (Maybe Int)
            -> Maybe Int -> Seq (Maybe Int)
      inner i a b c end d dlast
        | dlast == Just pmn = go True d
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

_nkappa :: Seq (Maybe Int) -> [Int] -> Int
_nkappa dico kappa = if null kappa
  then 0
  else fromJust (dico `S.index` _nkappa dico (init kappa)) + last kappa - 1

cleanPart :: [Int] -> [Int]
cleanPart kappa =
  let i = elemIndex 0 kappa in
  if isJust i then take (fromJust i) kappa else kappa

summation :: forall a. (Fractional a, MArray IOUArray a IO) => 
             Int -> [a] -> [a] -> [a] -> Seq (Maybe Int) -> Int -> a 
             -> Int -> a -> Int -> [Int] -> IOUArray (Int, Int) a -> IO a
summation m a b x dico n alpha i z j kappa jarray = do -- m inutile
  let go :: Int -> a -> a -> IO a
      go kappai !z' !s
        | i == n || 
          i == 0 && kappai > j || 
          i > 0 && kappai > min (last kappa) j = return s
        | otherwise = do
          let kappa' = cleanPart $ (element i .~ kappai) (kappa ++ repeat 0)
              nkappa = _nkappa dico kappa'        
              z'' = z' * _T alpha a b kappa'
          when (nkappa>1 && (length kappa' == 1 || kappa'!!1 == 0)) $ do 
            entry <- readArray jarray (nkappa-1, 1) 
            let newval = x!!0 * (1 + alpha * fromIntegral (kappa'!!0 - 1)) * entry
            writeArray jarray (nkappa, 1) newval
          let go' :: Int -> IO ()
              go' t 
                | t == n + 1 = return ()
                | otherwise = do
                  _ <- jack alpha x dico 0 1 0 t kappa' jarray kappa' nkappa
                  go' (t+1)
          _ <- go' 2
          entry' <- readArray jarray (nkappa, n)
          let s' = s + z'' * entry'
          if j > kappai && i <= n 
            then do 
              s'' <- summation m a b x dico n alpha (i+1) z'' (j-kappai) 
                               kappa' jarray
              go (kappai + 1) z'' (s' + s'') 
            else 
              go (kappai + 1) z'' s'
  go 1 z 0

jack :: (Fractional a, MArray IOUArray a IO) => 
        a -> [a] -> Seq (Maybe Int) -> Int -> a -> Int -> Int
        -> [Int] -> IOUArray (Int,Int) a -> [Int] -> Int -> IO ()
jack alpha x dico k beta c t mu jarray kappa nkappa = do 
  let i0 = max k 1
      i1 = length (cleanPart mu)
      go :: Int -> IO ()
      go i 
        | i == i1+1 = return ()
        | otherwise = do 
--          when (length mu == i && mu!!(i-1) > 0 || mu!!(i-1) > mu!!i) $ do
          when (length mu == i || mu!!(i-1) > mu!!i) $ do
            let gamma = beta * _betaratio kappa mu i alpha
                mu' = cleanPart $ (element (i-1) .~ mu!!(i-1) - 1) mu
                nmu = _nkappa dico mu'
            if not (null mu') && length mu' >= i && mu'!!(i-1) > 0 
              then do
                jack alpha x dico i gamma (c+1) t mu' jarray kappa nkappa
              else do
                when (nkappa > 1) $ do
                  entry' <- readArray jarray (nkappa, t)
                  if any (>0) mu' 
                    then do
                      entry <- readArray jarray (nmu, t-1)
                      writeArray jarray (nkappa, t) 
                                 (entry' + gamma * entry * x!!(t-1)^(c+1))
                    else 
                      writeArray jarray (nkappa, t) 
                                 (entry' + gamma * x!!(t-1)^(c+1))
          go (i+1)
  _ <- go i0
  entry1 <- readArray jarray (nkappa, t)
  if k == 0 
    then do
      when (nkappa > 1) $ do
        entry2 <- readArray jarray (nkappa, t-1)
        writeArray jarray (nkappa, t) (entry1 + entry2)
    else do 
      entry2 <- readArray jarray (_nkappa dico mu, t - 1) 
      writeArray jarray (nkappa, t) (entry1 + beta * x!!(t-1)^c * entry2)


hypergeom :: forall a. (Fractional a, IArray UArray a, MArray IOUArray a IO) => 
             Int -> a -> [a] -> [a] -> [a] -> IO a
hypergeom m alpha a b x = do 
  let n = length x
      pmn = _P m n 
      dico = _dico pmn m
      xrange = [1 .. n]
      line1 = zipWith (\i u -> ((1, i), u)) xrange (scanl1 (+) x)
      otherlines = concatMap (\j -> [((j, i), 0) | i <- xrange]) [2 .. pmn]
      arr0 = array ((1, 1), (pmn, n)) (line1 ++ otherlines) :: UArray (Int,Int) a
  jarray <- thaw arr0
  s <- summation m a b x dico n alpha 0 1 m [] jarray
  return $ s + 1

