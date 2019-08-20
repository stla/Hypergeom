{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
module Hypergeom7 where
import           Control.Lens                             hiding (iconcatMap, (|>))
import           Data.Array
import           Data.List                                (elemIndex, findIndex,
                                                           nub, sort, sortOn)
import           Data.Maybe
import           Data.Sequence                            (Seq, index, update,
                                                           (|>))
import qualified Data.Sequence                            as S
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

a008284 :: [[Int]]
a008284 = [1] : f [[1]]
  where
  f xss = ys : f (ys : xss)
    where
    ys = map sum (zipWith take [1..] xss) ++ [1]

_P :: Int -> Int -> Int
_P m n = sum (concatMap (take (min m n)) (take m a008284))

_dico :: Int -> Int -> Int -> Seq (Maybe Int)
_dico pmn m n = go False S.empty
  where
  go :: Bool -> Seq (Maybe Int) -> Seq (Maybe Int)
  go k d'
    | k = d' -- n > 1
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

hypergeom :: forall a. (Fractional a, Show a) => Int -> a -> [a] -> [a] -> [a] -> (a, String)
hypergeom m alpha a b x = (summation 0 1 m kappa0 arr0)
  where
  n = length x
  pmn = _P m n
  dico = _dico pmn m n
  kappa0 = []
  xrange = [1 .. n]
  line1 = zipWith (\i u -> ((1,i), u)) xrange (scanl1 (+) x)
  otherlines = concatMap (\j -> [((j,i),0) | i <- xrange]) [2 .. pmn]
  arr0 = array ((1,1), (pmn,n)) (line1 ++ otherlines)
  --
  summation :: Fractional a => Int -> a -> Int -> [Int] -> Array (Int,Int) a -> (a, String)
  summation i z jj kappa jarray = go 1 z 0
    where
    go :: Int -> a -> a -> (a, String)
    go kappai !zz !s
      | i == 0 && kappai > jj || i>0 && kappai > min (last kappa) jj = (s, show jarray'')
      | otherwise = go (kappai + 1) z' s''
      where
      kappa' = cleanPart $ (element i .~ kappai) (kappa ++ repeat 0)
      nkappa = _nkappa dico kappa'
      z' = zz * _T alpha a b (filter (> 0) kappa')
      jarray' = if nkappa > 1 && (length kappa' == 1 || kappa'!!1 == 0)
        then
          let newval = x!!0 * (1 + alpha * fromIntegral (kappa'!!0 - 1)) * jarray ! (nkappa-1,1) in
          jarray // [((nkappa,1), newval)]
        else jarray
      go'' :: Int -> Array (Int,Int) a -> Array (Int,Int) a
      go'' tt !aa
        | tt == n+1 = aa
        | otherwise = go'' (tt+1) (jack 0 1 0 tt kappa' aa nkappa kappa')
      -- j1 = jack 0 1 0 2 kappa' jarray'
      -- jarray'' = jack 0 1 0 3 kappa' j1
      jarray'' = go'' 2 jarray'
      s' = s + z' * jarray'' ! (nkappa, n)
      s'' = if jj > kappai && i <= n
        then
          s' + (fst $ summation (i+1) z' (jj-kappai) kappa' jarray'') 
        else
          s'
    --
    --
    jack ::
        Int -> a -> Int -> Int -> [Int] -> Array (Int, Int) a -> Int -> [Int] -> Array (Int, Int) a
    jack k beta c t mu aa nkappa kappa' =
      let add = if k == 0 then (if nkappa > 1 then arr ! (nkappa, t - 1) else 0) else beta * x !! (t - 1) ^ c * arr ! (nmu, t - 1) in 
      arr // [((nkappa, t), arr ! (nkappa, t) + add)]
      where
        arr = go' (max k 1) aa
        nmu = _nkappa dico (cleanPart mu)
        go' :: Int -> Array (Int, Int) a -> Array (Int, Int) a
        go' j !jarr
          | j > length (cleanPart mu) = jarr
          | otherwise =
            go'
            (j + 1)
            (if (length mu == j && mu !! (j - 1) > 0) || mu !! (j - 1) > mu !! j
                then let gamma = beta * _betaratio kappa' mu j alpha
                    in let mu' = (element (j - 1) .~ mu !! (j - 1) - 1) mu
                        in if mu' !! (j - 1) > 0
                            then jack j gamma (c + 1) t mu' jarr nmu kappa'
                            else if nkappa == 1
                                    then jarr
                                    else let jjj =
                                                if any (> 0) mu'
                                                then jarr !
                                                        ( _nkappa
                                                            dico
                                                            (cleanPart mu')
                                                        , t - 1)
                                                else 1
                                        in jarr //
                                            [ ( (nkappa, t)
                                                , jarr ! (nkappa, t) +
                                                gamma * jjj *
                                                x !! (t - 1) ^ (c + 1))
                                            ]
                else jarr)
      --

