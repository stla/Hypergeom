{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Hypergeom11 where
import           Control.Monad                            (when)
import           Data.Array.Unboxed                       hiding (index)
import           Data.Array.IO                            hiding (index)
import           Data.Maybe
import           Data.Sequence                            (Seq, elemIndexL, (!?), index, update, (><), (|>), Seq (Empty), Seq ((:|>)), Seq ((:<|)))
import qualified Data.Sequence                            as S

_diffSequence :: Seq Int -> Seq Int
_diffSequence (x :<| ys@(y :<| _)) = (x - y) :<| _diffSequence ys
_diffSequence x = x

_dualPartition :: Seq Int -> Seq Int
_dualPartition Empty = S.empty
_dualPartition xs = go 0 (_diffSequence xs) S.empty
  where
    go !i (d :<| ds) acc = go (i + 1) ds (d :<| acc)
    go n Empty acc = finish n acc
    finish !j (k :<| ks) = S.replicate k j >< finish (j - 1) ks
    finish _ Empty = S.empty

_betaratio :: Fractional a => Seq Int -> Seq Int -> Int -> a -> a
_betaratio kappa mu k alpha = alpha * prod1 * prod2 * prod3
  where
    t = fromIntegral k - alpha * fromIntegral (mu `index` (k - 1))
    ss = S.fromList [1 .. k - 1]
    sss = ss |> k
    u =
      S.zipWith
        (\s kap -> t + 1 - fromIntegral s + alpha * fromIntegral kap)
        sss
        (S.take k kappa)
    v =
      S.zipWith
        (\s m -> t - fromIntegral s + alpha * fromIntegral m)
        ss
        (S.take (k - 1) mu)
    l = mu `index` (k - 1) - 1
    mu' = S.take l (_dualPartition mu)
    w =
      S.zipWith
        (\s m -> fromIntegral m - t - alpha * fromIntegral s)
        (S.fromList [1 .. l])
        mu'
    prod1 = product $ fmap (\x -> x / (x + alpha - 1)) u
    prod2 = product $ fmap (\x -> (x + alpha) / x) v
    prod3 = product $ fmap (\x -> (x + alpha) / x) w

_T :: Fractional a => a -> [a] -> [a] -> Seq Int -> a
_T alpha a b kappa =
  if S.null kappa || kappa !? 0 == Just 0
    then 1
    else prod1 * prod2 * prod3
  where
    lkappa = S.length kappa - 1
    kappai = kappa `index` lkappa 
    kappai' = fromIntegral kappai
    i = fromIntegral $ lkappa
    c = kappai' - 1 - i / alpha
    d = kappai' * alpha - i - 1
    s = fmap fromIntegral (S.fromList [1 .. kappai - 1])
    kappa' = fmap fromIntegral $ S.take kappai (_dualPartition kappa)
    e = S.zipWith (\x y -> d - x * alpha + y) s kappa'
    g = fmap (+ 1) e
    s' = fmap fromIntegral (S.fromList [1 .. lkappa])
    f = S.zipWith (\x y -> y * alpha - x - d) s' (fmap fromIntegral kappa)
    h = fmap (+ alpha) f
    l = S.zipWith (*) h f
    prod1 = product (fmap (+ c) a) / product (fmap (+ c) b)
    prod2 = product $ S.zipWith (\x y -> (y - alpha) * x / y / (x + alpha)) e g
    prod3 = product $ S.zipWith3 (\x y z -> (z - x) / (z + y)) f h l

a008284 :: [[Int]]
a008284 = [1] : f [[1]]
  where
    f xss = ys : f (ys : xss)
      where
        ys = map sum (zipWith take [1 ..] xss) ++ [1]

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
        inner ::
             Int
          -> [Int]
          -> [Int]
          -> [Int]
          -> Int
          -> Seq (Maybe Int)
          -> Maybe Int
          -> Seq (Maybe Int)
        inner i !a !b !c !end !d !dlast
          | dlast == Just pmn = go True d
          | otherwise =
            let bi = b !! i
            in if bi > 0
                 then let l = min bi (c !! i)
                      in let ddlast = Just $ end + 1
                         in let dd = d |> ddlast
                            in let range1l = [1 .. l]
                               in inner
                                    (i + 1)
                                    (a ++ [end + 1 .. end + l])
                                    (b ++ map (\x -> bi - x) range1l)
                                    (c ++ range1l)
                                    (end + l)
                                    dd
                                    ddlast
                 else inner (i + 1) a b c end (d |> Nothing) Nothing

_nkappa :: Seq (Maybe Int) -> Seq Int -> Int
_nkappa dico (kappa0 :|> kappan) =
  fromJust (dico `S.index` _nkappa dico kappa0) + kappan - 1
_nkappa _ Empty = 0

cleanPart :: Seq Int -> Seq Int
cleanPart kappa =
  let i = elemIndexL 0 kappa
  in if isJust i
       then S.take (fromJust i) kappa
       else kappa

summation ::
     forall a. (Fractional a, MArray IOUArray a IO)
  => [a]
  -> [a]
  -> [a]
  -> Seq (Maybe Int)
  -> Int
  -> a
  -> Int
  -> a
  -> Int
  -> Seq Int
  -> IOUArray (Int, Int) a
  -> IO a
summation a b x dico n alpha i z j kappa jarray 
 = do
  let lkappa = kappa `index` (S.length kappa - 1)
  let go :: Int -> a -> a -> IO a
      go kappai !z' !s
        | i == n || i == 0 && kappai > j || i > 0 && kappai > min lkappa j =
          return s
        | otherwise = do
          let kappa' = kappa |> kappai -- correct ? seems yes
              nkappa = _nkappa dico kappa'
              z'' = z' * _T alpha a b kappa'
          when (nkappa > 1 && (S.length kappa' == 1 || kappa' !? 1 == Just 0)) $ do
            entry <- readArray jarray (nkappa - 1, 1)
            let newval =
                  x !! 0 * (1 + alpha * fromIntegral (kappa' `index` 0 - 1)) * entry
            writeArray jarray (nkappa, 1) newval
          let go' :: Int -> IO ()
              go' t
                | t == n + 1 = return ()
                | otherwise = do
                  _ <- jack alpha x dico 0 1 0 t kappa' jarray kappa' nkappa
                  go' (t + 1)
          _ <- go' 2
          entry' <- readArray jarray (nkappa, n)
          let s' = s + z'' * entry'
          if j > kappai && i <= n
            then do
              s'' <-
                summation
                  a
                  b
                  x
                  dico
                  n
                  alpha
                  (i + 1)
                  z''
                  (j - kappai)
                  kappa'
                  jarray
              go (kappai + 1) z'' (s' + s'')
            else go (kappai + 1) z'' s'
  go 1 z 0

jack :: (Fractional a, MArray IOUArray a IO)
  => a
  -> [a]
  -> Seq (Maybe Int)
  -> Int
  -> a
  -> Int
  -> Int
  -> Seq Int
  -> IOUArray (Int, Int) a
  -> Seq Int
  -> Int
  -> IO ()
jack alpha x dico k beta c t mu jarray kappa nkappa = do
  let i0 = max k 1
      i1 = S.length (cleanPart mu) + 1
      go :: Int -> IO ()
      go i
        | i == i1 = return ()
        | otherwise
         = do
          let u = mu `index` (i - 1)
          when (S.length mu == i || u > mu `index` i) $ do
            let gamma = beta * _betaratio kappa mu i alpha
                mu' = cleanPart $ update (i-1) (u - 1) mu
                nmu = _nkappa dico mu'
            if not (S.null mu') && S.length mu' >= i && u > 1
              then do
                jack alpha x dico i gamma (c + 1) t mu' jarray kappa nkappa
              else do
                when (nkappa > 1) $ do
                  entry' <- readArray jarray (nkappa, t)
                  if any (> 0) mu'
                    then do
                      entry <- readArray jarray (nmu, t - 1)
                      writeArray
                        jarray
                        (nkappa, t)
                        (entry' + gamma * entry * x !! (t - 1) ^ (c + 1))
                    else writeArray
                           jarray
                           (nkappa, t)
                           (entry' + gamma * x !! (t - 1) ^ (c + 1))
          go (i + 1)
  _ <- go i0
  entry1 <- readArray jarray (nkappa, t)
  if k == 0
    then do
      when (nkappa > 1) $ do
        entry2 <- readArray jarray (nkappa, t - 1)
        writeArray jarray (nkappa, t) (entry1 + entry2)
    else do
      entry2 <- readArray jarray (_nkappa dico mu, t - 1)
      writeArray jarray (nkappa, t) (entry1 + beta * x !! (t - 1) ^ c * entry2)

hypergeom ::
     forall a. (Fractional a, IArray UArray a, MArray IOUArray a IO)
  => Int
  -> a
  -> [a]
  -> [a]
  -> [a]
  -> IO a
hypergeom m alpha a b x = do
  let n = length x
      pmn = _P m n
      dico = _dico pmn m
      xrange = [1 .. n]
      line1 = zipWith (\i u -> ((1, i), u)) xrange (scanl1 (+) x)
      otherlines = concatMap (\j -> [((j, i), 0) | i <- xrange]) [2 .. pmn]
      arr0 =
        array ((1, 1), (pmn, n)) (line1 ++ otherlines) :: UArray (Int, Int) a
  jarray <- thaw arr0
  s <- summation a b x dico n alpha 0 1 m S.empty jarray
  return $ s + 1




