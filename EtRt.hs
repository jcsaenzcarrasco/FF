
module EtRt where

import qualified Data.Tree as T
import Data.Tree.Pretty
import Data.List.Split
--import Data.List (nub)
--import System.Random

-- | Print a RoseForest (multiway)
prtForest f = putStrLn (drawVerticalForest (map (fmap show) f))
prtTree   t = putStrLn (drawVerticalTree   (fmap show t))

-- | Transformation from ET into RoseForest (multiway)
-- | the input may or may not include loops, the result is the same
et2rf :: (Eq a) => [(a,a)] -> T.Forest a
et2rf xs = et2rf' (arrange xs)

arrange :: (Eq a) => [(a,a)] -> [(a,a)]
arrange []     = []
arrange [x]    = [x]
arrange xs@[(x1,y1),(x2,y2)]
   | y1 == x2  = xs
   | otherwise = [(x1,y1),(y2,x2)]
arrange ((x1,y1):(x2,y2):xs)
   | y1 == x2  = (x1,y1):arrange ((x2,y2):xs)
   | otherwise = (x1,y1):arrange ((y2,x2):xs)


et2rf' :: (Eq a) => [(a,a)] -> T.Forest a
et2rf' []         = []
et2rf' [(x,y)]    = [T.Node x []]
et2rf' ((x,y):xs) = [T.Node x $ concat (map et2rf splitlist)]
 where
   splitlist = splitWhen (\(x',_)->x'==x) xs

-- | Transformation from ETs (multiple ET) into RoseForest (multiway)
-- | the input may or may not include loops, the result is the same
-- | USEFUL when dealing with Dyn Trees
ets2rf :: (Eq a) => [[(a,a)]] -> T.Forest a
ets2rf []  = []
ets2rf (x:xs) = et2rf x ++ ets2rf xs

-- | Transformation from ET into RoseTree (multiway)
-- | the input may or may not include loops, the result is the same
et2rt :: (Eq a) => [(a,a)] -> T.Tree a
et2rt []           = error ""   -- Maybe type / different data type for Data.Tree ???
et2rt [(x,y)]      = T.Node x []
et2rt t@((x,y):xs) = T.Node x forest
  where
    (T.Node x forest) = head (et2rf t)


-- | Transformation from RoseForest (multiway) into an ET
-- | result is non-all loop vertices; loops are created once
rf2et :: (Eq a) => T.Forest a -> [[(a,a)]]
rf2et []            = []
rf2et [T.Node x []] = [[(x,x)]]
rf2et (t:ts)        = (rt2et t) : rf2et ts

-- | Transformation from RoseTree (multiway) into an ET
-- | result is non-all loop vertices; loops are created once
rt2et :: (Eq a) => T.Tree a -> [(a,a)]
rt2et (T.Node x ts) = case ts of
  []  -> [(x,x)]
  _   -> root ++ concat ( map (\t->pref t++rt2et t++suff t) ts )
    where
     pref v = [(x,T.rootLabel v)]
     suff v = [(T.rootLabel v,x)]
     root = [(x,x)]

rt2etUniK :: (Eq a,Ord a) => T.Tree a -> [(a,a)]
rt2etUniK (T.Node x ts) = case ts of
  []  -> [(x,x)]
  _   -> root ++ concat ( map (\t->pref t++rt2etUniK t++suff t) ts )
    where
     pref v = [(min x (T.rootLabel v), max x (T.rootLabel v))]
     suff v = [(min (T.rootLabel v) x, max (T.rootLabel v) x)]
     root = [(x,x)]


-- | Size of a RoseTree
sizeRT :: T.Tree a -> Int
sizeRT (T.Node _ []) = 1
sizeRT (T.Node _ xs) = 1 + sizeRF xs

-- | Size of a RoseForest
sizeRF :: T.Forest a -> Int
sizeRF [] = 0
sizeRF (x:xs) = sizeRT x + sizeRF xs

rndF []     = []
rndF (x:xs) = T.Node x [] : rndF xs

et48 ::[(Int,Int)]
et48 = [(4,4),(4,5),(5,5),(5,6),(6,6),(6,5),(5,4),(4,7),(7,7),(7,4),(4,8)
      ,(8,8),(8,3),(3,3),(3,1),(1,1),(1,3),(3,2),(2,2),(2,3),(3,8),(8,4),(4,4)]

et7 ::[(Int,Int)]
et7 = [(4,4),(4,5),(5,5),(5,6),(6,6),(6,5),(5,4),(4,7),(7,7),(7,4),(4,8)
      ,(8,8),(8,1),(1,1),(1,8),(8,2),(2,2),(2,8),(8,4),(4,4)]
