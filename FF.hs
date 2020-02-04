{-#  LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

module FF where

import FTtop
import EtRt
import qualified Data.Set as S
import Data.Maybe (fromJust)
import GHC.Exts (IsList(..))
import Data.Monoid ((<>))
import System.Environment
import Control.DeepSeq

-- ************************************************************
type Pair      a = (a,a)
type SetPair   a = S.Set (Pair a)
type FT        a = FingerTree (SetPair a) (Pair a)
data Top       a = Top { getSetTop::SetPair a
                       , getFT::FT a} deriving Show
type Forest    a = FingerTree (SetPair a) (Top a)
data TopForest a = TopForest { getNverticesForest::Int
                             , getSetForest::SetPair a
                             , getForest::Forest a} deriving Show

emptyFT :: Ord a => FT a
emptyFT  = empty

emptyTop :: Ord a => Top a
emptyTop = Top set ft
 where
   set = S.empty
   ft  = emptyFT

emptyForest :: Ord a => Forest a
emptyForest  = empty

emptyTopForest :: Ord a => TopForest a
emptyTopForest  = TopForest 0 set forest
 where
   set    = S.empty
   forest = emptyForest

instance (Ord a) => Edges (S.Set (a,a)) (a,a) where
   edges (x,y) = S.insert (x, y) S.empty

-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
--           ROOT of tree
-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
root :: Ord a => FT a -> Maybe a
root tree = case viewl tree of
  EmptyL   -> Nothing
  x :< _   -> Just $ fst x

-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
--           REroot of tree
-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
reroot :: Ord a => FT a -> a -> FT a
reroot tree vertex = case (searchTree pred tree) of
   BuiltTree left _ right -> root <| (right >< left)
   NoBuiltTree      -> tree
 where root          = (vertex,vertex)
       pred before   = (S.member root) before

-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
--            CONNECTED ( u, v ) in same tree ? IN WHICH tour ?
-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
instance Ord a => Edges  (S.Set (a,a)) (Top a) where
  edges (Top s _) = s

searchFor :: Ord a => a -> TopForest a -> Maybe (Top a, a)
searchFor x (TopForest _ set forest)
    = if p set then
         case (searchTree p forest) of
         BuiltTree _ top _ -> Just (top, fromJust $ root (getFT top))
         NoBuiltTree       -> Nothing
      else Nothing
  where
     p b  = (S.member pair) b
     pair = (x,x)

type PairTopVertex a = (Top a, a, Top a, a)

connected :: Ord a => a -> a -> TopForest a -> (Bool, Maybe (PairTopVertex a))
connected x y f =
 case (searchFor x f, searchFor y f) of
  (Nothing          , _           ) -> (False, Nothing)
  (_                , Nothing     ) -> (False, Nothing)
  (Just (tx,rx)     , Just (ty,ry)) -> if rx == ry
                                   then (True,  Just(tx,rx,tx,rx))
                                   else (False, Just(tx,rx,ty,ry))

-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
--     MERGING (APPENDING) TOPs
--     SEARCHING within TOPs
-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
data ResultSearch a
  = NoResult
  | ResultSearch (Top a) (Pair a) (Top a)
  deriving (Show)

instance NFData a => NFData (ResultSearch a) where
  rnf NoResult               = ()
  rnf (ResultSearch tl p tr) = rnf tl `seq` rnf p `seq` rnf tr

instance NFData a => NFData (Top a) where
  rnf (Top set ft) = rnf set `seq` rnf ft

instance (NFData a) => NFData (TopForest a) where
   rnf (TopForest v s f) = rnf v `seq` rnf s `seq` rnf f


mer :: (Ord a) => Top a -> Top a -> Top a
mer (Top sleft tleft) (Top sright tright) =
 let set   = sleft `S.union` sright
     ft    = tleft   ><      tright
 in  set `seq` ft `seq` Top set ft

sea :: (NFData a, Ord a) => Pair a -> Top a -> ResultSearch a
sea (u,v) top@(Top set _) = if p set then sea' p top else NoResult
 where
   p before = (S.member (u',v')) before || (S.member (v',u')) before
   u' = min u v
   v' = max u v

sea' :: (NFData a, Ord a)
     => (SetPair a -> Bool) -> Top a -> ResultSearch a
sea' p top@(Top set ft) = case (search p ft ) of
   NoBuilt                            -> NoResult
   Built spot ltree lset x rtree rset ->
       case spot of
           LeftEnd   -> ResultSearch llset x lrset
           RightEnd  -> ResultSearch rlset x rrset
           CentreEnd -> ResultSearch lsetx x rsetx
       where
           lsetx = {-# SCC lsetx #-} Top lset ltree
           rsetx = {-# SCC rsetx #-} Top rset rtree
           llset = {-# SCC llset #-} Top lset ltree
           lrset = {-# SCC lrset #-} Top (set S.\\ lset) rtree
           rlset = {-# SCC rlset #-} Top (set S.\\ rset) ltree
           rrset = {-# SCC rrset #-} Top rset rtree

-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
--                           L I N K  (for trees and forest)
-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]

linkTreeSafe :: (NFData a,Ord a) => a -> Top a -> a -> Top a -> Maybe (Top a)
linkTreeSafe u tu'@(Top su ftu)
             v tv'@(Top sv ftv)
             = case (S.member (u,u) su, S.member (v,v) sv) of
  (False, _    ) -> Nothing
  (_    , False) -> Nothing
  (True , True ) -> case (root ftu,root ftv) of
    (Nothing, _      ) -> Nothing
    (_      , Nothing) -> Nothing
    (Just r1, Just r2) ->
     if r1 == r2 then Nothing
     else Just $
      let from  = reroot ftu u
          tu    = Top su from
          ResultSearch left'@(Top lset ltree) _
                       right'@(Top rset rtree)  =  sea (v,v) tv'
          left  = Top ((u',v') `S.insert` ((v,v) `S.insert` lset))
                      (ltree |> (v,v) |> (u',v'))
          right = Top ((u',v') `S.insert` rset)
                      ((u',v') <| rtree)
      in  left `mer` tu `mer` right
 where
   pred before  = (S.member (v,v)) before
   u'  =  min u v
   v'  =  max u v

linkTree :: (NFData a,Ord a) => a -> Top a -> a -> Top a -> Top a
linkTree u tu'@(Top su ftu) v tv'@(Top sv ftv) =
     let from  = reroot ftu u
         tu    = Top su from
         ResultSearch left'@(Top lset ltree) _
                      right'@(Top rset rtree)  = {-# SCC link_sea #-} sea (v,v) tv'
         left  = Top ((u',v') `S.insert` ((v,v) `S.insert` lset))
                     (ltree |> (v,v) |> (u',v'))
         right = Top ((u',v') `S.insert` rset)
                     ((u',v') <| rtree)
     in {-# SCC mer_link #-} left `mer` tu `mer` right
 where
  pred before  = (S.member (v,v)) before
  u'  =  min u v
  v'  =  max u v

link :: (NFData a,Ord a) => a -> a -> TopForest a -> TopForest a
link u v f@(TopForest size set forest)
  | u == v    = f  -- FURTHER MSG management
  | otherwise =
     case connected u v f of
      (False, Just (tu,ru,tv,rv)) -> linkAll (linkTree u tu v tv)
      _                           -> f
 where
    BuiltTree lf' _ rf' = searchTree predU forest
    BuiltTree lf  _ rf  = searchTree predV (lf' >< rf')
    linkAll top   = TopForest size (S.insert (u',v') set) (top <| (lf >< rf))
    predU before  = (S.member (u,u)) before
    predV before  = (S.member (v,v)) before
    u' = min u v
    v' = max u v

-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
--                     C U T   (for trees and forest)
-- two edges will be deleted: 1 (u,v), 2 (v,u) from tree
-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]

cutTreeSafe :: (NFData a,Ord a) => a -> a -> Top a -> Maybe (Top a, Top a)
cutTreeSafe u v top@(Top set ft) =
  if (S.member (u,u) set && S.member (v,v) set) then
   case (sea (u',v') top) of
     ResultSearch left _ right ->  -- (u,v) is discarded, first edge deletion
        case (sea (u',v') left)  of
          -- (v,u) is on the left and discarded, second edge deletion
          ResultSearch leftL _ rightL -> Just (rightL, mer leftL right)
          _              ->           -- (v,u) is on the right
             case (sea (u',v') right) of
               -- (v,u) is on the right and discarded, second edge deletion
               ResultSearch leftR _ rightR -> Just (leftR, mer left rightR)
               _ -> Nothing     -- BAD Formed tree since (v,u) is missing
     _  -> Nothing                -- BAD Formed tree since (u,v) is missing
  else
    Nothing
 where
   u' = min u v
   v' = max u v

cutTree :: (NFData a,Ord a) => a -> a -> Top a -> (Top a, Top a)
cutTree u v top@(Top set ft)
   = let ResultSearch l1 _ r1 = {-# SCC first_sea #-} sea (u',v') top
         (left,left2,right2)  = {-# SCC second_sea #-}
           case sea (u',v') l1 of
              ResultSearch l2 _ r2 -> (r2,l2,r1)
              NoResult             ->
                 let ResultSearch l3 _ r3 = {-# SCC third_sea #-} sea (u',v') r1
                 in  (l3,l1,r3)
     in  (left,{-# SCC mer_cut #-} left2 `mer` right2)
 where
   u' = min u v
   v' = max u v

cut :: (NFData a,Ord a) => a -> a -> TopForest a -> TopForest a
cut u v f@(TopForest size set forest)
 | u == v    = f  -- further notice about NOT cut computed
 | otherwise =
    case connected u' v' f of
      (True, Just (tx,_,_,_)) -> buildForest (cutTree u' v' tx)
      _                       -> f -- further notice NOT cut ...
 where
    buildForest (t2,t3) = TopForest size
                                    (S.delete (u',v') set)
                                    (t3 <| (t2 <| (rf >< lf)))
    BuiltTree lf _ rf = searchTree pred forest
    pred before       = (S.member (u',u')) before
    u' = min u v
    v' = max u v

-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
--            HELPER functions  (for trees and forest)
-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
toListFT :: (Ord a, Edges v a) => FingerTree v a -> [a]
toListFT ft = case (viewl ft) of
  EmptyL    -> []
  x :< rest -> x : toListFT rest


prtT :: (Eq a, Ord a, Show a) => Top a -> IO ()
prtT (Top _ ft) = prtFT ft

prtFT :: (Eq a, Ord a, Show a) => FT a -> IO ()
prtFT  = prtTree . et2rt . toListFT

prtF :: (Ord a, Show a) => TopForest a -> IO()
prtF (TopForest _ _ forest) = prtFF forest

prtFF :: (Eq a, Ord a, Show a) => Forest a -> IO ()
prtFF f = ( prtForest . ets2rf ) ( forest f )
 where
   forest f = case viewl f of
     EmptyL   -> []
     x :<  xs -> toListFT (getFT x) : forest xs

-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
--    SOME TREE AND FOREST EXAMPLES
-- [][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][][]
ft0,ft1,ft1',ft2,ft2',s8,s8',s9,s9' :: FT Int
ft0  = emptyFT
ft1  = foldr (<|) emptyFT [(1,1),(1,2),(2,2),(2,1),(1,3),(3,3),(3,1),(1,4),(4,4),(4,1)]
ft1' = foldr (<|) emptyFT [(1,1),(1,2),(2,2),(1,2),(1,3),(3,3),(1,3),(1,4),(4,4),(1,4)]

ft2  = foldr (<|) emptyFT [(5,5),(5,6),(6,6),(6,7),(7,7),(7,6),(6,5)]
ft2' = foldr (<|) emptyFT [(5,5),(5,6),(6,6),(6,7),(7,7),(6,7),(5,6)]

s8   = (8,8) <| emptyFT ; s9  = (99,99) <| emptyFT
s8'  = s8               ; s9' = s9

forest0,forest1,forest2 :: TopForest Int
forest0  = emptyTopForest

forest1  = TopForest 7
                     (S.union (getSetTop top1)(getSetTop top2))
                     ((top1 <| emptyForest) |> top2)
forest2  = TopForest 9
                     (S.insert (99,99) (S.insert (8,8) (S.union (getSetTop top1)(getSetTop top2))))
                     (foldr (<|) emptyForest [top9,top1,top2,top8])

top0,top1,top2,top8,top9 :: Top Int
top0 = emptyTop
top1 = Top (S.fromList [(1,1),(1,2),(1,3),(1,4),(2,2),(3,3),(4,4)]) ft1'
top2 = Top (S.fromList [(5,5),(5,6),(6,6),(6,7),(7,7)])             ft2'
top8 = Top (S.insert (8,8) S.empty)   s8'
top9 = Top (S.insert (99,99) S.empty) s9'
