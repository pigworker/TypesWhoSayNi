------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Composition                                             -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Composition where

open import Lib.One
open import Lib.Equality
open import Lib.Pi
open import Lib.Sigma
open import Lib.Sum
open import Lib.Index
open import Lib.Bwd
open import Thin.Data
open import Thin.Select
open import Thin.Triangle
open import Thin.Cover
open import Thin.Thinned
open import Relevant.Pair
open import Relevant.Abstraction
open import Syntax.Desc
open import Syntax.Tm
open import Syntax.Action
open import Syntax.Substitution
open import Syntax.Thinning

module _
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}
 open DESC B S b2s
 module _
  (Cn : S -> Set) -- what constructors exist for each sort
  (Ds : {s : S} -> Cn s -> Desc)
  (M : S * Scope -> Set)
  where
  open TM B S b2s Cn Ds M
  open ACTION B S b2s Cn Ds M
  open SUBSTITUTION B S b2s Cn Ds M
  open THINNING B S b2s Cn Ds M


------------------------------------------------------------------------------
-- the inevitable lemma about weakening
------------------------------------------------------------------------------

{-
There's a naturality property which is always crucial. Substitution then
weakening is the same thing as weakening then deploying the weakened
substitution.

The proof makes crucial use of the fact that although an action and its
weakening have different source scopes, the support of the term we care
about embeds in both.
-}

  module WKSBG {_=>_}(X : Action _=>_) where
   open Action X ; open SBG ; open THINACTION X ; open THSBG X
   open SBGFUN Thinned X

   wknLemma : forall {D ga de}
     {t : Tm D :< ga}(sg : ga => de){t' : Tm D :< de} -> SbG X D t sg t' ->
     forall b -> SbG X D (t :^ b) (wkn sg b) (t' :^ b)
   wknLemma {t = t0 ^ th} sg {t' = t1 ^ ph} s b
     with mkSbG X _ (t0 ^ th -^ b) (wkn sg b)
   ... | t2 , s'
     with sbGQ (\ i -> 
         (hit (i -<- th) sg :- idth -^ b)
           ~[ (thing (hit (i -<- th) sg) ^_) $~ ((_-^ b) $~ (_ <id)) >
         (hit (i -<- th) sg :^ b)
           < hitWkn+ (i -<- th) sg b ]~
         hit (i -<- th -^ b) (wkn sg b)
           [QED])
       (thSbG s (idth -^ b)) s'
   ... | q = s' :[ SbG X _ _ _ $~ 
     t2                          < q ]~
     (t1 ^ ph -<- idth -^ b)    ~[ (t1 ^_) $~ ((_-^ b) $~ (ph <id)) >
     (t1 ^ ph -^ b) [QED] >


------------------------------------------------------------------------------
-- constructing the composition of actions as an action
------------------------------------------------------------------------------

  module SBGCO {_=X>_}{_=Y>_}(X : Action _=X>_)(Y : Action _=Y>_) where
   private module X = SBG X ; module Y = SBG Y
   open Action ; open SBG ; open SBGFUN Y Y ; open WKSBG Y

   _=XY>_ : Scope -> Scope -> Set
   ga =XY> de = <(ga =X>_) :* (_=Y> de)>

   actionCo : Action _=XY>_
   hit actionCo i (rh ^ sg) = mkSbG Y (` _) (hit X i rh) sg .fst
   wkn actionCo (rh ^ sg) b = wkn X rh b ^ wkn Y sg b
   hitWkn0 actionCo (rh ^ sg) b
     with hit X (noth -, b) (wkn X rh b) | hitWkn0 X rh b
        | mkSbG Y (` b2s b) (hit X (noth -, b) (wkn X rh b)) (wkn Y sg b)
   ... | _ | r~ | ! vaSb _ r~ = hitWkn0 Y sg b
   hitWkn+ actionCo i (rh ^ sg) b 
     with hit X i rh | hit X (i -^ b) (wkn X rh b) | hitWkn+ X i rh b
        | mkSbG Y (` _) (hit X i rh) sg
        | mkSbG Y (` _) (hit X (i -^ b) (wkn X rh b)) (wkn Y sg b)
   ... | _ | _ | r~ | ! r | ! r'
     = sbGQ (\ _ -> r~) r' (wknLemma sg r b)

{-
Now prove that the composition of the actions is the action of the
composition.
-}

   compLemma : forall {D ga0 ga1 ga2}{rh : ga0 =X> ga1}{sg : ga1 =Y> ga2}
     {t0 : Tm D :< ga0}{t1 : Tm D :< ga1}{t2 : Tm D :< ga2} ->
     SbG X D t0 rh t1 -> SbG Y D t1 sg t2 -> SbG actionCo D t0 (rh ^ sg) t2
   compLemma {rh = rh}{sg} (vaSb i r~) y =
     vaSb i (sbGQ (\ _ -> r~) (mkSbG Y _ (hit X i rh) sg .snd) y)
   compLemma (cnSb c x) (cnSb .c y) = cnSb c (compLemma x y)
   compLemma (meSb m x) (meSb .m y) = meSb m (compLemma x y)
   compLemma unSb unSb = unSb
   compLemma (prSb p0 dx ex p1) (prSb p2 dy ey p3) with prInj p1 p2
   ... | (r~ , r~) , r~ = prSb p0 (compLemma dx dy) (compLemma ex ey) p3
   compLemma (kkSb x) (kkSb y) = kkSb (compLemma x y)
   compLemma (llSb x) (llSb y) = llSb (compLemma x y)
