------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Thinning                                                -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Thinning where

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

module _
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}
 open DESC B S b2s
 module THINNING
  (Cn : S -> Set)
  (Ds : {s : S} -> Cn s -> Desc)
  (M : S * Scope -> Set)
  where
  open TM B S b2s Cn Ds M
  open ACTION B S b2s Cn Ds M
  open SUBSTITUTION B S b2s Cn Ds M


------------------------------------------------------------------------------
-- making an environment from a thinning (e.g., the identity substitution)
------------------------------------------------------------------------------

  module _ where
   open Action actionSb

   thsb : forall {ga de}(th : ga <= de) -> Sb ga de
   thsb []        = []
   thsb (th -, b) = wkn (thsb th) b
   thsb (th -^ b) with wkn (thsb th) b
   ... | sg -, _ = sg


------------------------------------------------------------------------------
-- a lemma about selection and composition
------------------------------------------------------------------------------

  thsb& : PreTri \ th ph ps -> th & ph =< ps -> th <? thsb ph ~ thsb ps
  thsb& [] = r~
  thsb& (_-,_ {th = th} {ph} v b)
    rewrite nat<? (_:^ b) th (thsb ph) | thsb& v = r~
  thsb& (_-^,_ {th = th} {ph} v b)
    rewrite nat<? (_:^ b) th (thsb ph) | thsb& v = r~
  thsb& {th = th} (_-^_ {ph = ph} v b)
    rewrite nat<? (_:^ b) th (thsb ph) | thsb& v = r~


------------------------------------------------------------------------------
-- acting by a thinning is a complete waste of time
------------------------------------------------------------------------------

{-
Thinnings have an action (generated from the identity by postcomposition).
Substituting by such an action achieves no more than directly thinning the
input at its root.
-}

  module THSBG {_=>_}(X : Action _=>_) where
   open Action X ; open SBG ; open THINACTION X

   thSbG : forall {D ga de}
     {t : Tm D :< ga}{sg : ga => de}{t' : Tm D :< de} -> SbG X D t sg t' ->
     forall {ze}(ph : de <= ze) -> SbG Thinned D t (sg ^ ph) (t' :- ph)
   thSbG (vaSb i r~) ph = vaSb i r~
   thSbG (cnSb c s) ph = cnSb c (thSbG s ph)
   thSbG (meSb m s) ph = meSb m (thSbG s ph)
   thSbG unSb ph rewrite noth! (noth -<- ph) noth = unSb
   thSbG (prSb p ds es p') ph =
     prSb p (thSbG ds ph) (thSbG es ph) (pr< p' ph)
   thSbG (kkSb s) ph = kkSb (thSbG s ph)
   thSbG (llSb s) ph = llSb (thSbG s (ph -, _))


  module _ where
   open THINACTION action~ ; open THSBG action~ ; open SBG Thinned
   open SBGFUN Thinned Thinned

   thLemma : forall {D ga de}{t : Tm D :< ga}(th : ga <= de){t' : Tm D :< de}
          -> SbG D t (r~ ^ th) t' -> t' ~ t :- th
   thLemma {D} {t = t} th s = sbGQ (\ _ -> r~) s (thSbG {D} (idSbG t) th)


------------------------------------------------------------------------------
-- environments made from thinnings just do thinning
------------------------------------------------------------------------------

{-
Here we exploit our freedom to consider different kinds of action that
hit variables in the same way.

The substitution action of an environment made from a thinning hits variables
in just the same way as the thinning action.
-}

  module _ where
   open THINACTION action~
   open Action; open SBG; open SBGFUN actionSb Thinned

   thsb1 : forall {de b}(i : b <- de) -> thsb i ~ ([] -, (var ^ i))
   thsb1 (i -, b) rewrite noth! i noth = (_-, _) $~ env0
   thsb1 (i -^ b) rewrite thsb1 i = r~

   thsbHit : forall {ga0 ga de}
     (ph : ga0 <= ga)(th : ga <= de) -> Hit ph (thsb th) ph (r~ ^ th)
   thsbHit ph th i with i -&- ph
   ... | j , v with j -&- th
   ... | k , w rewrite thsb& w | thsb1 k = r~

   thsbLemma : forall {D ga de}{t : Tm D :< ga}(th : ga <= de){t'} ->
     SbG actionSb D t (thsb th) t' -> t' ~ t :- th
   thsbLemma {D} {t = t@(_ ^ ph)} th s with mkSbG Thinned D t (r~ ^ th)
   ... | t' , s' with thLemma th s'
   ... | r~ = sbGQ (thsbHit ph th) s s' 
