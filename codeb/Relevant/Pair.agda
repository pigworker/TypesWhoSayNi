------------------------------------------------------------------------------
-----                                                                    -----
-----     Relevant.Pair                                                  -----
-----                                                                    -----
------------------------------------------------------------------------------

module Relevant.Pair where

open import Lib.Equality
open import Lib.Pi
open import Lib.Sigma
open import Lib.Index
open import Lib.Bwd
open import Thin.Data
open import Thin.Triangle
open import Thin.Cover
open import Thin.Thinned

module _ {B : Set} where

 open THIN {B}


------------------------------------------------------------------------------
-- Everybody's Got To Be Somewhere
------------------------------------------------------------------------------

{-
Suppose S and T are scoped datatypes enforcing relevance in free variables.
What does it mean to pair an S and a T, also enforcing relevance?

We must hand each of the S and the T exactly the support they need, but we
must make sure that no free variables get forgotten about in the process.
That is, we must ensure that the thinnings which embed the left and right
supports into the overall support form a *cover*.
-}

 infixl 9 _/*\_
 infix 6 _</_\>_
 record _/*\_ (S T : Scope -> Set)(ga : Scope) : Set where
   constructor _</_\>_
   field
     {lsupp rsupp} : Scope
     {lthin} : lsupp <= ga
     {rthin} : rsupp <= ga
     outl  : S lsupp
     cover : lthin /u\ rthin
     outr  : T rsupp
 open _/*\_

{-
Let us build some associated kit.
-}


 module _ {S T : Scope -> Set} where


------------------------------------------------------------------------------
-- smart constructor
------------------------------------------------------------------------------

  infixl 2 _/,\_
  _/,\_ : [(S :<_) -:> (T :<_) -:> (S /*\ T :<_)]
  s ^ th /,\ t ^ ph = let (! ps) , ! ! ! u = th /+\ ph in  s </ u \> t ^ ps

{-
Given the left and right thinnings, compute their coproduct diagram.
-}


------------------------------------------------------------------------------
-- smart projections
------------------------------------------------------------------------------

  infixl 5 _-/ _-\

  _-/ : [(S /*\ T :<_) -:> (S :<_)]
  _-\ : [(S /*\ T :<_) -:> (T :<_)]
  (s </ u \> _ ^ th) -/ = s ^ u/ u -<- th
  (_ </ u \> t ^ th) -\ = t ^ u\ u -<- th

  fstQ : forall {ga}(s : S :< ga)(t : T :< ga) -> (s /,\ t) -/ ~ s
  fstQ (s ^ th) (t ^ ph) with th /+\ ph
  ... | (! ps) , ! v , w , u rewrite eq& v = r~

  sndQ : forall {ga}(s : S :< ga)(t : T :< ga) -> (s /,\ t) -\ ~ t
  sndQ (s ^ th) (t ^ ph) with th /+\ ph
  ... | (! ps) , ! v , w , u rewrite eq& w = r~


------------------------------------------------------------------------------
-- the smart constructor, relationally
------------------------------------------------------------------------------

  data Pr {ga}(s : S :< ga)(t : T :< ga) : S /*\ T :< ga -> Set
    where
    mkPr : {x : <(_ <=_) :* (_<= ga) :* (_ <=_)>} -> let ! th , ps , ph = x in
      th & ps =< thin s -> (u : th /u\ ph) -> ph & ps =< thin t ->
      Pr s t (thing s </ u \> thing t ^ ps)

{-
That is, we'll accept pairing via *any* coproduct diagram...
-}


------------------------------------------------------------------------------
-- the inputs determine the output and the pair
------------------------------------------------------------------------------

  _~Pr~_ : forall {ga}{s : S :< ga}{t : T :< ga}{st st' : S /*\ T :< ga} ->
     (p0 : Pr s t st)(p1 : Pr s t st') -> st ~ st' >< \ {r~ -> p0 ~ p1 }
  mkPr v0 u v1 ~Pr~ mkPr w0 u' w1
    with copQ (! ! v0 , v1 , u) (! ! w0 , w1 , u') ; ... | r~ = r~ , r~

{-
...because they're unique, anyway.
-}


------------------------------------------------------------------------------
-- the output determines the inputs and the pair
------------------------------------------------------------------------------

  prInj : forall {ga}{s s' : S :< ga}{t t' : T :< ga}{st : S /*\ T :< ga} ->
    (p0 : Pr s t st)(p1 : Pr s' t' st) ->
    (s ~ s' * t ~ t') >< \ { (r~ , r~) -> p0 ~ p1 }
  prInj (mkPr v0 u v1) (mkPr w0 .u w1) with v0 ~&~ w0 | v1 ~&~ w1
  ... | r~ , r~ | r~ , r~ = (r~ , r~) , r~


------------------------------------------------------------------------------
-- the smart constructor pairs
------------------------------------------------------------------------------

  prPr : forall {ga}{s : S :< ga}{t : T :< ga} -> Pr s t (s /,\ t)
  prPr {_}{s ^ th}{t ^ ph} with th /+\ ph
  prPr {_}{s ^ th}{t ^ ph} | ! ! v , w , u = mkPr v u w


------------------------------------------------------------------------------
-- just the cover is enough
------------------------------------------------------------------------------

  covPr : forall {ga0 ga ga1 de}
    {th : ga0 <= de}{ph : ga1 <= de}{ps : de <= ga}{s t u} ->
    Pr (s ^ th -<- ps) (t ^ ph -<- ps) (s </ u \> t ^ ps)
  covPr = mkPr ((_ -&- _).snd) _ ((_ -&- _).snd)


------------------------------------------------------------------------------
-- how to thin a pairing
------------------------------------------------------------------------------

  pr< : forall {ga de}{s t st} -> Pr s t st -> (th : ga <= de) ->
    Pr (s :- th) (t :- th) (st :- th)
  pr< (mkPr v u w) th = mkPr (v &< th) u (w &< th)
