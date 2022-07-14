------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin                                                           -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin where

open import Basics         public
open import Lib.Bwd        public
open import Thin.Data      public
open import Thin.Triangle  public
open import Thin.Select    public
open import Thin.Cover     public
open import Thin.Square    public
open import Thin.Pullback  public
open import Thin.IYJRN     public

module _ {X : Set} where

 open THIN {X}             public

{-

 data _!-_ (x : X)(T : Bwd X -> Set)(xz : Bwd X) : Set where
   ll : T (xz -, x) -> (x !- T) xz
   kk : T xz        -> (x !- T) xz

 infixr 4 _\\_
 _\\_ : forall x {T xz} -> T :< xz -, x -> x !- T :< xz
 x \\ t ^ th -, .x = ll t ^ th
 x \\ t ^ th -^ .x = kk t ^ th

 infixl 4 _/*\_
 infix 6 _</_\>_
 record _/*\_ (S T : Bwd X -> Set)(scope : Bwd X) : Set where
   constructor _</_\>_
   field
     {lsupp rsupp} : Bwd X
     {lthin} : lsupp <= scope
     {rthin} : rsupp <= scope
     outl  : S lsupp
     cover : lthin /u\ rthin
     outr  : T rsupp

 module _ {S T : Bwd X -> Set} where

  infixl 2 _/,\_
  _/,\_ : [(S :<_) -:> (T :<_) -:> (S /*\ T :<_)]
  s ^ th /,\ t ^ ph = let (! _ , ps , _) , _ , _ , u = th /+\ ph
                      in  s </ u \> t ^ ps

  data Pr {xz}(s : S :< xz)(t : T :< xz) : S /*\ T :< xz -> Set
    where
    mkPr : {x : <(_ <=_) :* (_<= xz) :* (_ <=_)>} -> let ! th , ps , ph = x in
      th & ps =< thin s -> (u : th /u\ ph) -> ph & ps =< thin t ->
      Pr s t (thing s </ u \> thing t ^ ps)

  covPr : forall {iz jz kz xz}{th : iz <= kz}{ph : jz <= kz}{ps : kz <= xz}
    {s : S iz}{t : T jz}{c : th /u\ ph} ->
    Pr (s ^ th -<- ps) (t ^ ph -<- ps) (s </ c \> t ^ ps)
  covPr = mkPr (_ -&- _) _ (_ -&- _)

  prPr : Tan (S :<_) (T :<_) \ s t -> Pr s t (s /,\ t)
  prPr {_}{s ^ th}{t ^ ph} with th /+\ ph
  prPr {_}{s ^ th}{t ^ ph} | ! v , w , u = mkPr v u w

  pr< : Tether (S :<_) (T :<_) ((S /*\ T) :<_) \ s t st ->
    Pr s t st -> YAN (_ <=_) \ th -> Pr (s :- th) (t :- th) (st :- th)
  pr< (mkPr v u w) th = mkPr (v &< th) u (w &< th)

  prInj : forall {ga}{s s' : S :< ga}{t t' : T :< ga}{st : S /*\ T :< ga} ->
    Pr s t st -> Pr s' t' st -> (s ~ s') * (t ~ t')
  prInj (mkPr lv c rv) (mkPr lu .c ru) rewrite lv ~&~ lu | rv ~&~ ru = r~ , r~

  _~Pr~_ : forall {ga}{s : S :< ga}{t : T :< ga}{st st' : S /*\ T :< ga} ->
     Pr s t st -> Pr s t st' -> st ~ st'
  mkPr lv c rv ~Pr~ mkPr lu b ru with copQ (! lv , rv , c) (! lu , ru , b)
  ... | r~ = r~

-}
