module Pat where

open import String

open import Fun
open import Basics
open import Cats
open import Eq
open import Bwd
open import All
open import Thin
open import Atom

open Cat (OPE {One})

data Pat (ga : Nat) : Set where
  !!!_  : (a : Atom)                          -> Pat ga
  _&&&_ : (p q : Pat ga)                      -> Pat ga
  \\\_  : (q : Pat (ga -, <>))                -> Pat ga
  ???   : String -> {de : Nat}(th : de <= ga) -> Pat ga

infixr 60 !!!_
infixr 40 _&&&_ \\\_


PatNoConf : forall {G}(p0 p1 : Pat G) -> Set -> Set
PatNoConf (!!! a0) (!!! a1) P = a0 == a1 -> P
PatNoConf (p0 &&& q0) (p1 &&& q1) P = p0 == p1 -> q0 == q1 -> P
PatNoConf (\\\ q0) (\\\ q1) P = q0 == q1 -> P
PatNoConf (??? x0 {D0} th0) (??? x1 {D1} th1) P = x0 == x1 -> Pi (D0 == D1) \ { refl -> th0 == th1 -> P }
PatNoConf _ _ P = One

patNoConf : forall {G}{p0 p1 : Pat G} -> p0 == p1 -> {P : Set} -> PatNoConf p0 p1 P -> P
patNoConf {p0 = !!! a} refl m = m refl
patNoConf {p0 = p &&& q} refl m = m refl refl
patNoConf {p0 = \\\ q} refl m = m refl
patNoConf {p0 = ??? _ th} refl m = m refl refl refl

infixl 30 _<P-_
data _<P-_ {ga}(de : Nat) : Pat ga -> Set where
  ???  : forall {x}{th : de <= ga}   -> de <P- ??? x th
  car  : forall {p q}    -> de <P- p -> de <P- p &&& q
  cdr  : forall {p q}    -> de <P- q -> de <P- p &&& q
  \\\_ : forall {q}      -> de <P- q -> de <P- \\\ q

schemIsIn : String -> forall {ga} -> Pat ga -> Two
schemIsIn s (!!! a) = #0
schemIsIn s (p &&& q) = schemIsIn s p \/ schemIsIn s q
schemIsIn s (\\\ q) = schemIsIn s q
schemIsIn s (??? x th) = primStringEquality s x

schemVar : (s : String) -> forall {ga}(p : Pat ga) -> So (schemIsIn s p) ->
  Sg _ \ de -> de <P- p
schemVar s (!!! a) ()
schemVar s (p &&& q) y with schemIsIn s q | schemVar s q
schemVar s (p &&& q) y | #0 | _ with schemVar s p y
... | _ , x = _ , car x
schemVar s (p &&& q) y | #1 | f with f <>
... | _ , x = _ , cdr x
schemVar s (\\\ q) y with schemVar s q y
... | _ , x = _ , \\\ x
schemVar s (??? x th) y = _ , ???

data Remove {ga}(de : Nat) : Pat ga -> Pat ga -> Set where
  ???  : forall {x}{th : de <= ga} -> Remove de (??? x th) (!!! 0)
  car  : forall {p p' q} -> Remove de p p' -> Remove de (p &&& q) (p' &&& q)
  cdr  : forall {p q q'} -> Remove de q q' -> Remove de (p &&& q) (p &&& q')
  \\\_ : forall {q q'} -> Remove de q q' -> Remove de (\\\ q) (\\\ q')

renom : forall {ga de}{p p' : Pat ga} -> Remove de p p' -> String
renom (??? {x}) = x
renom (car r) = renom r
renom (cdr r) = renom r
renom (\\\ r) = renom r

unholey : forall {ga} -> Pat ga -> Two
unholey (??? x th)  = #0
unholey (!!! a)     = #1
unholey (p &&& q)   = unholey p /\ unholey q
unholey (\\\ q)     = unholey q

infixl 30 _,P_ _,<P-_ _^P_

_,P_ : forall ga {de} -> Pat de -> Pat (ga -+ de)
ga ,P !!! a    = !!! a
ga ,P p &&& q  = (ga ,P p) &&& (ga ,P q)
ga ,P \\\ q    = \\\ (ga ,P q)
ga ,P ??? x th = ??? x (oi ^+ th)

_,<P-_ : forall ga {de' de}{p : Pat de} -> de' <P- p -> (ga -+ de') <P- (ga ,P p)
ga ,<P- ???   = ???
ga ,<P- car x = car (ga ,<P- x)
ga ,<P- cdr x = cdr (ga ,<P- x)
ga ,<P- \\\ x = \\\ (ga ,<P- x)

_^P_ : forall {ga de}(p : Pat ga)(ph : ga <= de) -> Pat de
!!! a    ^P ph = !!! a
p &&& q  ^P ph = (p ^P ph) &&& (q ^P ph)
\\\ q    ^P ph = \\\ (q ^P (ph su))
??? x th ^P ph = ??? x (th -< ph)

patTri : forall {ga0 ga1 ga2}(p : Pat ga0)
         {ph0 : ga0 <= ga1}{ph1 : ga1 <= ga2}{ph2 : ga0 <= ga2}
         (t : Tri ph0 ph1 ph2) ->
         ((p ^P ph0) ^P ph1) == (p ^P ph2)
patTri (!!! a)   t = refl
patTri (p &&& q) t = _&&&_ $= patTri p t =$= patTri q t
patTri (\\\ q)   t = \\\_ $= patTri q (t su)
patTri (??? x th) {ph0}{ph1}{ph2} t = ??? x $= (
  ((th -< ph0) -< ph1)
    =< cocoC th ph0 ph1 ]=
  (th -< (ph0 -< ph1))
    =[ (th -<_) $= triDet (mkTri ph0 ph1) t >=
  (th -< ph2)
    [QED])

_^<P-_ : forall {ga' ga de}{p : Pat ga} ->
         ga' <P- p -> (ph : ga <= de) -> ga' <P- (p ^P ph)
???   ^<P- ph = ???
car x ^<P- ph = car  (x ^<P- ph)
cdr x ^<P- ph = cdr  (x ^<P- ph)
\\\ x ^<P- ph = \\\ (x ^<P- (ph su))

_?P_ : forall {ga de}(th : ga <= de) -> Pat de -> Pat ga
ph ?P !!!_ a    = !!! a
ph ?P p &&& q   = (ph ?P p) &&& (ph ?P q)
ph ?P \\\ q     = \\\ ((ph su) ?P q)
ph ?P ??? x th  = let _ , th' , _ = pullback ph th in ??? x th'
