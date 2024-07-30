module Ref where

open import Basics
open import Cats
open import Eq
open import Bwd
open import Atom
open import Thin
open import Pat

open Cat (OPE {One})

infixl 30 _<P=_

data _<P=_ {ga} : Pat ga -> Pat ga -> Set where
  !!!_  : (a : Atom)                                  -> !!! a   <P= !!! a
  _&&&_ : forall {p p' q q'} -> p <P= p' -> q <P= q'  -> p &&& q <P= p' &&& q'
  \\\_  : forall {q q'} -> q <P= q'                   -> \\\ q   <P= \\\ q'
  ???   : forall {x de th}(p : Pat de){q : Pat ga} ->
                                (p ^P th) == q        -> q       <P= ??? x th

refl<P= : forall {ga}(p : Pat ga) -> p <P= p
refl<P= (!!! a)   = !!! a
refl<P= (p &&& q) = (refl<P= p) &&& (refl<P= q)
refl<P= (\\\ q)   = \\\ (refl<P= q)
refl<P= (??? x th)  = ??? (??? x oi) (??? x $= idcoC _)

thickRefine : forall {ga de p0 p1}(ph : ga <= de) -> p0 <P= (p1 ^P ph) ->
  Sg (Pat ga) \ p -> ((p ^P ph) == p0) * (p <P= p1)
thickRefine {p1 = !!! a}     ph (!!! .a)      = !!! a , refl , !!! a
thickRefine {p1 = _&&&_ p1 q1} ph (_&&&_ p01 q01)
  with thickRefine ph p01 | thickRefine ph q01
... | p , pe , pr | q , qe , qr = _&&&_ p q , _&&&_ $= pe =$= qe , _&&&_ pr qr
thickRefine {p1 = \\\_ q1}    ph (\\\_ q01) with thickRefine (ph su) q01
... | q , qe , qr = \\\_ q , \\\_ $= qe , \\\_ qr
thickRefine {p1 = ??? x th}    ph (??? p e)     =
  (p ^P th) , _ =[ patTri p (mkTri th ph) >= _ =[ e >= _ [QED] , ??? p refl


_-<P=-_ : forall {ga}{p0 p1 p2 : Pat ga}(p01 : p0 <P= p1)(p12 : p1 <P= p2) ->
          p0 <P= p2
p01 -<P=- ??? {th = th} p1 refl with thickRefine th p01
... | p , pe , pr = ??? p pe
!!!_ .a      -<P=- !!!_ a       = !!!_ a
_&&&_ p01 q01 -<P=- _&&&_ p12 q12 = _&&&_ (p01 -<P=- p12) (q01 -<P=- q12)
\\\_ q01     -<P=- \\\_ q12     = \\\_ (q01 -<P=- q12)

squeezeRefine : forall {ga de}(ph : ga <= de)(p : Pat de) ->
  ((ph ?P p) ^P ph) <P= p
squeezeRefine ph (!!!_ a) = !!!_ a
squeezeRefine ph (_&&&_ p q) = _&&&_ (squeezeRefine ph p) (squeezeRefine ph q)
squeezeRefine ph (\\\_ q) = \\\_ (squeezeRefine (ph su) q)
squeezeRefine ph (??? _ th) with pullback ph th
... | _ , ph' , th' , ps' , t0 , t1
    = ??? (??? _ th') (??? _ $= (
        (th' -< th)
          =[ triDet (mkTri th' th) t1 >=
        ps'
          =[ triDet t0 (mkTri ph' ph) >=
        (ph' -< ph)
          [QED]))

pullbackPat : forall {ga0 ga1 ga} p0 (th0 : ga0 <= ga) p1 (th1 : ga1 <= ga) ->
  (p0 ^P th0) == (p1 ^P th1) ->
  let de , ph0 , ph1 , ph , _ = pullback th0 th1
  in Sg (Pat de) \ p -> (p ^P ph0) == p0 * (p ^P ph1) == p1
pullbackPat (!!!_ a) th0 (!!!_ .a) th1 refl = !!!_ a , refl , refl
pullbackPat (!!!_ a) th0 (_&&&_ p1 p2) th1 ()
pullbackPat (!!!_ a) th0 (\\\_ p1) th1 ()
pullbackPat (!!!_ a) th0 (??? _ th) th1 ()
pullbackPat (_&&&_ p0 p1) th0 (!!!_ a) th1 ()
pullbackPat (_&&&_ p0 q0) th0 (_&&&_ p1 q1) th1 e = patNoConf e \ ep eq ->
  let p , ep0 , ep1 = pullbackPat p0 th0 p1 th1 ep
      q , eq0 , eq1 = pullbackPat q0 th0 q1 th1 eq
  in  _&&&_ p q , _&&&_ $= ep0 =$= eq0 , _&&&_ $= ep1 =$= eq1
pullbackPat (_&&&_ p0 p1) th0 (\\\_ p2) th1 ()
pullbackPat (_&&&_ p0 p1) th0 (??? _ th) th1 ()
pullbackPat (\\\_ p0) th0 (!!!_ a) th1 ()
pullbackPat (\\\_ p0) th0 (_&&&_ p1 p2) th1 ()
pullbackPat (\\\_ q0) th0 (\\\_ q1) th1 e = patNoConf e \ eq ->
  let q , eq0 , eq1 = pullbackPat q0 (th0 su) q1 (th1 su) eq
  in  \\\_ q , \\\_ $= eq0 , \\\_ $= eq1
pullbackPat (\\\_ p0) th0 (??? _ th) th1 ()
pullbackPat (??? _ th) th0 (!!!_ a) th1 ()
pullbackPat (??? _ th) th0 (_&&&_ p1 p2) th1 ()
pullbackPat (??? _ th) th0 (\\\_ p1) th1 ()
pullbackPat (??? _ th0') th0 (??? _ th1') th1 e
  with th0' -< th0 | mkTri th0' th0 | th1' -< th1 | mkTri th1' th1
pullbackPat (??? _ th0') th0 (??? _ th1') th1 refl | ps0 | t0 | .ps0 | t1
  with pullback th0 th1 | pullbackU th0 th1 t0 t1
... | de , ph0 , ph1 , ps' , t2 , t3 | ps , t4 , t5
    = ??? _ ps , ??? _ $= triDet (mkTri ps ph0) t4 , ??? _ $= triDet (mkTri ps ph1) t5


squeezedRefine : forall {de ga p' p}(ph : de <= ga) ->
  (p' ^P ph) <P= p -> (p' ^P ph) <P= ((ph ?P p) ^P ph)
squeezedRefine {p' = !!!_ a} { !!!_ .a} ph (!!!_ .a) = !!!_ a
squeezedRefine {p' = _&&&_ p' p''} { !!!_ a} ph ()
squeezedRefine {p' = \\\_ p'} { !!!_ a} ph ()
squeezedRefine {p' = ??? _ th} { !!!_ a} ph ()
squeezedRefine {p' = !!!_ a} {_&&&_ p q} ph ()
squeezedRefine {p' = _&&&_ p' q'} {_&&&_ p q} ph (_&&&_ pr qr)
  = _&&&_ (squeezedRefine ph pr) (squeezedRefine ph qr)
squeezedRefine {p' = \\\_ p'} {_&&&_ p q} ph ()
squeezedRefine {p' = ??? _ th} {_&&&_ p q} ph ()
squeezedRefine {p' = !!!_ a} {\\\_ q} ph ()
squeezedRefine {p' = _&&&_ p' p''} {\\\_ q} ph ()
squeezedRefine {p' = \\\_ p'} {\\\_ q} ph (\\\_ r) = \\\_ (squeezedRefine (ph su) r)
squeezedRefine {p' = ??? _ th} {\\\_ q} ph ()
squeezedRefine {p' = p'} {??? _ th} ph (??? p e) with pullback ph th | pullbackPat p' ph p th (sym e)
... | de , ph' , th' , ps' , t0 , t1 | q , eq' , eq = ??? q (
  (q ^P coC ph' ph)
    =< patTri q (mkTri ph' ph) ]=
  ((q ^P ph') ^P ph)
    =[ (_^P ph) $= eq' >=
  (p' ^P ph)
    [QED])


data MPat (ga : Nat) : Set where
  fail : MPat ga
  [_]M : Pat ga -> MPat ga

_<MP=_ : forall {ga} -> MPat ga -> MPat ga -> Set
fail   <MP= q      = One
[ p ]M <MP= fail   = Zero
[ p ]M <MP= [ q ]M = p <P= q

patMono : forall {ga de}(p p' : Pat ga)(th : ga <= de) ->
  (p ^P th) == (p' ^P th) -> p == p'
patMono (!!!_ a) (!!!_ .a) th refl = refl
patMono (!!!_ _) (_&&&_ _ _) th ()
patMono (!!!_ _) (\\\_ _) th ()
patMono (!!!_ _) (??? _ _) th ()
patMono (_&&&_ _ _) (!!!_ _) th ()
patMono (_&&&_ p q) (_&&&_ p' q') th e = patNoConf e \ e0 e1 -> 
  _&&&_ $= patMono p p' th e0 =$= patMono q q' th e1
patMono (_&&&_ _ _) (\\\_ _) th ()
patMono (_&&&_ _ _) (??? _ _) th ()
patMono (\\\_ _) (!!!_ _) th ()
patMono (\\\_ _) (_&&&_ _ _) th ()
patMono (\\\_ p) (\\\_ p') th q = patNoConf q \ e -> \\\_ $= patMono p p' (th su) e
patMono (\\\_ _) (??? _ _) th ()
patMono (??? _ _) (!!!_ _) th ()
patMono (??? _ _) (_&&&_ _ _) th ()
patMono (??? _ _) (\\\_ _) th ()
patMono (??? _ ph0) (??? _ ph1) th q = patNoConf q \ { refl refl e -> 
  ??? _ $= qThinMono ph0 ph1 th e }

patRIrr : forall {ga}{p q : Pat ga}(r r' : p <P= q) -> r == r'
patRIrr (!!!_ a) (!!!_ .a) = refl
patRIrr (_&&&_ r0 r1) (_&&&_ r2 r3) rewrite patRIrr r0 r2 | patRIrr r1 r3 = refl
patRIrr (\\\_ r) (\\\_ r') rewrite patRIrr r r' = refl
patRIrr (??? p refl) (??? p' q) with patMono p' p _ q
patRIrr (??? p refl) (??? .p refl) | refl = refl

mpatRIrr : forall {ga}{p q : MPat ga}(r r' : p <MP= q) -> r == r'
mpatRIrr {p = fail} {q} r r' = refl
mpatRIrr {p = [ _ ]M} {fail} () r'
mpatRIrr {p = [ _ ]M} {[ _ ]M} r r' = patRIrr r r'


unify : forall {ga}(p0 p1 : Pat ga) ->
        Sg (MPat ga) \ p -> (p <MP= [ p0 ]M) * (p <MP= [ p1 ]M)
unify (??? x th) p = [ (th ?P p) ^P th ]M , ??? (th ?P p) refl , squeezeRefine th p
unify p (??? x th) = [ (th ?P p) ^P th ]M , squeezeRefine th p , ??? (th ?P p) refl 
unify (!!! a0)    (!!! a1) with atomEq? a0 a1
unify (!!! a)     (!!! .a) | #1 , refl = [ !!! a ]M , !!! a , !!! a
unify (!!! a0)    (!!! a1) | #0 , x = fail , <> , <>
unify (p0 &&& q0) (p1 &&&  q1) with unify p0 p1 | unify q0 q1
unify (p0 &&& q0) (p1 &&&  q1) | fail , _           | _        = fail , <> , <>
unify (p0 &&& q0) (p1 &&&  q1) | [ _ ]M , _         | fail , _ = fail , <> , <>
unify (p0 &&& q0) (p1 &&&  q1) | [ p ]M , pr0 , pr1 | [ q ]M , qr0 , qr1
  = [ p &&& q ]M , pr0 &&& qr0 , pr1 &&& qr1
unify (\\\ q0)    (\\\ q1) with unify q0 q1
unify (\\\ q0)    (\\\ q1) | fail , qr0 , qr1 = fail , <> , <>
unify (\\\ q0)    (\\\ q1) | [ q ]M , qr0 , qr1
  = [ \\\ q ]M , \\\ qr0 , \\\_ qr1
unify _ _  = fail , <> , <>

unifyU : forall {ga}(p0 p1 : Pat ga) ->
         let p , r0 , r1 = unify p0 p1 in
         ((p' : MPat ga) -> p' <MP= [ p0 ]M -> p' <MP= [ p1 ]M -> p' <MP= p)
unifyU p0 p1 fail r0 r1 = <>
unifyU (??? _ th) p1 [ x ]M (??? p refl) r1 = squeezedRefine th r1
unifyU (!!!_ a) .(!!!_ a) [ .(!!!_ a) ]M (!!!_ .a) (!!!_ .a)
  rewrite atomEqLemma a = !!!_ a
unifyU (_&&&_ p0 q0) (_&&&_ p1 q1) [ .(_&&&_ _ _) ]M (_&&&_ r0 r1) (_&&&_ r2 r3)
  with unify p0 p1 | unifyU p0 p1 _ r0 r2 | unify q0 q1 | unifyU q0 q1 _ r1 r3
... | fail , pr0 , pr1 | () | q , qr0 , qr1 | qu
... | [ p ]M , pr0 , pr1 | pu | fail , qr0 , qr1 | ()
... | [ p ]M , pr0 , pr1 | pu | [ q ]M , qr0 , qr1 | qu = _&&&_ pu qu
unifyU (\\\_ q0) (\\\_ q1) [ .(\\\_ _) ]M (\\\_ r0) (\\\_ r1)
  with unify q0 q1 | unifyU q0 q1 _ r0 r1
... | fail , qr0 , qr1 | ()
... | [ q ]M , qr0 , qr1 | qu = \\\_ qu
unifyU (!!!_ a)     .(??? _ _) [ .(!!!_ a) ]M (!!!_ .a) (??? p x) = !!!_ a
unifyU (_&&&_ p0 q0) .(??? _ _) [ .(_&&&_ _ _) ]M (_&&&_ r0 r1) (??? (!!!_ a) ())
unifyU (_&&&_ p0 q0) (??? _ th) [ ._ ]M (_&&&_ r0 r1) (??? (_&&&_ p' q') refl) =
  squeezedRefine th (_&&&_ r0 r1)
unifyU (_&&&_ p0 q0) .(??? _ _) [ .(_&&&_ _ _) ]M (_&&&_ r0 r1) (??? (\\\_ p) ())
unifyU (_&&&_ p0 q0) .(??? _ _) [ .(_&&&_ _ _) ]M (_&&&_ r0 r1) (??? (??? _ th) ())
unifyU (\\\_ p0) .(??? _ _) [ .(\\\_ _) ]M (\\\_ r0) (??? (!!!_ a) ())
unifyU (\\\_ p0) .(??? _ _) [ .(\\\_ _) ]M (\\\_ r0) (??? (_&&&_ _ _) ())
unifyU (\\\_ p0) (??? _ th) [ ._ ]M (\\\_ r0) (??? (\\\_ q') refl) =
  squeezedRefine th (\\\_ r0)
unifyU (\\\_ p0) .(??? _ _) [ .(\\\_ _) ]M (\\\_ r0) (??? (??? _ th) ())

sgIrr : forall {A B}{a0 a1 : A}(a : a0 == a1){b0 : B a0}{b1 : B a1} ->
  ((a : A)(b b' : B a) -> b == b') ->
  _==_ {_}{Sg A B} (a0 , b0) (a1 , b1)
sgIrr refl Birr = (_ ,_) $= Birr _ _ _

unifyEq : forall {ga}(p : Pat ga) -> unify p p == ([ p ]M , refl<P= p , refl<P= p)
unifyEq (!!! a) rewrite atomEqLemma a = refl
unifyEq (p &&& q) rewrite unifyEq p | unifyEq q = refl
unifyEq (\\\ q) rewrite unifyEq q = refl
unifyEq (??? _ th) with pullback th th | pullbackEq th
unifyEq (??? _ th) | .(_ , oi , oi , th , oiTri th , oiTri th) | refl
  = sgIrr ([_]M $= (??? _ $= idcoC _))
  \ { a (r0 , r1) (r2 , r3) -> _,_ $= mpatRIrr r0 r2 =$= mpatRIrr r1 r3 }   

_=/=_ : forall {ga}(p q : Pat ga) -> Two
p =/= q with unify p q
... | fail , _ = #1
... | [ _ ]M , _ = #0

_~~_ : forall {ga}(p q : Pat ga) -> Set
p ~~ q = Sg _ \ r -> r <P= p * r <P= q

unify? : forall {ga}(p q : Pat ga) -> Dec (p ~~ q)
unify? p q with unify p q | unifyU p q
unify? p q | fail , r0 , r1 | u = #0 , \ { (r , r2 , r3) -> u [ r ]M r2 r3 }
unify? p q | [ r ]M , r0 , r1 | u = #1 , r , r0 , r1

sym~~ : forall {ga}(p q : Pat ga) -> p ~~ q -> q ~~ p
sym~~ p q pq with unify? q p
sym~~ p q (r , rp , rq) | #0 , n = naughty (n (r , rq , rp))
sym~~ p q pq | #1 , y = y

boom : forall {ga}(p q : Pat ga) -> So (p =/= q) -> p ~~ q -> Zero
boom p q n y with unify p q | unifyU p q
boom p q n (r , r0 , r1) | fail , _ , _ | u = u [ r ]M r0 r1
boom p q n y | [ x ]M , r0 , r1 | _ = n

moob : forall {ga}(p q : Pat ga) -> (p ~~ q -> Zero) -> So (p =/= q)
moob p q n with unify p q
moob p q n | fail , _ = <>
moob p q n | [ r ]M , r0 , r1 = n (r , r0 , r1)

Apartz : forall {X ga} -> (X -> Pat ga) -> Bwd X -> Pat ga -> Two
Apartz f [] p = #1
Apartz f (xz -, y) p = Apartz f xz p /\ (f y =/= p)

Apart : forall {X ga} -> (X -> Pat ga) -> Bwd X -> Two
Apart f [] = #1
Apart f (xz -, x) = Apart f xz /\ Apartz f xz (f x)

Pairwise : forall {X}(R : X -> X -> Set) -> Bwd X -> Set
Pairwise R xz = forall {x y} -> ([] -, x -, y) <= xz -> R x y

ztrapa : forall {X ga}(f : X -> Pat ga)(xz : Bwd X)(p : Pat ga) ->
  So (Apartz f xz p) ->
  forall {y}(i : y <- xz) -> f y ~~ p -> Zero
ztrapa f .(_ -, _) p apa (th no) u = ztrapa f _ p (soOutl apa) th u
ztrapa f .(_ -, _) p apa (th su) u = boom _ _ (soOutr apa) u

trapa : forall {X ga}(f : X -> Pat ga)(xz : Bwd X) ->
  So (Apart f xz) -> Pairwise (\ x y -> f x ~~ f y -> Zero) xz
trapa f [] <> () 
trapa f (xz -, x) apa (th no) = trapa f xz (soOutl apa) th
trapa f (xz -, x) apa (th su) = ztrapa f xz (f x) (soOutr apa) th 
