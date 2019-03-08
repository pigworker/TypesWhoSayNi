module Pat where

open import Fun
open import Basics
open import Cats
open import Eq
open import Bwd
open import All
open import Thin
open import Atom

open Cat (OPE {One})

Nat = Bwd One

data Pat (ga : Nat) : Set where
  atom : (a : Atom)                -> Pat ga
  cons : (p q : Pat ga)            -> Pat ga
  abst : (q : Pat (ga -, <>))      -> Pat ga
  hole : {de : Nat}(th : de <= ga) -> Pat ga

pattern _-_ p q = cons p q
pattern \\\_ q = abst q
infixr 40 _-_
infixr 45 \\\_

??? : forall {ga} -> Pat ga
??? = hole oi

PatNoConf : forall {G}(p0 p1 : Pat G) -> Set -> Set
PatNoConf (atom a0) (atom a1) P = a0 == a1 -> P
PatNoConf (cons p0 q0) (cons p1 q1) P = p0 == p1 -> q0 == q1 -> P
PatNoConf (abst q0) (abst q1) P = q0 == q1 -> P
PatNoConf (hole {D0} th0) (hole {D1} th1) P = Pi (D0 == D1) \ { refl -> th0 == th1 -> P }
PatNoConf _ _ P = One

patNoConf : forall {G}{p0 p1 : Pat G} -> p0 == p1 -> {P : Set} -> PatNoConf p0 p1 P -> P
patNoConf {p0 = atom a} refl m = m refl
patNoConf {p0 = cons p q} refl m = m refl refl
patNoConf {p0 = abst q} refl m = m refl
patNoConf {p0 = hole th} refl m = m refl refl

data _<P-_ {ga}(de : Nat) : Pat ga -> Set where
  hole : forall {th : de <= ga}   -> de <P- hole th
  car  : forall {p q} -> de <P- p -> de <P- cons p q
  cdr  : forall {p q} -> de <P- q -> de <P- cons p q
  abst : forall {q}   -> de <P- q -> de <P- abst q

data Remove {ga}(de : Nat) : Pat ga -> Pat ga -> Set where
  hole : forall {th : de <= ga} -> Remove de (hole th) (atom 0)
  car  : forall {p p' q} -> Remove de p p' -> Remove de (cons p q) (cons p' q)
  cdr  : forall {p q q'} -> Remove de q q' -> Remove de (cons p q) (cons p q')
  abst : forall {q q'} -> Remove de q q' -> Remove de (abst q) (abst q')

Unholey : forall {ga} -> Pat ga -> Set
Unholey (hole th) = Zero
Unholey (atom a) = One
Unholey (cons p q) = Unholey p * Unholey q
Unholey (abst q) = Unholey q

_,P_ : forall ga {de} -> Pat de -> Pat (ga -+ de)
ga ,P atom a   = atom a
ga ,P cons p q = cons (ga ,P p) (ga ,P q)
ga ,P abst q   = abst (ga ,P q)
ga ,P hole th  = hole (oi ^+ th)

_,<P-_ : forall ga {de' de}{p : Pat de} -> de' <P- p -> (ga -+ de') <P- (ga ,P p)
ga ,<P- hole   = hole
ga ,<P- car x  = car  (ga ,<P- x)
ga ,<P- cdr x  = cdr  (ga ,<P- x)
ga ,<P- abst x = abst (ga ,<P- x)

_^P_ : forall {ga de}(p : Pat ga)(ph : ga <= de) -> Pat de
atom a   ^P ph = atom a
cons p q ^P ph = cons (p ^P ph) (q ^P ph)
abst q   ^P ph = abst (q ^P (ph su))
hole th  ^P ph = hole (th -< ph)

{-
comp^P : forall {ga0 ga1 ga2}(p : Pat ga0)(ph0 : ga0 <= ga1)(ph1 : ga1 <= ga2) ->
  (p ^P (ph0 -< ph1)) == ((p ^P ph0) ^P ph1)
comp^P (atom a)   ph0 ph1 = refl
comp^P (cons p q) ph0 ph1 = cons $= comp^P p ph0 ph1 =$= comp^P q ph0 ph1
comp^P (abst q)   ph0 ph1 = abst $= comp^P q (ph0 su) (ph1 su)
comp^P (hole th)  ph0 ph1 = hole $= cocoC th ph0 ph1
-}

patTri : forall {ga0 ga1 ga2}(p : Pat ga0)
         {ph0 : ga0 <= ga1}{ph1 : ga1 <= ga2}{ph2 : ga0 <= ga2}
         (t : Tri ph0 ph1 ph2) ->
         ((p ^P ph0) ^P ph1) == (p ^P ph2)
patTri (atom a)   t = refl
patTri (cons p q) t = cons $= patTri p t =$= patTri q t
patTri (abst q)   t = abst $= patTri q (t su)
patTri (hole th) {ph0}{ph1}{ph2} t = hole $= (
  ((th -< ph0) -< ph1)
    =< cocoC th ph0 ph1 ]=
  (th -< (ph0 -< ph1))
    =[ (th -<_) $= triDet (mkTri ph0 ph1) t >=
  (th -< ph2)
    [QED])


_^<P-_ : forall {ga' ga de}{p : Pat ga} ->
         ga' <P- p -> (ph : ga <= de) -> ga' <P- (p ^P ph)
hole   ^<P- ph = hole
car x  ^<P- ph = car  (x ^<P- ph)
cdr x  ^<P- ph = cdr  (x ^<P- ph)
abst x ^<P- ph = abst (x ^<P- (ph su))

_?P_ : forall {ga de}(th : ga <= de) -> Pat de -> Pat ga
ph ?P atom a   = atom a
ph ?P cons p q = cons (ph ?P p) (ph ?P q)
ph ?P abst q   = abst ((ph su) ?P q)
ph ?P hole th  = let _ , th' , _ = pullback ph th in hole th'

data _<P=_ {ga} : Pat ga -> Pat ga -> Set where
  atom : (a : Atom)                                 -> atom a   <P= atom a
  cons : forall {p p' q q'} -> p <P= p' -> q <P= q' -> cons p q <P= cons p' q'
  abst : forall {q q'} -> q <P= q'                  -> abst q   <P= abst q'
  hole : forall {de th}(p : Pat de){q : Pat ga} ->
                                (p ^P th) == q      -> q        <P= hole th

thickRefine : forall {ga de p0 p1}(ph : ga <= de) -> p0 <P= (p1 ^P ph) ->
  Sg (Pat ga) \ p -> ((p ^P ph) == p0) * (p <P= p1)
thickRefine {p1 = atom a}     ph (atom .a)      = atom a , refl , atom a
thickRefine {p1 = cons p1 q1} ph (cons p01 q01)
  with thickRefine ph p01 | thickRefine ph q01
... | p , pe , pr | q , qe , qr = cons p q , cons $= pe =$= qe , cons pr qr
thickRefine {p1 = abst q1}    ph (abst q01) with thickRefine (ph su) q01
... | q , qe , qr = abst q , abst $= qe , abst qr
thickRefine {p1 = hole th}    ph (hole p e)     =
  (p ^P th) , _ =[ patTri p (mkTri th ph) >= _ =[ e >= _ [QED] , hole p refl

refl<P= : forall {ga}(p : Pat ga) -> p <P= p
refl<P= (atom a)   = atom a
refl<P= (cons p q) = cons (refl<P= p) (refl<P= q)
refl<P= (abst q)   = abst (refl<P= q)
refl<P= (hole th)  = hole (hole oi) (hole $= idcoC _)

_-<P=-_ : forall {ga}{p0 p1 p2 : Pat ga}(p01 : p0 <P= p1)(p12 : p1 <P= p2) ->
          p0 <P= p2
p01 -<P=- hole {th = th} p1 refl with thickRefine th p01
... | p , pe , pr = hole p pe
atom .a      -<P=- atom a       = atom a
cons p01 q01 -<P=- cons p12 q12 = cons (p01 -<P=- p12) (q01 -<P=- q12)
abst q01     -<P=- abst q12     = abst (q01 -<P=- q12)

squeezeRefine : forall {ga de}(ph : ga <= de)(p : Pat de) ->
  ((ph ?P p) ^P ph) <P= p
squeezeRefine ph (atom a) = atom a
squeezeRefine ph (cons p q) = cons (squeezeRefine ph p) (squeezeRefine ph q)
squeezeRefine ph (abst q) = abst (squeezeRefine (ph su) q)
squeezeRefine ph (hole th) with pullback ph th
... | _ , ph' , th' , ps' , t0 , t1
    = hole (hole th') (hole $= (
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
pullbackPat (atom a) th0 (atom .a) th1 refl = atom a , refl , refl
pullbackPat (atom a) th0 (cons p1 p2) th1 ()
pullbackPat (atom a) th0 (abst p1) th1 ()
pullbackPat (atom a) th0 (hole th) th1 ()
pullbackPat (cons p0 p1) th0 (atom a) th1 ()
pullbackPat (cons p0 q0) th0 (cons p1 q1) th1 e = patNoConf e \ ep eq ->
  let p , ep0 , ep1 = pullbackPat p0 th0 p1 th1 ep
      q , eq0 , eq1 = pullbackPat q0 th0 q1 th1 eq
  in  cons p q , cons $= ep0 =$= eq0 , cons $= ep1 =$= eq1
pullbackPat (cons p0 p1) th0 (abst p2) th1 ()
pullbackPat (cons p0 p1) th0 (hole th) th1 ()
pullbackPat (abst p0) th0 (atom a) th1 ()
pullbackPat (abst p0) th0 (cons p1 p2) th1 ()
pullbackPat (abst q0) th0 (abst q1) th1 e = patNoConf e \ eq ->
  let q , eq0 , eq1 = pullbackPat q0 (th0 su) q1 (th1 su) eq
  in  abst q , abst $= eq0 , abst $= eq1
pullbackPat (abst p0) th0 (hole th) th1 ()
pullbackPat (hole th) th0 (atom a) th1 ()
pullbackPat (hole th) th0 (cons p1 p2) th1 ()
pullbackPat (hole th) th0 (abst p1) th1 ()
pullbackPat (hole th0') th0 (hole th1') th1 e
  with th0' -< th0 | mkTri th0' th0 | th1' -< th1 | mkTri th1' th1
pullbackPat (hole th0') th0 (hole th1') th1 refl | ps0 | t0 | .ps0 | t1
  with pullback th0 th1 | pullbackU th0 th1 t0 t1
... | de , ph0 , ph1 , ps' , t2 , t3 | ps , t4 , t5
    = hole ps , hole $= triDet (mkTri ps ph0) t4 , hole $= triDet (mkTri ps ph1) t5

squeezedRefine : forall {de ga p' p}(ph : de <= ga) ->
  (p' ^P ph) <P= p -> (p' ^P ph) <P= ((ph ?P p) ^P ph)
squeezedRefine {p' = atom a} {atom .a} ph (atom .a) = atom a
squeezedRefine {p' = cons p' p''} {atom a} ph ()
squeezedRefine {p' = abst p'} {atom a} ph ()
squeezedRefine {p' = hole th} {atom a} ph ()
squeezedRefine {p' = atom a} {cons p q} ph ()
squeezedRefine {p' = cons p' q'} {cons p q} ph (cons pr qr)
  = cons (squeezedRefine ph pr) (squeezedRefine ph qr)
squeezedRefine {p' = abst p'} {cons p q} ph ()
squeezedRefine {p' = hole th} {cons p q} ph ()
squeezedRefine {p' = atom a} {abst q} ph ()
squeezedRefine {p' = cons p' p''} {abst q} ph ()
squeezedRefine {p' = abst p'} {abst q} ph (abst r) = abst (squeezedRefine (ph su) r)
squeezedRefine {p' = hole th} {abst q} ph ()
squeezedRefine {p' = p'} {hole th} ph (hole p e) with pullback ph th | pullbackPat p' ph p th (sym e)
... | de , ph' , th' , ps' , t0 , t1 | q , eq' , eq = hole q (
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
patMono (atom a) (atom .a) th refl = refl
patMono (atom _) (cons _ _) th ()
patMono (atom _) (abst _) th ()
patMono (atom _) (hole _) th ()
patMono (cons _ _) (atom _) th ()
patMono (cons p q) (cons p' q') th e = patNoConf e \ e0 e1 -> 
  cons $= patMono p p' th e0 =$= patMono q q' th e1
patMono (cons _ _) (abst _) th ()
patMono (cons _ _) (hole _) th ()
patMono (abst _) (atom _) th ()
patMono (abst _) (cons _ _) th ()
patMono (abst p) (abst p') th q = patNoConf q \ e -> abst $= patMono p p' (th su) e
patMono (abst _) (hole _) th ()
patMono (hole _) (atom _) th ()
patMono (hole _) (cons _ _) th ()
patMono (hole _) (abst _) th ()
patMono (hole ph0) (hole ph1) th q = patNoConf q \ { refl e -> 
  hole $= qThinMono ph0 ph1 th e }

patRIrr : forall {ga}{p q : Pat ga}(r r' : p <P= q) -> r == r'
patRIrr (atom a) (atom .a) = refl
patRIrr (cons r0 r1) (cons r2 r3) rewrite patRIrr r0 r2 | patRIrr r1 r3 = refl
patRIrr (abst r) (abst r') rewrite patRIrr r r' = refl
patRIrr (hole p refl) (hole p' q) with patMono p' p _ q
patRIrr (hole p refl) (hole .p refl) | refl = refl

mpatRIrr : forall {ga}{p q : MPat ga}(r r' : p <MP= q) -> r == r'
mpatRIrr {p = fail} {q} r r' = refl
mpatRIrr {p = [ _ ]M} {fail} () r'
mpatRIrr {p = [ _ ]M} {[ _ ]M} r r' = patRIrr r r'

unify : forall {ga}(p0 p1 : Pat ga) ->
        Sg (MPat ga) \ p -> (p <MP= [ p0 ]M) * (p <MP= [ p1 ]M)
unify (hole th) p = [ (th ?P p) ^P th ]M , hole (th ?P p) refl , squeezeRefine th p
unify p (hole th) = [ (th ?P p) ^P th ]M , squeezeRefine th p , hole (th ?P p) refl 
unify (atom a0)    (atom a1) with atomEq? a0 a1
unify (atom a)  (atom .a) | #1 , refl = [ atom a ]M , atom a , atom a
unify (atom a0) (atom a1) | #0 , x = fail , <> , <>
unify (cons p0 q0) (cons p1 q1) with unify p0 p1 | unify q0 q1
unify (cons p0 q0) (cons p1 q1) | fail , _           | _        = fail , <> , <>
unify (cons p0 q0) (cons p1 q1) | [ _ ]M , _         | fail , _ = fail , <> , <>
unify (cons p0 q0) (cons p1 q1) | [ p ]M , pr0 , pr1 | [ q ]M , qr0 , qr1
  = [ cons p q ]M , cons pr0 qr0 , cons pr1 qr1
unify (abst q0)    (abst q1) with unify q0 q1
unify (abst q0) (abst q1) | fail , qr0 , qr1 = fail , <> , <>
unify (abst q0) (abst q1) | [ q ]M , qr0 , qr1
  = [ abst q ]M , abst qr0 , abst qr1
unify _ _  = fail , <> , <>

unifyU : forall {ga}(p0 p1 : Pat ga) ->
         let p , r0 , r1 = unify p0 p1 in
         ((p' : MPat ga) -> p' <MP= [ p0 ]M -> p' <MP= [ p1 ]M -> p' <MP= p)
unifyU p0 p1 fail r0 r1 = <>
unifyU (hole th) p1 [ x ]M (hole p refl) r1 = squeezedRefine th r1
unifyU (atom a) .(atom a) [ .(atom a) ]M (atom .a) (atom .a)
  rewrite atomEqLemma a = atom a
unifyU (cons p0 q0) (cons p1 q1) [ .(cons _ _) ]M (cons r0 r1) (cons r2 r3)
  with unify p0 p1 | unifyU p0 p1 _ r0 r2 | unify q0 q1 | unifyU q0 q1 _ r1 r3
... | fail , pr0 , pr1 | () | q , qr0 , qr1 | qu
... | [ p ]M , pr0 , pr1 | pu | fail , qr0 , qr1 | ()
... | [ p ]M , pr0 , pr1 | pu | [ q ]M , qr0 , qr1 | qu = cons pu qu
unifyU (abst q0) (abst q1) [ .(abst _) ]M (abst r0) (abst r1)
  with unify q0 q1 | unifyU q0 q1 _ r0 r1
... | fail , qr0 , qr1 | ()
... | [ q ]M , qr0 , qr1 | qu = abst qu
unifyU (atom a)     .(hole _) [ .(atom a) ]M (atom .a) (hole p x) = atom a
unifyU (cons p0 q0) .(hole _) [ .(cons _ _) ]M (cons r0 r1) (hole (atom a) ())
unifyU (cons p0 q0) (hole th) [ ._ ]M (cons r0 r1) (hole (cons p' q') refl) =
  squeezedRefine th (cons r0 r1)
unifyU (cons p0 q0) .(hole _) [ .(cons _ _) ]M (cons r0 r1) (hole (abst p) ())
unifyU (cons p0 q0) .(hole _) [ .(cons _ _) ]M (cons r0 r1) (hole (hole th) ())
unifyU (abst p0) .(hole _) [ .(abst _) ]M (abst r0) (hole (atom a) ())
unifyU (abst p0) .(hole _) [ .(abst _) ]M (abst r0) (hole (cons _ _) ())
unifyU (abst p0) (hole th) [ ._ ]M (abst r0) (hole (abst q') refl) =
  squeezedRefine th (abst r0)
unifyU (abst p0) .(hole _) [ .(abst _) ]M (abst r0) (hole (hole th) ())

sgIrr : forall {A B}{a0 a1 : A}(a : a0 == a1){b0 : B a0}{b1 : B a1} ->
  ((a : A)(b b' : B a) -> b == b') ->
  _==_ {_}{Sg A B} (a0 , b0) (a1 , b1)
sgIrr refl Birr = (_ ,_) $= Birr _ _ _

unifyEq : forall {ga}(p : Pat ga) -> unify p p == ([ p ]M , refl<P= p , refl<P= p)
unifyEq (atom a) rewrite atomEqLemma a = refl
unifyEq (cons p q) rewrite unifyEq p | unifyEq q = refl
unifyEq (abst q) rewrite unifyEq q = refl
unifyEq (hole th) with pullback th th | pullbackEq th
unifyEq (hole th) | .(_ , oi , oi , th , oiTri th , oiTri th) | refl
  = sgIrr ([_]M $= (hole $= idcoC _))
  \ { a (r0 , r1) (r2 , r3) -> _,_ $= mpatRIrr r0 r2 =$= mpatRIrr r1 r3 }   

_=/=_ : forall {ga}(p q : Pat ga) -> Set
p =/= q with unify p q
... | fail , _ = One
... | [ _ ]M , _ = Zero

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

boom : forall {ga}(p q : Pat ga) -> p =/= q -> p ~~ q -> Zero
boom p q n y with unify p q | unifyU p q
boom p q n (r , r0 , r1) | fail , _ , _ | u = u [ r ]M r0 r1
boom p q n y | [ x ]M , r0 , r1 | _ = n

moob : forall {ga}(p q : Pat ga) -> (p ~~ q -> Zero) -> p =/= q
moob p q n with unify p q
moob p q n | fail , _ = <>
moob p q n | [ r ]M , r0 , r1 = n (r , r0 , r1)

{-
asunder : forall {ga}{p' p q' q : Pat ga} ->
            p' <P= p -> q' <P= q -> p =/= q -> p' =/= q'
asunder {ga}{p'}{p}{q'}{q} r0 r1 a with unify p q | unifyU p q | unify p' q'
asunder {ga} {p'} {p} {q'} {q} r0 r1 a | fail , r2 , r3 | z | fail , r4 , r5 = <>
asunder {ga} {p'} {p} {q'} {q} r0 r1 a | fail , r2 , r3 | z | [ U ]M , r4 , r5
  = z _ (r4 -<P=- r0) (r5 -<P=- r1)
asunder {ga} {p'} {p} {q'} {q} r0 r1 () | [ x ]M , r2 , r3 | z | u' , r4 , r5
-}

Apartz : forall {X ga} -> (X -> Pat ga) -> Bwd X -> Pat ga -> Set
Apartz f [] p = One
Apartz f (xz -, y) p = Apartz f xz p * (f y =/= p)

Apart : forall {X ga} -> (X -> Pat ga) -> Bwd X -> Set
Apart f [] = One
Apart f (xz -, x) = Apart f xz * Apartz f xz (f x)

Pairwise : forall {X}(R : X -> X -> Set) -> Bwd X -> Set
Pairwise R xz = forall {x y} -> ([] -, x -, y) <= xz -> R x y

apartz : forall {X ga}(f : X -> Pat ga)(xz : Bwd X)(p : Pat ga) ->
  (forall {y}(i : y <- xz) -> f y ~~ p -> Zero) ->
  Apartz f xz p
apartz f [] p m = <>
apartz f (xz -, x) p m
  = apartz f xz p (m ` _no)
  , moob (f x) p (m (oe su))

ztrapa : forall {X ga}(f : X -> Pat ga)(xz : Bwd X)(p : Pat ga) ->
  Apartz f xz p ->
  forall {y}(i : y <- xz) -> f y ~~ p -> Zero
ztrapa f .(_ -, _) p (xaz , _) (th no) u = ztrapa f _ p xaz th u
ztrapa f .(_ -, _) p (_ , xa) (th su) u = boom _ _ xa u

apart : forall {X ga}(f : X -> Pat ga)(xz : Bwd X) ->
  Pairwise (\ x y -> f x ~~ f y -> Zero) xz -> Apart f xz
apart f [] pw = <>
apart f (xz -, x) pw = apart f xz (pw ` _no) , apartz f xz (f x) (pw ` _su)

trapa : forall {X ga}(f : X -> Pat ga)(xz : Bwd X) ->
  Apart f xz -> Pairwise (\ x y -> f x ~~ f y -> Zero) xz
trapa f [] <> () 
trapa f (xz -, x) (xza , xaz) (th no) = trapa f xz xza th
trapa f (xz -, x) (xza , xaz) (th su) = ztrapa f xz (f x) xaz th 

{-
cartApart : forall {X Y ga}
  (f : X -> Pat ga)(xz : Bwd X)(g : Y -> Pat ga)(yz : Bwd Y) ->
  Apart f xz -> Apart g yz -> Apart (\ { (x , y) -> cons (f x) (g y)}) (cart xz yz)
cartApart f xz g yz xzA yzA = {!!}
-}
