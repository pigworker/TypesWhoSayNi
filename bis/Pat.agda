module Pat where

open import Basics
open import Cats
open import Eq
open import Bwd
open import Thin
open import Atom

open Cat (OPE {One})

Nat = Bwd One

data Pat (ga : Nat) : Set where
  atom : (a : Atom)                -> Pat ga
  cons : (p q : Pat ga)            -> Pat ga
  abst : (q : Pat (ga -, <>))      -> Pat ga
  hole : {de : Nat}(th : de <= ga) -> Pat ga

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
  hole : forall {th : de <= ga} -> Remove de (hole th) (atom NIL)
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

comp^P : forall {ga0 ga1 ga2}(p : Pat ga0)(ph0 : ga0 <= ga1)(ph1 : ga1 <= ga2) ->
  (p ^P (ph0 -< ph1)) == ((p ^P ph0) ^P ph1)
comp^P (atom a)   ph0 ph1 = refl
comp^P (cons p q) ph0 ph1 = cons $= comp^P p ph0 ph1 =$= comp^P q ph0 ph1
comp^P (abst q)   ph0 ph1 = abst $= comp^P q (ph0 su) (ph1 su)
comp^P (hole th)  ph0 ph1 = hole $= cocoC th ph0 ph1

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
  (p ^P th) , _ =< comp^P p th ph ]= _ =[ e >= _ [QED] , hole p refl

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
... | _ , ph' , th' , ps' , t0 , t1 , u
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
  with pullback th0 th1
... | de , ph0 , ph1 , ps' , t2 , t3 , u
  with u t0 t1
... | ps , t4 , t5
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
... | de , ph' , th' , ps' , t0 , t1 , u | q , eq' , eq = hole q (
  (q ^P coC ph' ph)
    =[ comp^P q ph' ph >=
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

unify : forall {ga}(p0 p1 : Pat ga) ->
        Sg (MPat ga) \ p ->
        (p <MP= [ p0 ]M) *
        (p <MP= [ p1 ]M) *
        ((p' : MPat ga) -> p' <MP= [ p0 ]M -> p' <MP= [ p1 ]M -> p' <MP= p)
unify (hole th) p
  = [ (th ?P p) ^P th ]M
  , hole (th ?P p) refl
  , squeezeRefine th p
  , \ { fail _ _ -> <>
      ; [ .(p' ^P _) ]M (hole p' refl) p'1 -> squeezedRefine th p'1 }
unify p (hole th)
  = [ (th ?P p) ^P th ]M
  , squeezeRefine th p
  , hole (th ?P p) refl
  , \ { fail _ _ -> <>
      ; [ .(p' ^P _) ]M p'0 (hole p' refl) -> squeezedRefine th p'0 }
unify (atom a0)    (atom a1) with atomEq? a0 a1
unify (atom a)  (atom .a) | #1 , refl = [ atom a ]M , atom a , atom a ,
  \ { fail p'0 p'1 -> <> ; [ .(atom a) ]M (atom a) (atom .a) -> atom a }
unify (atom a0) (atom a1) | #0 , x = fail , <> , <> , 
  \ { fail p'0 p'1 -> <> ; [ .(atom a0) ]M (atom a0) (atom .a0) -> x refl }
unify (cons p0 q0) (cons p1 q1) with unify p0 p1 | unify q0 q1
unify (cons p0 q0) (cons p1 q1)
  | fail , pr0 , pr1 , pu | q , qr0 , qr1 , qu
  = fail , <> , <> ,
  \ { fail _ _ -> <>
    ; [ .(cons _ _) ]M (cons p'0 q'0) (cons p'1 q'1) ->
      pu [ _ ]M p'0 p'1 }
unify (cons p0 q0) (cons p1 q1)
  | [ p ]M , pr0 , pr1 , pu | fail , qr0 , qr1 , qu
  = fail , <> , <> ,
  \ { fail _ _ -> <>
    ; [ .(cons _ _) ]M (cons p'0 q'0) (cons p'1 q'1) ->
      qu [ _ ]M q'0 q'1 }
unify (cons p0 q0) (cons p1 q1)
  | [ p ]M , pr0 , pr1 , pu | [ q ]M , qr0 , qr1 , qu
  = [ cons p q ]M , cons pr0 qr0 , cons pr1 qr1 ,
  \ { fail _ _ -> <>
    ; [ .(cons _ _) ]M (cons p'0 q'0) (cons p'1 q'1) ->
      cons (pu [ _ ]M p'0 p'1) (qu [ _ ]M q'0 q'1) }
unify (abst q0)    (abst q1) with unify q0 q1
unify (abst q0) (abst q1) | fail , qr0 , qr1 , qu = fail , <> , <> ,
  \ { fail _ _ -> <> ; [ .(abst _) ]M (abst q'0) (abst q'1) ->
                           qu [ _ ]M q'0 q'1 }
unify (abst q0) (abst q1) | [ q ]M , qr0 , qr1 , qu
  = [ abst q ]M , abst qr0 , abst qr1 ,
  \ { fail _ _ -> <> ; [ .(abst _) ]M (abst q'0) (abst q'1) ->
                           abst (qu [ _ ]M q'0 q'1) }
unify (atom a) (cons p1 p2)  = fail , <> , <> ,
  \ { fail _ _ -> <> ; [ .(atom a) ]M (atom a) () }
unify (atom a) (abst p1)     = fail , <> , <> ,
  \ { fail _ _ -> <> ; [ .(atom a) ]M (atom a) () }
unify (cons p0 p2) (atom a)  = fail , <> , <> ,
  \ { fail _ _ -> <> ; [ .(cons _ _) ]M (cons p'0 p'1) () }
unify (cons p0 p2) (abst p1) = fail , <> , <> ,
  \ { fail _ _ -> <> ; [ .(cons _ _) ]M (cons p'0 p'1) () }
unify (abst p0) (atom a)     = fail , <> , <> ,
  \ { fail _ _ -> <> ; [ .(abst _) ]M (abst p'0) () }
unify (abst p0) (cons p1 p2) = fail , <> , <> ,
  \ { fail _ _ -> <> ; [ .(abst _) ]M (abst p'0) () }
