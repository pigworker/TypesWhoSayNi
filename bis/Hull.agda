module Hull where

open import Basics
open import Eq
open import Atom
open import Bwd
open import All
open import Cats
open import Pat
open import Term
open import Thin
open import Supp
open import ActCats

open Monoidal (OPEMON {One})
open Cat (OPE {One})
open Act THIN

thinMatch : forall {M de ga ga'}(p : Pat ga)(th : ga <= ga')
  (pi' : Env M (de ,P (p ^P th))) ->
  Sg (Env M (de ,P p)) \ pi -> ((p %P pi) ^ (oi ^+ th)) == ((p ^P th) %P pi')
thinMatch (atom a) th (atom .a) = atom a , refl
thinMatch (cons p q) th (cons pi' chi') with thinMatch p th pi' | thinMatch q th chi'
... | pi , q0 | chi , q1 = cons pi chi , _&_ $= q0 =$= q1
thinMatch (abst q) th (abst chi') with thinMatch q (th su) chi'
... | chi , q0 = abst chi , \\_ $= q0
thinMatch (hole ph) th (hole t) = hole t ,
  ((t ^ (oi ^+ ph)) ^ (oi ^+ th))
    =[ thinco t _ _ >=
  (t ^ ((oi ^+ ph) -< (oi ^+ th)))
    =[ (t ^_) $= (
        ((oi ^+ ph) -< (oi ^+ th))
          =[ moco oi ph oi th >=
        ((oi -< oi) ^+ (ph -< th))
          =[ (_^+ (ph -< th)) $= idcoC _ >=
        (oi ^+ (ph -< th))
          [QED]) >=
  (t ^ (oi ^+ (ph -< th)))
    [QED] 

refineMatch : forall {M de ga}{p' p : Pat ga}(r : p' <P= p)(pi' : Env M (de ,P p')) ->
  Sg (Env M (de ,P p)) \ pi -> (p %P pi) == (p' %P pi')
refineMatch (atom a) (atom .a) = atom a , refl
refineMatch (cons r0 r1) (cons pi' chi') with refineMatch r0 pi' | refineMatch r1 chi'
... | pi , q0 | chi , q1 = cons pi chi , _&_ $= q0 =$= q1
refineMatch (abst r) (abst chi') with refineMatch r chi'
... | chi , q = abst chi , \\_ $= q
refineMatch (hole {th = th} p refl) pi' with thinMatch p th pi'
... | pi , q = hole (p %P pi) , q

data Match {M ga} : Pat ga -> Term M ga lib chk -> Set where
  atom : forall a -> Match (atom a) (! a)
  cons : forall {p q s t} -> Match p s -> Match q t -> Match (cons p q) (s & t)
  abst : forall {q t} -> Match q t -> Match (abst q) (\\ t)
  hole : forall {de}{th : de <= ga}{t t'} -> t <[ th ]= t' -> Match (hole th) t'

match : forall {M ga de}(p : Pat de)(pi : Env M (ga ,P p)) -> Match (ga ,P p) (p %P pi)
match (atom a) (atom .a) = atom a
match (p - q) (cons pi chi) = cons (match p pi) (match q chi)
match (\\\ q) (abst chi) = abst (match q chi)
match (hole th) (hole t) = hole (thinR t (oi ^+ th))

matchQ : forall {M ga de}(p : Pat de)(pi : Env M (ga ,P p))(t : Term M (ga -+ de) lib chk)
 -> (p %P pi) == t -> Match (ga ,P p) t
matchQ p pi _ refl = match p pi

{-
hull : forall {M ga}(t : Term M ga lib chk) ->
  let de , th , t' = support t in
  Sg (Pat de) \ p -> Match (p ^P th) t *
  ((p' : Pat ga) -> Match p' t -> (p ^P th) <P= p')
hull (! a) = atom a , atom a , \
  { .(atom a) (atom a) -> atom a
  ; .(hole _) (hole t) -> hole (atom a) refl }
hull (s & t) with support s | hull s | support t | hull t
... | des , ths , s' , sq , us | p , ps , up | det , tht , t' , tq , ut | q , qt , uq
    with coproduct ths tht
... | de , phs , pht , th , t0 , t1 , u
  rewrite sym (patTri p t0) | sym (patTri q t1)
  = cons (p ^P phs) (q ^P pht)
  , cons ps qt
  , \ { .(_ - _) (cons mp mq) -> cons (up _ mp) (uq _ mq)
      ; .(hole _) (hole (essl (cons sa ta))) -> {!!} }
    {- .(cons _ _) (cons m0 m1) -> cons (up _ m0) (uq _ m1)
      ; .(hole _) (hole ())
      ; .(hole th+) (hole (s+ & t+) {th+} refl) -> 
          let sph , t2 = us _ th+ s+ refl
              tph , t3 = ut _ th+ t+ refl
          in  hole (cons (p ^P sph) (q ^P tph)) (
               (cons $= (((p ^P sph) ^P th+) =[ patTri p t2 >=
                        (p ^P ths) =< patTri p t0 ]=
                        ((p ^P phs) ^P th) [QED])
                    =$= ((((q ^P tph) ^P th+) =[ patTri q t3 >=
                        (q ^P tht) =< patTri q t1 ]=
                        ((q ^P pht) ^P th) [QED]))))
      ; .(hole _) (hole (\\ st) ())
      ; .(hole _) (hole (thnk st) ())
      ; .(hole _) (hole (_ ?- _) ())
      -}
hull (\\ t) with support t | hull t
hull (\\ ._) | de , (th no) , t' , refl , ut | q , qt , uq
  rewrite sym (patTri q (oiTri th nosuno))
  = abst (q ^P (oi no)) , abst qt
  , {!!} {- .(abst _) (abst m) -> abst (uq _ m)
      ; .(hole _) (hole (! _) ())
      ; .(hole _) (hole (_ & _) ())
      ; .(hole _) (hole (\\ t+) {th+} x) -> termNoConf x \ y -> termNoConf y \ z ->
           let tph , t0 = ut _ (th+ su) t+ z in
           hole (abst (q ^P tph)) (abst $= (
              ((q ^P tph) ^P (th+ su)) =[ patTri q t0  >=
              (q ^P (th no)) =< patTri q (oiTri th nosuno) ]=
              ((q ^P (oi no)) ^P (th su)) [QED]))
      ; .(hole _) (hole (thnk t) ())
      ; .(hole _) (hole (_ ?- _) ())
      -}
hull (\\ ._) | (de -, <>) , (th su) , t' , refl , ut | q , qt , uq
  = abst q , abst qt
  , {!!} {- .(abst _) (abst m) -> abst (uq _ m)
      ; .(hole _) (hole (! _) ())
      ; .(hole _) (hole (_ & _) ())
      ; .(hole _) (hole (\\ t+) {th+} x) -> termNoConf x \ y -> termNoConf y \ z ->
          let tph , t0 = ut _ (th+ su) t+ z in
          hole (abst (q ^P tph)) (abst $= patTri q t0)
      ; .(hole _) (hole (thnk _) ())
      ; .(hole _) (hole (_ ?- _) ()) -}
hull (thnk t) with support t
... | de , th , t' , refl , ut
  = hole oi
  , {!!} -- hole (thnk t') (thnk $= ((t' ^_) $= sym (idcoC th)))
  , {!!} {- .(hole _) (hole (essl _) ())
      ; .(hole _) (hole (thnk t+) {th+} x) -> termNoConf x \ y -> 
          let ph , t0 = ut _ th+ t+ y in
          hole (hole ph) (hole $=
            ((ph -< th+) =[ triDet (mkTri ph th+) t0 >=
            th =< idcoC th ]=
            (oi -< th) [QED])) 
      ; .(hole _) (hole (_ ?- _) ()) -}
hull (x ?- ez) with supportz ez
... | de , th , ez' , refl , uez
  = hole oi
  , {!!} -- hole (x ?- ez') ((x ?-_) $= (actz ez' $= ((refl ,_) $= sym (idcoC th))))
  , {!!} {- .(hole _) (hole (essl t) ())
      ; .(hole _) (hole (thnk t) ())
      ; .(hole _) (hole (x+ ?- ez+) {th+} y) -> termNoConf y \ {refl refl z ->
         let ph , t0 = uez _ th+ ez+ z in
         hole (hole ph) (hole $= (
            (ph -< th+) =[ triDet (mkTri ph th+) t0 >=
            th =< idcoC th ]=
            (oi -< th) [QED])) }
      -}
-}

holeU : forall {ga de}(th : ga <= de)(p : Pat de) -> hole th ~~ p
holeU {ga}{de} th p = (th ?P p) ^P th , hole (th ?P p) refl , squeezeRefine th p

matchU : forall {M ga de}(p : Pat de)(ss : Env M (ga ,P p))
                         (q : Pat de)(ts : Env M (ga ,P q)) ->
                         p %P ss == q %P ts -> p ~~ q
matchU {ga = ga} (atom .a) (atom .a) (atom a) (atom .a) refl = atom a , atom a , atom a
matchU {ga = ga} (atom a) (atom .a) (_ - _) (cons _ t_) ()
matchU {ga = ga} (atom a) (atom .a) (\\\ q) (abst ts) ()
matchU {ga = ga} p ss (hole th) ts e with holeU th p
... | u , r0 , r1 = u , r1 , r0
matchU {ga = ga} (p - q) (cons ss ss₁) (atom a) (atom .a) ()
matchU {ga = ga} (p - q) (cons ss ts) (p' - q') (cons ss' ts') e = termNoConf e \ e -> termNoConf e \ e0 e1 ->
  let u0 , r0 , r1 = matchU p ss p' ss' e0 in
  let u1 , r2 , r3 = matchU q ts q' ts' e1 in
  cons u0 u1 , cons r0 r2 , cons r1 r3
matchU {ga = ga} (p - q) (cons _ _) (\\\ _) (abst ts) ()
matchU {ga = ga} (\\\ p) (abst ss) (atom a) (atom .a) ()
matchU {ga = ga} (\\\ p) (abst ss) (_ - _) (cons ts ts₁) ()
matchU {ga = ga} (\\\ p) (abst ss) (\\\ q) (abst ts) e = termNoConf e \ e -> termNoConf e \ e ->
  let u , r0 , r1 = matchU p ss q ts e in abst u , abst r0 , abst r1
matchU {ga = ga} (hole th) (hole s) q ts e = holeU th q

matchUnique : forall {M ga de}(p : Pat de)(ss ts : Env M (ga ,P p))
                 ->    p %P ss == p %P ts -> ss == ts
matchUnique (atom a) (atom .a) (atom .a) z = refl
matchUnique (p - q) (cons ss ss') (cons ts ts') z = termNoConf z \ z -> termNoConf z \ z0 z1 ->
  cons $= matchUnique p ss ts z0 =$= matchUnique q ss' ts' z1
matchUnique (\\\ p) (abst ss) (abst ts) z = termNoConf z \ z -> termNoConf z \ z ->
  abst $= matchUnique p ss ts z
matchUnique (hole th) (hole s) (hole t) z = hole $= thinMonoTerm s t (oi ^+ th) z
