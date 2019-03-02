module Hull where

open import Basics
open import Eq
open import Bwd
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
  hole : forall {de} t {th : de <= ga}{t'} -> t' == (t ^ th) -> Match (hole th) t'

hull : forall {M ga}(t : Term M ga lib chk) ->
  let de , th , t' = support t in
  Sg (Pat de) \ p -> Match (p ^P th) t *
  ((p' : Pat ga) -> Match p' t -> (p ^P th) <P= p')
hull (! a) = atom a , atom a , \
  { .(atom a) (atom a) -> atom a
  ; .(hole _) (hole t x) -> hole (atom a) refl }
hull (s & t) with support s | hull s | support t | hull t
... | des , ths , s' , sq , us | p , ps , up | det , tht , t' , tq , ut | q , qt , uq
    with coproduct ths tht
... | de , phs , pht , th , t0 , t1 , u
  rewrite sym (patTri p t0) | sym (patTri q t1)
  = cons (p ^P phs) (q ^P pht)
  , cons ps qt
  , \ { .(cons _ _) (cons m0 m1) -> cons (up _ m0) (uq _ m1)
      ; .(hole _) (hole (! a) ())
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
      }
hull (\\ t) with support t | hull t
hull (\\ ._) | de , (th no) , t' , refl , ut | q , qt , uq
  rewrite sym (patTri q (oiTri th nosuno))
  = abst (q ^P (oi no)) , abst qt
  , \ { .(abst _) (abst m) -> abst (uq _ m)
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
      }
hull (\\ ._) | (de -, <>) , (th su) , t' , refl , ut | q , qt , uq
  = abst q , abst qt
  , \ { .(abst _) (abst m) -> abst (uq _ m)
      ; .(hole _) (hole (! _) ())
      ; .(hole _) (hole (_ & _) ())
      ; .(hole _) (hole (\\ t+) {th+} x) -> termNoConf x \ y -> termNoConf y \ z ->
          let tph , t0 = ut _ (th+ su) t+ z in
          hole (abst (q ^P tph)) (abst $= patTri q t0)
      ; .(hole _) (hole (thnk _) ())
      ; .(hole _) (hole (_ ?- _) ()) }
hull (thnk t) with support t
... | de , th , t' , refl , ut
  = hole oi
  , hole (thnk t') (thnk $= ((t' ^_) $= sym (idcoC th)))
  , \ { .(hole _) (hole (essl _) ())
      ; .(hole _) (hole (thnk t+) {th+} x) -> termNoConf x \ y -> 
          let ph , t0 = ut _ th+ t+ y in
          hole (hole ph) (hole $=
            ((ph -< th+) =[ triDet (mkTri ph th+) t0 >=
            th =< idcoC th ]=
            (oi -< th) [QED])) 
      ; .(hole _) (hole (_ ?- _) ()) }
hull (x ?- ez) with supportz ez
... | de , th , ez' , refl , uez
  = hole oi
  , hole (x ?- ez') ((x ?-_) $= (actz ez' $= ((refl ,_) $= sym (idcoC th))))
  , \ { .(hole _) (hole (essl t) ())
      ; .(hole _) (hole (thnk t) ())
      ; .(hole _) (hole (x+ ?- ez+) {th+} y) -> termNoConf y \ {refl refl z ->
         let ph , t0 = uez _ th+ ez+ z in
         hole (hole ph) (hole $= (
            (ph -< th+) =[ triDet (mkTri ph th+) t0 >=
            th =< idcoC th ]=
            (oi -< th) [QED])) }
      }
