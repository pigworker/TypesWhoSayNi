module Pat where

open import Eq
open import Cats
open import Basics
open import Bwd
open import Thin
open import Atom
open import All
open import Term
open import ActGood

data Mebbe (X : Set) : Set where
  aye : X -> Mebbe X
  naw : Mebbe X

_>>=_ : forall {X Y} -> Mebbe X -> (X -> Mebbe Y) -> Mebbe Y
naw   >>= k = naw
aye x >>= k = k x

data Pat (G : Nat) : Set where
  atom : (a : Atom)          -> Pat G
  cons : (p q : Pat G)       -> Pat G
  abst : (q : Pat (G -, <>)) -> Pat G
  --
  hole : {D : Nat} -> D <= G -> Pat G

_^P_ : forall {D G} -> Pat D -> (th : D <= G) -> Pat G
atom a   ^P th = atom a
cons p q ^P th = cons (p ^P th) (q ^P th)
abst p   ^P th = abst (p ^P (th su))
hole x   ^P th = hole (x -< th)

dom : forall {G} -> Pat G -> Bwd Nat
dom (atom a)        = []
dom (cons p q)      = dom p -+ dom q
dom (abst q)        = dom q
dom (hole {D} th)   = [] -, D

plug : forall {G N D}(p : Pat G) -> (dom p) %[ N ! D ] -> Term N (D -+ G) lib chk
plug (atom a)   tz = ! a
plug (cons p q) tz = plug p sz & plug q uz where
  i = dom p ; j = dom q ; sz = lefts i j tz ; uz = rights i j tz
plug (abst q)   tz = \\ plug q tz
plug (hole th)  tz = top tz ^ (oi ^+ th)

Match : forall {G N D}(p : Pat G) -> Term N (D -+ G) lib chk -> Set
Match {G}{N}{D} p t = Sg ((dom p) %[ N ! D ]) \ tz -> t == (plug p tz)

module _ where
  open Cat (OPE {One})
  
  match^P : forall {G G' N D}(p : Pat G)(th : G <= G')
    (tz' : (dom (p ^P th)) %[ N ! D ]) ->
    Sg ((dom p) %[ N ! D ]) \ tz -> plug (p ^P th) tz' == (plug p tz ^ (oi ^+ th))
  match^P (atom a) th [] = [] , refl
  match^P (cons p q) th tz'
    with match^P p th (lefts (dom (p ^P th)) (dom (q ^P th)) tz')
       | match^P q th (rights (dom (p ^P th)) (dom (q ^P th)) tz')
  ... | (lz , lq) | (rz , rq) = (lz :+ rz) , _&_
    $=  (_ =[ lq >= _ =< (_^ (oi ^+ th)) $= (plug p $= leftis lz rz) ]= _ [QED])
    =$= (_ =[ rq >= _ =< (_^ (oi ^+ th)) $= (plug q $= rightis lz rz) ]= _ [QED])
  match^P (abst p) th tz' with match^P p (th su) tz'
  ... | tz , tq = tz , \\_ $= tq
  match^P (hole ph) th ([] -, t) = ([] -, t) , 
    (t ^ (oi ^+ (ph -< th))) =< (t ^_) $=
      (((oi ^+ ph) -< (oi ^+ th)) =[ moco oi oi ph th >=
      ((oi -< oi) ^+ (ph -< th)) =[ (_^+ (ph -< th)) $= coidC _ >=
      (oi ^+ (ph -< th)) [QED]) ]=
    (t ^ ((oi ^+ ph) -< (oi ^+ th))) =< thinco t _ _ ]=
    ((t ^ (oi ^+ ph)) ^ (oi ^+ th)) [QED]

data _<P=_ {G : Nat} : Pat G -> Pat G -> Set where
  atom : (a : Atom) -> atom a <P= atom a
  cons : forall {p q p' q'} -> p <P= p' -> q <P= q' -> cons p q <P= cons p' q'
  abst : forall {q q'} -> q <P= q' -> abst q <P= abst q'
  hole : forall {D}{th : D <= G}(p : Pat D) ->
           (p ^P th) <P= hole th

_<MP=_ : forall {G : Nat} -> Mebbe (Pat G) -> Mebbe (Pat G) -> Set
naw <MP= _ = One
aye _ <MP= naw = Zero
aye p <MP= aye q = p <P= q

refiner : forall {G N D}{p p' : Pat G} -> p <P= p' ->
  (tz : (dom p) %[ N ! D ]) ->
  Sg ((dom p') %[ N ! D ]) \ tz' -> plug p' tz' == plug p tz
refiner (atom a) [] = [] , refl
refiner (cons {p} {q} {p'} {q'} rp rq) tz
  with refiner rp (lefts (dom p) (dom q) tz)
     | refiner rq (rights (dom p) (dom q) tz)
... | (sz , sq) | (uz , uq) = (sz :+ uz) , _&_
  $=  (_ =[ plug p' $= leftis sz uz >= _ =[ sq >= _ [QED])
  =$= (_ =[ plug q' $= rightis sz uz >= _ =[ uq >= _ [QED])
refiner (abst r) tz with refiner r tz
... | tz' , q = tz' , \\_ $= q
refiner (hole {th = th} p) tz with match^P p th tz
... | tz' , q = ([] -, plug p tz') , sym q

tighten : forall {D G}(th : D <= G)(p : Pat G) ->
  Sg (Pat D) \ r -> (r ^P th) <P= p
tighten th (atom a) = atom a , atom a
tighten th (cons p q) with tighten th p | tighten th q
... | p' , rp | q' , rq = cons p' q' , cons rp rq
tighten th (abst p) with tighten (th su) p
... | p' , r = abst p' , abst r
tighten th (hole ph) with pullback th ph
tighten th (hole ph) | _ , th' , ph' , ps' , t0 , t1 , u = hole th' ,
  help th ph th' ph' ps' t0 t1 where
  help : forall {D0 D D' G} (th : D <= G) (ph : D' <= G)
         (th' : D0 <= D) (ph' : D0 <= D') (ps' : D0 <= G) ->
       Tri th' th ps' -> Tri ph' ph ps' -> hole (th' -< th) <P= hole ph
  help th ph th' ph' ps' t0 t1
    rewrite (triDet (mkTri th' th) t0)
          | (triDet t1 (mkTri ph' ph))
          = hole (hole ph')



match? : forall {G N D}(p : Pat G)(t : Term N (D -+ G) lib chk) ->
  Dec (Match p t)
--
match? (atom a)   (! b)     with atomEq? a b
match? (atom a)   (! .a) | #1 , refl = #1 , ([] , refl)
match? (atom a)   (! b)  | #0 , anob = #0 , \ { (_ , refl) -> anob refl }
match? (atom a)   (_ & _)  = #0 , \ { (_ , ()) }
match? (atom a)   (\\ _)   = #0 , \ { (_ , ()) }
match? (atom a)   (thnk _) = #0 , \ { (_ , ()) }
match? (atom a)   (_ ?- _) = #0 , \ { (_ , ()) }
--
match? (cons p q) (s & t) with match? p s | match? q t
match? (cons p q) (s & t) | #0 , pnos | x  , r = #0 ,
  \ { (_ , refl) -> pnos (_ , refl) } 
match? (cons p q) (s & t) | #1 , l | #0 , qnot = #0 ,
  \ { (_ , refl) -> qnot (_ , refl) } 
match? (cons p q) (.(plug p sz) & .(plug q tz))
  | #1 , (sz , refl) | #1 , (tz , refl) = #1 , ((sz :+ tz) , (_&_
  $=  (plug p $= sym (leftis sz tz))
  =$= (plug q $= sym (rightis sz tz))))
match? (cons p q) (! _)    = #0 , \ { (_ , ()) }
match? (cons p q) (\\ _)   = #0 , \ { (_ , ()) }
match? (cons p q) (thnk _) = #0 , \ { (_ , ()) }
match? (cons p q) (_ ?- _) = #0 , \ { (_ , ()) }
--
match? (abst q) (\\ t)   with match? q t
match? (abst q) (\\ t) | #0 , qnot =  #0 ,
  \ { (_ , refl) -> qnot (_ , refl) } 
match? (abst q) (\\ .(plug q tz)) | #1 , (tz , refl) = #1 , (tz , refl)
match? (abst q) (! _)    = #0 , \ { (_ , ()) }
match? (abst q) (_ & _)  = #0 , \ { (_ , ()) }
match? (abst q) (thnk _) = #0 , \ { (_ , ()) }
match? (abst q) (_ ?- _) = #0 , \ { (_ , ()) }
--
match? (hole th)  t with dep? (oi ^+ th) t
match? (hole th) t | #0 , bad = #0 , \ { (([] -, t') , refl) -> bad (t' , refl) }
match? (hole th) .(t' ^ (oi ^+ th)) | #1 , (t' , refl) = #1 , (([] -, t') , refl)

_/\_ : forall {G}(p0 p1 : Pat G) ->
  Sg (Mebbe (Pat G)) \ p -> (p <MP= aye p0) * (p <MP= aye p1)
hole th /\ p1 with tighten th p1
... | p , r = aye (p ^P th) , hole p , r
atom a0 /\ atom a1 with atomEq? a0 a1
(atom a0 /\ atom a1) | #0 , q = naw , _
(atom a0 /\ atom .a0) | #1 , refl = aye (atom a0) , atom a0 , atom a0
cons p0 q0 /\ cons p1 q1 with p0 /\ p1 | q0 /\ q1
... | aye p , pr0 , pr1 | aye q , qr0 , qr1 =
  aye (cons p q) , (cons pr0 qr0) , (cons pr1 qr1) 
... | naw , _ | _ = naw , _
... | _ | naw , _ = naw , _
abst q0 /\ abst q1 with q0 /\ q1
... | aye q , r0 , r1 = aye (abst q) , abst r0 , abst r1
... | naw , _ = naw , _
_ /\ _ = naw , _
