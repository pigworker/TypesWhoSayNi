module Pat where

open import Eq
open import Fun
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

Aye : {X : Set}(mx : Mebbe X)(P : X -> Set) -> Set
Aye (aye x) P = P x
Aye naw P = Zero

data Pat (G : Nat) : Set where
  atom : (a : Atom)          -> Pat G
  cons : (p q : Pat G)       -> Pat G
  abst : (q : Pat (G -, <>)) -> Pat G
  --
  hole : {D : Nat} -> D <= G -> Pat G

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

plugCons : forall {G N D}{s t}
  (p q : Pat G)(sz : (dom p) %[ N ! D ])(tz : (dom q) %[ N ! D ]) ->
  plug p sz == s -> plug q tz == t -> plug (cons p q) (sz :+ tz) == (s & t)
plugCons p q sz tz sq tq rewrite leftis sz tz | rightis sz tz = _&_ $= sq =$= tq

Match : forall {G N D}(p : Pat G) -> Term N (D -+ G) lib chk -> Set
Match {G}{N}{D} p t = Sg ((dom p) %[ N ! D ]) \ tz -> t == (plug p tz)

module _ where
  open POLYTHIN
  open Act THIN

  _^P[_-<_] : forall {G0 G1 G2}(p : Pat G0)(th : G0 <= G1)(ph : G1 <= G2) ->
    ((p ^P th) ^P ph) == (p ^P (th -< ph))
  atom a ^P[ th -< ph ] = refl
  cons p q ^P[ th -< ph ] = cons $= (p ^P[ th -< ph ]) =$= (q ^P[ th -< ph ])
  abst q ^P[ th -< ph ] = abst $= (q ^P[ th su -< ph su ])
  hole ps ^P[ th -< ph ] = hole $= sym (cocoC ps th ph)

  match^P : forall {G G' N D}(p : Pat G)(th : G <= G')
    (tz' : (dom (p ^P th)) %[ N ! D ]) ->
    Sg ((dom p) %[ N ! D ]) \ tz -> plug (p ^P th) tz' == (plug p tz ^ (oi ^+ th))
  match^P (atom a) th [] = [] , refl
  match^P (cons p q) th tz'
    with match^P p th (lefts (dom (p ^P th)) (dom (q ^P th)) tz')
       | match^P q th (rights (dom (p ^P th)) (dom (q ^P th)) tz')
  ... | (lz , lq) | (rz , rq) = (lz :+ rz) ,
    _ =[ _&_ $= lq =$= rq >= _ =< (_^ (oi ^+ th)) $= plugCons p q lz rz refl refl ]= _ [QED]
  match^P (abst p) th tz' with match^P p (th su) tz'
  ... | tz , tq = tz , \\_ $= tq
  match^P (hole ph) th ([] -, t) = ([] -, t) , 
    (t ^ (oi ^+ (ph -< th))) =< (t ^_) $=
      (((oi ^+ ph) -< (oi ^+ th)) =[ moco oi oi ph th >=
      ((oi -< oi) ^+ (ph -< th)) =[ (_^+ (ph -< th)) $= coidC _ >=
      (oi ^+ (ph -< th)) [QED]) ]=
    (t ^ ((oi ^+ ph) -< (oi ^+ th))) =< thinco t _ _ ]=
    ((t ^ (oi ^+ ph)) ^ (oi ^+ th)) [QED]

  TriInv : forall {X}{iz jz kz : Bwd X}(th : iz <= jz)(ph : jz <= kz)(ps : iz <= kz) ->
    Set -> Set
  TriInv th (ph no) (ps no) P = Tri th ph ps -> P
  TriInv th (ph su) (ps no) P = forall th' -> th == (th' no) -> Tri th' ph ps -> P
  TriInv th (ph no) (ps su) P = One
  TriInv th (ph su) (ps su) P = forall th' -> th == (th' su) -> Tri th' ph ps -> P
  TriInv th ze ze P = P

  triInv : forall {X}{iz jz kz : Bwd X}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
    (t : Tri th ph ps){P : Set} -> TriInv th ph ps P -> P
  triInv (t no) m = m t
  triInv (t nosuno) m = m _ refl t
  triInv (t su) m = m _ refl t
  triInv ze m = m

  support : forall {M G l d}(t : Term M G l d) ->
    Sg _ \ D -> Sg (Term M D l d) \ t' -> Sg (D <= G) \ th -> t == (t' ^ th) *
    (forall {E}(t_ : Term M E l d)(ph : E <= G) -> t == (t_ ^ ph) ->
     Sg (D <= E) \ ps -> Tri ps ph th)
  supportz : forall {M G X}(ez : All (\ _ -> Term M G lib syn) X) ->
    Sg _ \ D -> Sg (All (\ _ -> Term M D lib syn) X) \ ez' -> Sg (D <= G) \ th -> ez == actz ez' (oi , th) *
    (forall {E}(ez_ : All (\ _ -> Term M E lib syn) X)(ph : E <= G) -> ez == actz ez_ (oi , ph) ->
    Sg (D <= E) \ ps -> Tri ps ph th)
  support (atom a) = [] , atom a , oe , refl , \
    { (atom a) ph refl -> oe , oeTri ph ; (cons _ _) ph () ; (abst _) ph () }
  support (cons s t) with support s | support t
  ... | _ , s' , th , sq , sw | _ , t' , ph , tq , tw with coproduct th ph
  ... | _ , th' , ph' , ps , t0 , t1 , u =
    _ , cons (s' ^ th') (t' ^ ph') , ps ,
    cons $= (_ =[ sq >= _ =< (s' ^_) $= triDet (mkTri th' ps) t0 ]= _ =< thinco s' th' ps ]= _ [QED])
        =$= (_ =[ tq >= _ =< (t' ^_) $= triDet (mkTri ph' ps) t1 ]= _ =< thinco t' ph' ps ]= _ [QED]) ,
    \ { (cons s_ t_) th_ e -> termNoConf e \ se te -> 
        let _ , t2 = sw s_ th_ se ; _ , t3 = tw t_ th_ te ; _ , t4 , t5 , t6 = u t2 t3
        in  _ , t5
    ; (atom _) _ () ; (abst _) _ () }
  support (abst t) with support t
  support (abst t) | _ , t' , (th no) , tq , tw =
    _ , abst (t' ^ (oi no)) , th , abst $= (_ =[ tq >= _ =< (t' ^_) $= (_no $= idcoC _) ]= _ =< thinco t' (oi no) (th su) ]= _ [QED]) ,
    \ { (atom _) th_ () ; (cons _ _) th_ ()
      ; (abst t_) th_ e -> termNoConf e \ e -> let _ , x = tw t_ (th_ su) e in triInv x \ { _ _ y -> _ , y } }
  support (abst t) | _ , t' , (th su) , tq , tw = _ , abst t' , th , abst $= tq , 
    \ { (atom _) th_ () ; (cons _ _) th_ ()
      ; (abst t_) th_ e -> termNoConf e \ e -> let _ , x = tw t_ (th_ su) e in triInv x \ { _ _ y -> _ , y } }
  support (vari i) = _ , vari oi , i , vari $= sym (idcoC _) , 
    \ { (vari j) th refl -> _ , mkTri j th ; (elim _ _) th () }
  support (elim e s) with support e | support s
  ... | _ , e' , th , eq , ew | _ , s' , ph , sq , sw  with coproduct th ph
  ... | _ , th' , ph' , ps , t0 , t1 , u = _ , elim (e' ^ th') (s' ^ ph') , ps ,
    elim $= (_ =[ eq >= _ =< (e' ^_) $= triDet (mkTri th' ps) t0 ]= _ =< thinco e' th' ps ]= _ [QED])
        =$= (_ =[ sq >= _ =< (s' ^_) $= triDet (mkTri ph' ps) t1 ]= _ =< thinco s' ph' ps ]= _ [QED]) ,
    \ { (vari _) th_ ()
      ; (elim e_ s_) th_ q -> termNoConf q \ qe qs -> 
        let _ , t2 = ew e_ th_ qe ; _ , t3 = sw s_ th_ qs ; _ , t4 , t5 , t6 = u t2 t3
        in  _ , t5 }
  support {d = chk} (essl t) with support t
  ... | _ , t' , th , tq , tw = _ , essl t' , th , essl $= tq , 
    \ { (essl t_) th_ e -> termNoConf e \ e -> tw t_ th_ e
      ; (thnk _) th_ () ; (_ ?- _) th_ () }
  support {d = syn} (essl t) with support t
  ... | _ , t' , th , tq , tw = _ , essl t' , th , essl $= tq ,
    \ { (essl t_) th_ e -> termNoConf e \ e -> tw t_ th_ e
      ; (_ :: _) th_ () }
  support (thnk t) with support t
  ... | _ , t' , th , tq , tw = _ , thnk t' , th , thnk $= tq , 
    \ { (essl t_) th_ () ; (x ?- x₁) th_ ()
      ; (thnk t_) th_ e -> termNoConf e \ e -> tw t_ th_ e }
  support (t :: T) with support t | support T
  ... | _ , t' , th , tq , tw | _ , T' , ph , Tq , Tw with coproduct th ph
  ... | _ , th' , ph' , ps , t0 , t1 , u = _ , (t' ^ th') :: (T' ^ ph') , ps ,
    _::_ $= (_ =[ tq >= _ =< (t' ^_) $= triDet (mkTri th' ps) t0 ]= _ =< thinco t' th' ps ]= _ [QED])
        =$= (_ =[ Tq >= _ =< (T' ^_) $= triDet (mkTri ph' ps) t1 ]= _ =< thinco T' ph' ps ]= _ [QED]) , 
    \ { (essl t_) th ()
      ; (t_ :: T_) th_ e -> termNoConf e \ tq Tq ->
      let _ , t2 = tw t_ th_ tq ; _ , t3 = Tw T_ th_ Tq ; _ , t4 , t5 , t6 = u t2 t3
      in  _ , t5 }
  support (x ?- ez) with supportz ez
  ... | _ , ez' , th , ezq , ezw = _ , (x ?- ez') , th , _?-_ $= sym (coidC _) =$= ezq ,
    \ { (essl _) th_ () ; (thnk _) th_ ()
      ; (x ?- ez_) th_ e -> termNoConf e \ { refl refl e -> ezw ez_ th_ e } }
  supportz [] = _ , [] , oe , refl , \ { [] th_ q -> _ , oeTri _ }
  supportz (ez -, e) with supportz ez | support e
  ... | _ , ez' , th , ezq , ezw | _ , e' , ph , eq , ew with coproduct th ph
  ... | _ , th' , ph' , ps , t0 , t1 , u = _ , (actz ez' (oi , th') -, (e' ^ ph')) , ps ,
    _-,_ $= (_ =[ ezq >= _ =< (actz ez' ` (oi ,_)) $= triDet (mkTri th' ps) t0 ]=
             _ =< actz ez' $= ((_, _) $= coidC _) ]=
             _ =< coz ez' (oi , th') (oi , ps) ]= _ [QED])
        =$= (_ =[ eq >= _ =< (e' ^_) $= triDet (mkTri ph' ps) t1 ]= _ =< thinco e' ph' ps ]= _ [QED])
    , \ { (ez_@._ -, e_@._) th_ refl -> 
      let _ , t2 = ezw ez_ th_ refl ; _ , t3 = ew e_ th_ refl ; _ , t4 , t5 , t6 = u t2 t3 in _ , t5 }
    where open ActCompo THINTHINTHIN

data _<P=_ {G : Nat} : Pat G -> Pat G -> Set where
  atom : (a : Atom) -> atom a <P= atom a
  cons : forall {p q p' q'} -> p <P= p' -> q <P= q' -> cons p q <P= cons p' q'
  abst : forall {q q'} -> q <P= q' -> abst q <P= abst q'
  hole : forall {D}{p'}{th : D <= G}(p : Pat D) -> p' == (p ^P th) ->
           p' <P= hole th

_^R_ : forall {G D : Nat}{p0 p1 : Pat G}(r : p0 <P= p1)(th : G <= D) ->
  (p0 ^P th) <P= (p1 ^P th)
atom a ^R th = atom a
cons r s ^R th = cons (r ^R th) (s ^R th)
abst r ^R th = abst (r ^R (th su))
hole {th = ph} p refl ^R th = hole p (p ^P[ ph -< th ])

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
... | (sz , sq) | (uz , uq) = (sz :+ uz) , plugCons p' q' sz uz sq uq
refiner (abst r) tz with refiner r tz
... | tz' , q = tz' , \\_ $= q
refiner (hole {th = th} p refl) tz with match^P p th tz
... | tz' , q = ([] -, plug p tz') , sym q

pullbackPat : forall {D0 D1 G}(th : D0 <= G)(ph : D1 <= G) ->
  let _ , th' , ph' , ps' , _ = pullback th ph
  in (p0 : Pat D0)(p1 : Pat D1) ->
    (p0 ^P th) == (p1 ^P ph) ->
    Sg _ \ p -> (p0 == (p ^P th')) * (p1 == (p ^P ph'))
pullbackPat th ph (atom a) (atom .a) refl = atom a , refl , refl
pullbackPat th ph (atom a) (cons p1 p2) ()
pullbackPat th ph (atom a) (abst p1) ()
pullbackPat th ph (atom a) (hole x) ()
pullbackPat th ph (cons p0 p1) (atom a) ()
pullbackPat th ph (cons p0 q0) (cons p1 q1) e = patNoConf e \ ep eq ->
  let p , ep0 , ep1 = pullbackPat th ph p0 p1 ep
      q , eq0 , eq1 = pullbackPat th ph q0 q1 eq
  in  cons p q , cons $= ep0 =$= eq0 , cons $= ep1 =$= eq1
pullbackPat th ph (cons p0 p1) (abst p2) ()
pullbackPat th ph (cons p0 p1) (hole x) ()
pullbackPat th ph (abst p0) (atom a) ()
pullbackPat th ph (abst p0) (cons p1 p2) ()
pullbackPat th ph (abst p0) (abst p1) e = patNoConf e \ ep ->
  let p , ep0 , ep1 = pullbackPat (th su) (ph su) p0 p1 ep
  in  abst p , abst $= ep0 , abst $= ep1
pullbackPat th ph (abst p0) (hole x) ()
pullbackPat th ph (hole x) (atom a) ()
pullbackPat th ph (hole x) (cons p1 p2) ()
pullbackPat th ph (hole x) (abst p1) ()
pullbackPat th ph (hole th_) (hole ph_) e with pullback th ph | th_ -< th | mkTri th_ th | mkTri ph_ ph
pullbackPat th ph (hole th_) (hole ph_) refl | _ , th' , ph' , ps' , t0 , t1 , u | .(ph_ -< ph) | t2 | t3 =
  let ps , t4 , t5 = u t2 t3 in hole ps , hole $= triDet t4 (mkTri ps th') , hole $= triDet t5 (mkTri ps ph')

tighten : forall {D G}(th : D <= G)(p : Pat G) ->
  Sg (Pat D) \ r -> ((r ^P th) <P= p) *
  ((pD : Pat D) -> (pD ^P th) <P= p -> pD <P= r)
tighten th (atom a) = atom a , atom a ,
  \ { (atom a) (atom .a) -> atom a
    ; (cons _ _) () ; (abst pD) () ; (hole _) () }
tighten th (cons p q) with tighten th p | tighten th q
... | p' , rp , up | q' , rq , uq = cons p' q' , cons rp rq , 
  \ { (cons pD qD) (cons rG sG) -> cons (up _ rG) (uq _ sG)
    ; (atom a) () ; (abst pD) () ; (hole x) () }
tighten th (abst p) with tighten (th su) p
... | p' , r , u = abst p' , abst r , 
  \ { (abst pD) (abst rG) -> abst (u _ rG)
    ; (atom _) () ; (cons _ _) () ; (hole x) () }
tighten th (hole ph) with pullback th ph | pullbackPat th ph
tighten th (hole ph) | _ , th' , ph' , ps' , t0 , t1 , u | pp = 
  hole th' ,
  hole (hole ph')
    (hole $= ((th' -< th)  =[ triDet (mkTri th' th) t0 >=
              ps'          =< triDet (mkTri ph' ph) t1 ]=
              (ph' -< ph)  [QED])) ,
  \ { pD (hole pE x) -> 
      let pE , e0 , e1 = pp pD pE x in hole pE e0 }
  
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
  Sg (Mebbe (Pat G)) \ p -> (p <MP= aye p0) * (p <MP= aye p1) *
  ((p' : Pat G) -> p' <P= p0 -> p' <P= p1 -> aye p' <MP= p)
hole th /\ p with tighten th p
... | p' , r , u = aye (p' ^P th) , hole p' refl , r , 
  \ { _ (hole pD refl) r1 -> u _ r1 ^R th }
p /\ hole th with tighten th p
... | p' , r , u = aye (p' ^P th) , r , hole p' refl ,
  \ { _ r0 (hole pD refl) -> u _ r0 ^R th }
atom a0 /\ atom a1 with atomEq? a0 a1
(atom a0 /\ atom a1) | #0 , w = naw , _ , _ , 
  \ { _ (atom ._) (atom ._) -> w refl }
(atom a0 /\ atom .a0) | #1 , refl = aye (atom a0) , atom a0 , atom a0 ,
  \ { _ (atom ._) (atom ._) -> atom a0 }
cons p0 q0 /\ cons p1 q1 with p0 /\ p1 | q0 /\ q1
(cons p0 q0 /\ cons p1 q1) | aye p , pr0 , pr1 , up | aye q , qr0 , qr1 , uq =
  aye (cons p q) , cons pr0 qr0 , cons pr1 qr1 , 
  \ { _ (cons ps0 qs0) (cons ps1 qs1) -> cons (up _ ps0 ps1) (uq _ qs0 qs1) }
(cons p0 q0 /\ cons p1 q1) | aye p , pr0 , pr1 , up | naw , qr0 , qr1 , uq =
  naw , _ , _ , \ { _ (cons r0 s0) (cons r1 s1) -> uq _ s0 s1 }
(cons p0 q0 /\ cons p1 q1) | naw , pr0 , pr1 , up | q , qr0 , qr1 , uq =
  naw , _ , _ , \ { _ (cons r0 s0) (cons r1 s1) -> up _ r0 r1 } 
abst q0 /\ abst q1 with q0 /\ q1
(abst q0 /\ abst q1) | aye q , r0 , r1 , u = aye (abst q) , abst r0 , abst r1 ,
  \ { _ (abst r2) (abst r3) -> abst (u _ r2 r3) }
(abst q0 /\ abst q1) | naw , r0 , r1 , u = naw , _ , _ ,
  \ { _ (abst r2) (abst r3) -> u _ r2 r3 }
atom _ /\ cons _ _ = naw , _ , _ , \ { _ (atom _) () }
atom _ /\ abst _ = naw , _ , _ , \ { _ (atom _) () }
cons _ _ /\ atom _ = naw , _ , _ , \ { _ (cons _ _) () }
cons _ _ /\ abst _ = naw , _ , _ , \ { _ (cons _ _) () }
abst _ /\ atom _ = naw , _ , _ , \ { _ (abst _) () }
abst _ /\ cons _ _ = naw , _ , _ , \ { _ (abst _) () }

pullbackTerm : forall {G0 G1 G M d}
  (t0 : Term M G0 lib d)(th : G0 <= G)(t1 : Term M G1 lib d)(ph : G1 <= G) ->
  (t0 ^ th) == (t1 ^ ph) ->
  let G' , th' , ph' , ps' , _ = pullback th ph
  in Sg (Term M G' lib d) \ t' -> (t' ^ ps') == (t0 ^ th)
pullbackTerm t0 th t1 ph q01 with pullback th ph
... | G' , th' , ph' , ps' , c0 , c1 , u with support (t0 ^ th) 
... | G_ , t_ , ps , q , z = 
  let th0 , d0 = z t0 th refl
      ph1 , d1 = z t1 ph q01
      ps01 , e0 , e1 = u d0 d1
  in  (t_ ^ ps01) , 
      ((t_ ^ ps01) ^ ps')
        =[ thinco t_ ps01 ps' >=
      (t_ ^ (ps01 -< ps'))
        =[ (t_ ^_) $= (
         (ps01 -< ps') =[ (ps01 -<_) $= triDet c0 (mkTri th' th) >=
         (ps01 -< (th' -< th))
           =[ POLYTHIN.cocoC ps01 th' th  >=
         ((ps01 -< th') -< th)
           =[ (_-< th) $= triDet (mkTri ps01 th') e0 >=
         (th0 -< th)
           =[ triDet (mkTri th0 th) d0 >=
         ps [QED]) >=
      (t_ ^ ps) =< q ]=
      (t0 ^ th) [QED]

thickPat : forall {G' G N D}(t : Term N (D -+ G') lib chk) ->
  (th : G' <= G)(p : Pat G)(tz : (dom p) %[ N ! D ]) ->
  (t ^ (oi ^+ th)) == plug p tz ->
  Sg (Pat G') \ p' -> Sg ((dom p') %[ N ! D ]) \ tz' ->
  (p == (p' ^P th)) * (t == plug p' tz')
thickPat {G'}{G}{N}{D} t th (hole ph) ([] -, t') e with pullback (oi {S = D} ^+ th) (oi ^+ ph) | pullbackTerm t (oi ^+ th) t' (oi ^+ ph) e
... | _ , th' , ph' , ps' , a0 , a1 , u | t_ , b = {!hole th' , ? , ?!}
thickPat (! a) th (atom .a) tz refl = atom a , [] , refl , refl
thickPat (s & t) th (cons p q) tz e = {!!}
thickPat (\\ t) th (abst q) tz e = termNoConf e \ e -> termNoConf e \ e -> 
  let q' , tz' , a , b = thickPat t (th su) q tz e in abst q' , tz' , abst $= a , \\_ $= b 
thickPat (_ & _) th (atom a) tz ()
thickPat (\\ _) th (atom a) tz ()
thickPat (! a) th (cons p q) tz ()
thickPat (\\ _) th (cons p q) tz ()
thickPat (! a) th (abst q) tz ()
thickPat (_ & _) th (abst q) tz ()
thickPat (thnk _) th (atom a) tz ()
thickPat (_ ?- _) th (atom a) tz ()
thickPat (thnk _) th (cons p q) tz ()
thickPat (_ ?- _) th (cons p q) tz ()
thickPat (thnk _) th (abst p) tz ()
thickPat (_ ?- _) th (abst p) tz ()

hull : forall G {N D}(t : Term N (D -+ G) lib chk) ->
       Sg (Pat G) \ p -> Sg ((dom p) %[ N ! D ]) \ tz ->
       t == plug p tz * ((p' : Pat G) -> Match p' t -> p <P= p')
hull G (! a) = atom a , [] , refl ,
  \ { (atom a) ([] , refl) -> atom a
    ; (cons _ _) (tz' , ())
    ; (abst p') (tz' , ())
    ; (hole th) (([] -, t) , e) -> hole (atom a) refl
    }
hull G (s & t) with hull G s | hull G t
... | p , sz , pe , pf | q , tz , qe , qf =
  cons p q , (sz :+ tz) , sym (plugCons p q sz tz (sym pe) (sym qe)) ,
  \ { (atom a) (tz' , ())
  ; (cons p' q') (tz' , e) -> termNoConf e \ e -> termNoConf e \ se te ->
    cons (pf p' (lefts (dom p') (dom q') tz' , se))
         (qf q' (rights (dom p') (dom q') tz' , te))
  ; (abst p') (tz' , ())
  ; (hole th) (([] -, (! a)) , ())
  ; (hole th) (([] -, (s' & t')) , refl) -> {!!}
  ; (hole th) (([] -, (\\ u)) , ())
  ; (hole th) (([] -, thnk u) , ()) ; (hole th) (([] -, (_ ?- _)) , ()) }
hull G (\\ t) with hull (G -, <>) t
... | q , tz , qe , qf = abst q , {!!}
hull G (thnk _) = hole oi , {!!}
hull G (_ ?- _) = hole oi , {!!}
