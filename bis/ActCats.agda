module ActCats where

open import Basics
open import Eq
open import Cats
open import Bwd
open import Thin
open import Atom
open import Pat
open import Term
open import All


open module POLYTHIN {X} = Cat (OPE {X})
open module POLYSELECT {X P} = Concrete (Select {X}{P})

oiLemma : forall {X}{xz yz : Bwd X}(th : xz <= yz) ->
  (oi -< th) == (th -< oi)
oiLemma th = (oi -< th) =[ idcoC _ >= th =< coidC _ ]= (th -< oi) [QED]


module _ {A}(ACTA : Act A) where
  open Act ACTA

  record ActIden : Set where
    field
      ida : forall {G M} -> A (M , G) (M , G)
      idaWkn : forall {G M} ->
        ida {G -, <>}{M} == wkn ida
      idaHit : forall {G M}(i : <> <- G) ->
        hit i (ida {G}{M}) == essTo trg (vari i)
      idaMet : forall {G M X}(x : X <P- snd M) ez ->
        met x (ida {G}{M}) ez == (x ?- ez)
      idaMee : forall {G M}(x : <> <- fst M) ->
        mee x (ida {G}{M}) == essTo trg (mets x)

    open Cat (OPE {One})
    
    idaId : forall {M G d}(t : Term M G lib d) ->
      act t (ida {G}) == t
    idaCan : forall {M G}(k : Term M G ess chk) -> actk k (ida {G}) == k
    idaNeu : forall {M G}(n : Term M G ess syn) -> actn n (ida {G}) == essTo trg n
    idaz : forall {M G n}(ez : All (\ _ -> Term M G lib syn) n) ->
      actz ez ida == ez
    idaId {d = chk} (essl k) rewrite idaCan k = refl
    idaId {d = syn} (essl n) rewrite idaNeu n = toLibLemma trg syn n
    idaId (thnk n)   rewrite idaNeu n = toLibLemma trg chk n
    idaId (t :: T) rewrite idaId t | idaId T = refl
    idaId (x ?- ez) rewrite idaz ez = idaMet x ez
    idaCan (atom a)   = refl
    idaCan (cons s t) rewrite idaId s | idaId t = refl
    idaCan (abst t)   = abst $= (
      act t (wkn ida) =< act t $= idaWkn ]=
      act t ida =[ idaId t >= t [QED])
    idaNeu (vari i)   = idaHit i
    idaNeu (elim e s) rewrite idaId e | idaId s = refl
    idaNeu (mets x) = idaMee x
    idaz []        = refl
    idaz (ez -, e) rewrite idaz ez | idaId e = refl


module _ where
  open ActIden
  
  THINIDEN : ActIden THIN
  ida THINIDEN = refl , oi
  idaWkn THINIDEN = refl
  idaHit THINIDEN i = vari $= coidC _
  idaMet THINIDEN x ez = refl
  idaMee THINIDEN x = refl

  idsbHit : forall {M G}(i : <> <- G) -> project i (idsb {G}{M}) == (# i)
  idsbHit (i no) =
    top (select i (all (_^ (oi no)) idsb)) =[ top $= selectAll i (_^ (oi no)) idsb >=
    (top (select i idsb) ^ (oi no)) =[ (_^ (oi no)) $= idsbHit i >=
    (# i ^ (oi no)) =[ #_ $= (_no $= coidC _) >=
    # (i no) [QED]
  idsbHit (i su) rewrite oeU i oe = refl

  SBSTIDEN : ActIden SBST
  ida SBSTIDEN = refl , idsb
  idaWkn SBSTIDEN = refl
  idaHit SBSTIDEN i = idsbHit i
  idaMet SBSTIDEN x ez = refl
  idaMee SBSTIDEN x = refl



module _ {AF AB AC}(OAF : Act AF)(OAB : Act AB)(OAC : Act AC)
  where
  open Act
  record ActCompo : Set where
    field
      co : forall {MG0 MG1 MG2} -> AF MG0 MG1 -> AB MG1 MG2 -> AC MG0 MG2
      hitCo : forall {M0 G0 MG1 MG2}
        (i : <> <- G0)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2)
        -> act OAB (toLib (trg OAF) syn (hit OAF i f)) b ==
           toLib (trg OAC) syn (hit OAC i (co f b))
      metCo : forall {M0 G0 M1 G1 MG2 X}
        (x : X <P- snd M0)(ez : All (\ _ -> Term M1 G1 lib syn) X)
        (f : AF (M0 , G0) (M1 , G1))(b : AB (M1 , G1) MG2)
        -> act OAB (met OAF x f ez) b == met OAC x (co f b) (actz OAB ez b)
      wknCo : forall {MG0 MG1 MG2}(f : AF MG0 MG1)(b : AB MG1 MG2)
        -> co (wkn OAF f) (wkn OAB b) == wkn OAC (co f b)
      meeCo : forall {M0 G0 MG1 MG2}
        (x : <> <- fst M0)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2)
        -> act OAB (toLib (trg OAF) syn (mee OAF x f)) b ==
           toLib (trg OAC) syn (mee OAC x (co f b))
    coLib : forall {M0 G0 MG1 MG2 d}
      (t : Term M0 G0 lib d)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2) ->
            act OAB (act OAF t f) b == act OAC t (co f b)
    coCan : forall {M0 G0 MG1 MG2}
      (k : Term M0 G0 ess chk)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2) ->
            actk OAB (actk OAF k f) b == actk OAC k (co f b)
    coNeu : forall {M0 G0 MG1 MG2}
      (n : Term M0 G0 ess syn)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2) ->
            act OAB (toLib (trg OAF) syn (actn OAF n f)) b
            == toLib (trg OAC) syn (actn OAC n (co f b))
    coz : forall {M0 G0 MG1 MG2 X}(ez : All (\ _ -> Term M0 G0 lib syn) X)
            (f : AF (M0 , G0) MG1)(b : AB MG1 MG2) ->
            actz OAB (actz OAF ez f) b == actz OAC ez (co f b)
    coLib {d = chk} (essl k)   f b rewrite coCan k f b = refl
    coLib {d = syn} (essl n)   f b = coNeu n f b
    coLib           (thnk n)   f b
      rewrite trgLemma (trg OAF) (actn OAF n f)
            | trgLemma (trg OAC) (actn OAC n (co f b))
            | actThunk OAB (toLib (trg OAF) syn (actn OAF n f)) b
            = [_] $= coNeu n f b
    coLib           (t :: T) f b rewrite coLib t f b | coLib T f b = refl
    coLib (x ?- ez) f b rewrite metCo x (actz OAF ez f) f b | coz ez f b = refl
    coCan (atom a)    f b = refl
    coCan (cons s t)  f b rewrite coLib s f b | coLib t f b = refl
    coCan (abst t)    f b rewrite coLib t (wkn OAF f) (wkn OAB b) | wknCo f b = refl
    coNeu (vari i)   f b = hitCo i f b
    coNeu (elim e s) f b
      rewrite toLibLemma (trg OAF) syn (elim (act OAF e f) (act OAF s f))
            | toLibLemma (trg OAB) syn
                (elim (act OAB (act OAF e f) b) (act OAB (act OAF s f) b))
            | toLibLemma (trg OAC) syn (elim (act OAC e (co f b)) (act OAC s (co f b)))
            | coLib e f b | coLib s f b
            = refl
    coNeu (mets x)   f b = meeCo x f b
    coz []        f b = refl
    coz (ez -, e) f b rewrite coz ez f b | coLib e f b = refl


module _ {F B C : Meta -> Nat -> Nat -> Set}{fl bl cl}
  (of : forall {N} -> ObjAct fl N (F N))
  (ob : forall {N} -> ObjAct bl N (B N))
  (oc : forall {N} -> ObjAct cl N (C N))
  where
  open Act
  open ActCompo
  open POLYOBJACT

  record ObjComp : Set where
    field
      coOb : forall {M G0 G1 G2} ->
        F M G0 G1 -> B M G1 G2 -> C M G0 G2
      hitOb : forall {M G0 G1 G2}(i : <> <- G0)(f : F M G0 G1)(b : B M G1 G2) ->
        act (objAct _ ob) (toLib fl syn (objHit _ of i f)) (refl , b) ==
        toLib cl syn (objHit _ oc i (coOb f b))
      wknOb : forall {M G0 G1 G2}(f : F M G0 G1)(b : B M G1 G2) ->
          coOb (objWkn _ of f) (objWkn _ ob b) == objWkn _ oc (coOb f b)

    objAComp : ActCompo (objAct _ of) (objAct _ ob) (objAct _ oc)
    co objAComp (refl , f) (refl , b) = refl , coOb f b
    hitCo objAComp i (refl , f) (refl , b) = hitOb i f b
    metCo objAComp x ez (refl , f) (refl , b) = refl
    wknCo objAComp (refl , f) (refl , b) = (refl ,_) $= wknOb f b
    meeCo objAComp {MG2 = M , G2} x (refl , f) (refl , b)
      = act (objAct B ob) (toLib fl syn (essTo fl (mets x))) (refl , b)
          =[ act (objAct B ob) $= toLibLemma fl _ _ =$= refl >=
        toLib bl syn (essTo bl (mets x))
          =[ toLibLemma bl _ _ >=
        essl (mets x)
          =< toLibLemma cl _ _ ]=
        toLib cl syn (essTo cl (mets x))
          [QED]

module _ {A B C D E}
         {ACTA : Act A}{ACTB : Act B}{ACTC : Act C}
         {ACTD : Act D}{ACTE : Act E}
         (ABC : ActCompo ACTA ACTB ACTC)(DEC : ActCompo ACTD ACTE ACTC)
  where
  open Act
  open ActCompo

  pointCompo : forall {M0 G0 MG1 MG2 MG3}
    (a : A (M0 , G0) MG1)(b : B MG1 MG3)(d : D (M0 , G0) MG2)(e : E MG2 MG3)
    {z}(t : Term M0 G0 lib z) ->
    (co ABC a b == co DEC d e) ->
    act ACTB (act ACTA t a) b == act ACTE (act ACTD t d) e
  pointCompo a b d e t q =
    act ACTB (act ACTA t a) b =[ coLib ABC t a b >=
    act ACTC t (co ABC a b) =[ act ACTC t $= q >=
    act ACTC t (co DEC d e) =< coLib DEC t d e ]=
    act ACTE (act ACTD t d) e [QED]
  
  icompoLemma : forall {I}{M0 M1 M2 M3 : Meta}{G0 G1 G2 G3 : I -> Nat}
    (a : {i : I} -> A (M0 , G0 i) (M1 , G1 i))
    (b : {i : I} -> B (M1 , G1 i) (M3 , G3 i))
    (d : {i : I} -> D (M0 , G0 i) (M2 , G2 i))
    (e : {i : I} -> E (M2 , G2 i) (M3 , G3 i)) ->
    (q : {i : I} -> co ABC (a {i}) (b {i}) == co DEC (d {i}) (e {i})) ->
    forall {z}{X : Bwd I}(tz : All (\ i -> Term M0 (G0 i) lib z) X) ->
    all (\ t -> act ACTB t b) (all (\ t -> act ACTA t a) tz) ==
    all (\ t -> act ACTE t e) (all (\ t -> act ACTD t d) tz)
  icompoLemma a b d e q tz = 
    all (\ t -> act ACTB t b) (all (\ t -> act ACTA t a) tz)
      =< allCo _ _ _ (\ _ -> refl) _ ]=
    all (\ t -> act ACTB (act ACTA t a) b) tz
      =[ allCo _ _ _ (\ t -> pointCompo a b d e t q) _ >=
    all (\ t -> act ACTE t e) (all (\ t -> act ACTD t d) tz) [QED]



module _ where
  open ObjComp
  OBJTHINTHINTHIN : ObjComp OBJTHIN OBJTHIN OBJTHIN
  coOb OBJTHINTHINTHIN = _-<_
  hitOb OBJTHINTHINTHIN i f b = #_ $= sym (cocoC i f b)
  wknOb OBJTHINTHINTHIN f b = refl

  THINTHINTHIN = objAComp OBJTHINTHINTHIN

  thinco : forall {M G0 G1 G2 d}(t : Term M G0 lib d)(th : G0 <= G1)(ph : G1 <= G2) ->
    ((t ^ th) ^ ph) == t ^ (th -< ph)
  thinco t th ph = coLib t (refl , th) (refl , ph)
    where open ActCompo THINTHINTHIN

  OBJTHINSBSTSBST : ObjComp OBJTHIN OBJSBST OBJSBST
  coOb OBJTHINSBSTSBST = select
  hitOb OBJTHINSBSTSBST i th sg = top $= funCo th i sg
  wknOb OBJTHINSBSTSBST th sg = (_-, _) $= selectAll th (_^ (oi no)) sg

  THINSBSTSBST = objAComp OBJTHINSBSTSBST

module _ {M : Meta} where

  selIdsb : forall {G D}(th : G <= D) ->
    select th (idsb {D}{M}) == all (_^ th) (idsb {G}{M})
  selIdsb (th no) = 
    select th (all (_^ (oi no)) idsb)
      =[ selectAll th _ idsb >=
    all (_^ (oi no)) (select th idsb)
      =[ all (_^ (oi no)) $= selIdsb th >=
    all (_^ (oi no)) (all (_^ th) idsb)
      =< allCo _ _ _ (\ t -> 
        t ^ (th no)
          =< (t ^_) $= (_no $= coidC _) ]=
        t ^ ((th -< oi) no)
          =< thinco t th (oi no) ]=
        (t ^ th) ^ (oi no)
          [QED]) idsb ]=
    all (_^ (th no)) idsb
      [QED]
  selIdsb (th su) = _-,_ $= (
    select th (all (_^ (oi no)) idsb)
      =[ selectAll th _ idsb >=
    all (_^ (oi no)) (select th idsb)
      =[ all (_^ (oi no)) $= selIdsb th >=
    all (_^ (oi no)) (all (_^ th) idsb)
      =< icompoLemma THINTHINTHIN THINTHINTHIN _ _ _ _
          ((refl ,_) $= (_no $= oiLemma th)) idsb ]=
    all (_^ (th su)) (all (_^ (oi no)) idsb)
      [QED]
      ) =$= (#_ $= (_su $= oeU _ _))
  selIdsb ze = refl

{-
module _ {M : Meta} where
  open ActIden THINIDEN

  leftIdsb : forall G D ->
    lefts G D (idsb {G -+ D}{M}) == all (_^ thinl oi D) (idsb {G}{M})
  leftIdsb G [] = 
    select oi idsb =[ funId _ >=
    idsb =< allId _ idaId idsb ]=
    all (_^ oi {S = G}) idsb [QED]
  leftIdsb G (D -, <>) = 
    lefts G D (all (_^ (oi no)) idsb)
      =[ selectAll (thinl oi D) _ idsb >=
    all (_^ (oi no)) (lefts G D idsb)
      =[ all (_^ (oi no)) $= leftIdsb G D >=
    all (_^ (oi no)) (all (_^ thinl oi D) (idsb {G}))
      =< allCo _ _ _ (\ t -> 
        t ^ (thinl oi D no)
          =< (t ^_) $= (_no $= coidC _) ]=
        t ^ ((thinl oi D -< oi) no)
          =< thinco t (thinl oi D) (oi no) ]=
        (t ^ thinl oi D) ^ (oi no)
          [QED]) (idsb {G}) ]=
    all (_^ (thinl oi D no)) (idsb {G})
      [QED]
-}

module _ {A : Meta -> Nat -> Nat -> Set}{l}(OA : forall {N} -> ObjAct l N (A N)) where
  open module POLYA {N} = ObjAct (OA {N})
  open ObjComp
  open Act

  record SbstThen : Set where
    field
      hitZero : forall {M G D}(al : A M G D) ->
        toLib l syn (objHit (oe su) (objWkn al)) == # (oe su)
      thinThen  : ObjComp OBJTHIN OA OA
      thenThin  : ObjComp OA OBJTHIN OA
      wknThin : forall {M G D}(al : A M G D) ->
        coOb thinThen (oi no) (objWkn al) == coOb thenThin al (oi no)
        
    compSbst : ObjComp OBJSBST OA OBJSBST
    coOb compSbst sg al = all (\ t -> act (objAct _ OA) t (refl , al)) sg
    hitOb compSbst i sg al = sym (top $= selectAll i _ sg)
    wknOb compSbst sg al = _-,_
      $= icompoLemma (objAComp thinThen) (objAComp thenThin) _ _ _ _
            ((refl ,_) $= wknThin al)
            sg
      =$= hitZero al

module _ where
  open SbstThen
  open ObjComp

  SBSTTHENTHIN : SbstThen OBJTHIN
  hitZero SBSTTHENTHIN th = #_ $= (_su $= oeU _ _)
  thinThen SBSTTHENTHIN = OBJTHINTHINTHIN
  thenThin SBSTTHENTHIN = OBJTHINTHINTHIN
  wknThin SBSTTHENTHIN th = _no $= oiLemma th

  OBJSBSTTHINSBST = compSbst SBSTTHENTHIN
  SBSTTHINSBST = objAComp OBJSBSTTHINSBST

  SBSTTHENSBST : SbstThen OBJSBST
  hitZero SBSTTHENSBST sg = refl
  thinThen  SBSTTHENSBST = OBJTHINSBSTSBST
  thenThin  SBSTTHENSBST = OBJSBSTTHINSBST
  wknThin SBSTTHENSBST sg = funId _

  OBJSBSTSBSTSBST = compSbst SBSTTHENSBST
  SBSTSBSTSBST = objAComp OBJSBSTSBSTSBST

module _ {M : Meta} where
  open Concrete
  open ActIden THINIDEN
  open ActCompo THINTHINTHIN

  THINFUN : forall {l d} -> Concrete (OPE {One}) \ G -> Term M G l d
  fun THINFUN th t = t ^ th
  funId (THINFUN {ess} {chk}) t = idaCan t
  funId (THINFUN {ess} {syn}) t = idaNeu t
  funId (THINFUN {lib}) t = idaId t
  funCo (THINFUN {ess} {chk}) th ph t = sym (coCan t (refl , th) (refl , ph))
  funCo (THINFUN {ess} {syn}) th ph t =
    termNoConf (coNeu t (refl , th) (refl , ph)) \ e -> sym e
  funCo (THINFUN {lib}) th ph t = sym (thinco t th ph)


module _ {M : Meta} where
  open ActCompo THINSBSTSBST
  
  coidsb : forall {G D}(sg : [ M ! G ]/ D) ->
    all (_/ sg) idsb == sg
  coidsb [] = refl
  coidsb (sg -, e) = (_-, _) $= (
      all (_/ (sg -, e)) (all (_^ (oi no)) idsb)
        =< allCo _ _ _ (\ t -> 
          (t / sg)
            =< (t /_) $= funId _ ]=
          (t / select oi sg)
            =< coLib t _ _ ]=
          ((t ^ (oi no)) / (sg -, e))
            [QED]
         ) idsb ]=
      all (_/ sg) idsb
        =[ coidsb sg >=
      sg
        [QED])


module _ {M : Meta} where
  open ActIden SBSTIDEN
  open ObjComp OBJSBSTSBSTSBST
  open ActCompo SBSTSBSTSBST
  open Concrete

  SUBSTITUTION : Cat Nat \ G D -> [ M ! G ]/ D
  Cat.idC SUBSTITUTION = idsb
  Cat.coC SUBSTITUTION = coOb
  Cat.idcoC SUBSTITUTION = coidsb
  Cat.coidC SUBSTITUTION = allId _ idaId 
  Cat.cocoC SUBSTITUTION sg0 sg1 sg2 =
    allCo _ _ _ (\ t -> sym (coLib t (refl , sg1) (refl , sg2))) sg0

  SBSTFUN : forall {d} -> Concrete SUBSTITUTION \ G -> Term M G lib d
  fun SBSTFUN sg t = t / sg
  funId SBSTFUN = idaId
  funCo SBSTFUN sg0 sg1 t = sym (coLib t (refl , sg0) (refl , sg1))


module PLUGACT {M N : Meta}{A}(ACTA : Act A)
  (THINACTA : ActCompo THIN ACTA ACTA)(ACTATHIN : ActCompo ACTA THIN ACTA)
  (fact : forall {de de'} de0 ga (al : A (M , de) (N , de'))(th : de0 <= ga) ->
    ActCompo.co THINACTA (refl , (oi ^+ th)) (Act.wkns ACTA al ga) ==
    ActCompo.co ACTATHIN (Act.wkns ACTA al de0) (refl , (oi ^+ th)))
  where
  open Act ACTA
  open ActCompo

  plugActLemma : forall {ga de de'}
    (p : Pat ga)(ts : Env M (de ,P p))(al : A (M , de) (N , de')) ->
    (act (p %P ts) (wkns al ga)) == (p %P acte ts al)
  plugActLemma (atom a) (atom .a) al = refl
  plugActLemma (cons p q) (cons ss ts) al =
    _&_ $= plugActLemma p ss al =$= plugActLemma q ts al
  plugActLemma (abst p) (abst ts) al = \\_ $= plugActLemma p ts al
  plugActLemma {ga}{de}{de'}(hole {de0} th) (hole t) al =
    act (t ^ (oi ^+ th)) (wkns al ga)
      =[ coLib THINACTA t (refl , oi ^+ th) (wkns al ga) >=
    act t (co THINACTA (refl , (oi ^+ th)) (wkns al ga))
      =[ act t $= fact _ _ al th >=
    act t (co ACTATHIN (wkns al de0) (refl , (oi ^+ th)))
      =< coLib ACTATHIN t (wkns al de0) (refl , (oi ^+ th)) ]=
    act t (wkns al de0) ^ (oi ^+ th)
      [QED]
  
module _ {M : Meta} where

  open ObjAct (OBJTHIN {M})
  open Act THIN
  open ActCompo THINTHINTHIN

  thinWknsFact : {de de' de0 ga : Bwd One}
      (ph : de <= de')
      (th : de0 <= ga) ->
      ((oi ^+ th) -< objWkns ph ga)
      ==
      (objWkns ph de0 -< (oi ^+ th))
  thinWknsFact ph (th no) = _no $= thinWknsFact ph th
  thinWknsFact ph (th su) = _su $= thinWknsFact ph th
  thinWknsFact ph ze      = oiLemma ph

  open PLUGACT {M}{M} THIN THINTHINTHIN THINTHINTHIN
    (\ { de0 ga (refl , ph) th -> 
      co (refl , (oi ^+ th)) (wkns (refl , ph) ga)
        =[ co (refl , (oi ^+ th)) $= objWknsLemma _ OBJTHIN ph ga >=
      (refl , ((oi ^+ th) -< objWkns ph ga))
        =[ (refl ,_) $= thinWknsFact ph th >=
      (refl , objWkns ph de0 -< (oi ^+ th))
        =< co $= objWknsLemma _ OBJTHIN ph de0 =$ (refl , (oi ^+ th)) ]=
      co (wkns (refl , ph) de0) (refl , (oi ^+ th))
        [QED] })

  plugThinLemma = plugActLemma

module _ {M N : Meta} where
  
  open ObjAct (OBJTHIN {N})
  open Act THIN

  instThinLemma : forall {d ga ga'}
    (t : Term M ga lib d) ->
    Pi (Inst (M , ga) (N , ga')) \
      { (de , refl , sg , ts) -> 
      forall {de'}(th : de <= de') ->
    ((t % (sg , ts)) ^ objWkns th ga) ==
      (t % (all (_^ th) sg , acte ts (refl , th))) }
  instThinLemman : forall {ga ga'}
    (t : Term M ga ess syn) ->
    Pi (Inst (M , ga) (N , ga')) \
      { (de , refl , sg , ts) -> 
      forall {de'}(th : de <= de') ->
    ((Act.actn INST t (_ , refl , sg , ts)) ^ objWkns th ga) ==
      (Act.actn INST t (_ , refl , all (_^ th) sg , acte ts (refl , th))) }
  instThinLemmaz : forall {ga ga'}{X : Nat}
    (ez : All (\ _ -> Term M ga lib syn) X) ->
    Pi (Inst (M , ga) (N , ga')) \
      { (de , refl , sg , ts) -> 
      forall {de'}(th : de <= de') ->
    (all (_^ (th ^+ oi {S = ga})) (Act.actz INST ez (de , refl , sg , ts))) ==
     Act.actz INST ez (de' , refl , all (_^ th) sg , acte ts (refl , th)) }
  instThinLemma {syn} (essl n) (de , refl , sg , ts) th
    rewrite instThinLemman n (de , refl , sg , ts) th = refl
  instThinLemma (! a) (de , refl , sg , ts) th = refl
  instThinLemma (s & t) (de , refl , sg , ts) th
    rewrite instThinLemma s (de , refl , sg , ts) th
          | instThinLemma t (de , refl , sg , ts) th
          = refl
  instThinLemma (\\ t) (de , refl , sg , ts) th
    rewrite instThinLemma t (de , refl , sg , ts) th = refl
  instThinLemma {ga = ga} (thnk n) (de , refl , sg , ts) th
    rewrite thinThunkLemma (Act.actn INST n (de , refl , sg , ts)) (objWkns th ga)
          | instThinLemman n (de , refl , sg , ts) th
          = refl
  instThinLemma (t :: T) (de , refl , sg , ts) th
    rewrite instThinLemma t (de , refl , sg , ts) th
          | instThinLemma T (de , refl , sg , ts) th
          = refl
  instThinLemma {ga = ga} (_?-_ {D} x ez) (de , refl , sg , ts) {de'} th
    rewrite projeActe x ts (refl , th)
          | objWknsLemma _ OBJTHIN {M = N} th D
          | thinWknsLemma {N} th ga
          | thinWknsLemma {N} th D
    = pointCompo SBSTTHINSBST THINSBSTSBST _ _ _ _ (proje de x ts)
       ((refl ,_) $= (
         all (_^ (th ^+ oi {S = ga}))
           (lefts de ga idsb :+ Act.actz INST ez (de , refl , sg , ts))
           =[ allCat _ {yz = D} _ _ >=
         all (_^ (th ^+ oi {S = ga})) (lefts de ga idsb) :+
         all (_^ (th ^+ oi {S = ga})) (Act.actz INST ez (de , refl , sg , ts))
           =[ _:+_
             $=
             (all (_^ (th ^+ oi {S = ga})) (lefts de ga idsb)
                =< selectAll (thinl oi ga) _ _ ]=
              select (thinl oi ga) (all (_^ (th ^+ oi {S = ga})) idsb)
                =< select (thinl oi ga) $= selIdsb (th ^+ oi {S = ga}) ]=
              select (thinl oi ga) (select (th ^+ oi {S = ga}) idsb)
                =< funCo (th ^+ oi {S = ga}) (thinl oi ga) idsb ]=
              select (thinl oi ga -< (th ^+ oi {S = ga})) idsb
                =[ select
                   $= (thinl oi ga -< (th ^+ oi {S = ga})
                         =[ moco oi th oe (oi {S = ga}) >=
                       (oi -< th) ^+ (oe -< oi {S = ga})
                         =[ _^+_ $= idcoC th =$= oeU _ _ >=
                       thinl th ga [QED]) =$ idsb >=
              select (thinl th ga) idsb
                =[ select $= (
                  thinl th ga =< thinl $= coidC _ =$ ga ]=
                  thinl (th -< oi) ga =< thinlLeft th oi ga ]=
                  (th -< thinl oi ga) [QED]) =$ idsb >=
              select (th -< thinl oi ga) idsb
                =[ funCo (thinl oi ga) th idsb >=
              select th (lefts de' ga idsb)
                [QED])
             =$=
              (all (_^ (th ^+ oi {S = ga}))
                (Act.actz INST ez (de , refl , sg , ts))
                =[ instThinLemmaz ez (de , refl , sg , ts) th >=
               Act.actz INST ez (_ , refl , all (_^ th) sg , acte ts (refl , th))
                =< funId _ ]=
               select oi
                (Act.actz INST ez (_ , refl , all (_^ th) sg , acte ts (refl , th)))
                 [QED]) >=
         select th (lefts de' ga idsb) :+
         select oi (Act.actz INST ez (_ , refl , all (_^ th) sg , acte ts (refl , th)))
           =< selCat th oi _ _ ]=
         select (th ^+ oi {S = D})
           (lefts de' ga idsb :+
            Act.actz INST ez (_ , refl , all (_^ th) sg , acte ts (refl , th)))
           [QED]
         ))
  instThinLemman {ga = ga} (vari i) (de , refl , sg , ts) {de'} th =  #_ $= (
    ((i -< thinr de oi) -< objWkns th ga)
      =[ (_ -<_) $= thinWknsLemma th ga >=
    ((i -< thinr de oi) -< (th ^+ oi {S = ga}))
      =< cocoC i (thinr de oi) (th ^+ oi {S = ga}) ]=
    (i -< (thinr de oi -< (th ^+ oi {S = ga})))
      =[ (i -<_) $= ( (thinr de oi -< (th ^+ oi {S = ga}))
                        =[ thinrLemma oi th oi >=
                       thinr de' (oi -< oi)
                        =[ thinr de' $= idcoC oi >=
                       thinr de' oi
                         [QED]) >= 
    (i -< thinr de' oi)
      [QED])
  instThinLemman (elim e s) (de , refl , sg , ts) th
    rewrite instThinLemma e (de , refl , sg , ts) th
          | instThinLemma s (de , refl , sg , ts) th
          = refl
  instThinLemman {ga = ga} (mets x) (de , refl , sg , ts) th =
    ((project x sg ^ thinl oi ga) ^ objWkns th ga)
      =[ pointCompo THINTHINTHIN THINTHINTHIN _ _ _ _ (project x sg)
        ((refl ,_) $= (
           (thinl oi ga -< objWkns th ga)
              =[ (thinl oi ga -<_) $= thinWknsLemma th ga >=
           (thinl oi ga -< (th ^+ oi {S = ga}))
              =[ moco oi th oe (oi {S = ga}) >=
           ((oi -< th) ^+ (oe -< oi {S = ga}))
              =[ _^+_ $= oiLemma th =$= oeU _ _ >=
           thinl (th -< oi) ga
              =< thinlLeft th oi ga ]=
           (th -< thinl oi ga)
              [QED])) >=
    ((project x sg ^ th) ^ thinl oi ga)
      =< (_^ thinl oi ga) $= (top $= selectAll x (_^ th) sg) ]=
    (project x (all (_^ th) sg) ^ thinl oi ga)
      [QED]
  instThinLemmaz [] (de , refl , sg , ts) th = refl
  instThinLemmaz {ga = ga} (ez -, e) (de , refl , sg , ts) th
    rewrite instThinLemmaz ez (de , refl , sg , ts) th
          | sym (thinWknsLemma {N} th ga)
          | instThinLemma e (de , refl , sg , ts) th
          = refl

