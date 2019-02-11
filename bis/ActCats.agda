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


module _ where

  open ActWeak

  _>/<_ : forall {M G0 D0 G1 D1} ->
    [ M ! G0 ]/ D0 -> [ M ! G1 ]/ D1 ->
    [ M ! (G0 -+ G1) ]/ (D0 -+ D1)
  _>/<_ {M}{G0}{D0}{G1}{D1} sg0  sg1 =
    all (_^ thinl oi D1) sg0 :+ all (_^ thinr D0 oi) sg1

  SBSTWEAK : ActWeak _ OBJSBST
  wks SBSTWEAK {D = D} sg X = sg >/< idsb {X}
  wks1 SBSTWEAK {D = D} sg X = _-,_
    $= (all (_^ (oi no)) (all (_^ thinl oi X) sg :+ all (_^ thinr D oi) idsb)
          =[ allCat _ (all _ sg) (all _ (idsb {X})) >=
        all (_^ (oi no)) (all (_^ thinl oi X) sg) :+
        all (_^ (oi no)) (all (_^ thinr D oi) (idsb {X}))
          =< _:+_
            $= allCo _ _ _ (\ t -> 
               t ^ (thinl oi X no)
                 =< (t ^_) $= (_no $= coidC _) ]=
               t ^ ((thinl oi X -< oi) no)
                 =< thinco t _ _ ]=
               (t ^ thinl oi X) ^ (oi no)
                 [QED]) sg
            =$= icompoLemma THINTHINTHIN THINTHINTHIN _ _ _ _
              ((refl ,_) $= (_no $= oiLemma _)) (idsb {X}) ]=
        all (_^ (thinl oi X no)) sg :+
        all (_^ (thinr D oi su)) (all (_^ (oi no)) idsb)
          [QED])
    =$= (#_ $= (_su $= oeU _ _))
    
  _/E_ : forall {M}{p : Pat []}{G D} ->
    Env M (G ,P p) -> [ M ! G ]/ D -> Env M (D ,P p)
  om /E sg = acte SBSTWEAK om sg

  open Monoidal

  MONSBST : forall {M} -> Monoidal (MonoidBwd One) (SUBSTITUTION {M})
  _><_ MONSBST = _>/<_
  moid MONSBST S S' = 
    all (_^ thinl oi S') (idsb {S}) :+ all (_^ thinr S oi) (idsb {S'})
      =< _:+_ $= selIdsb (thinl oi S') =$= selIdsb (thinr S oi)  ]=
    select (thinl oi S') (idsb {S -+ S'}) :+ select (thinr S oi) (idsb {S -+ S'})
      =< split S S' (idsb {S -+ S'}) ]=
    idsb {S -+ S'}
      [QED]
  moco MONSBST {R}{R'}{S}{S'}{T}{T'} rh0 sg0 rh1 sg1 = 
    all (_/ (rh1 >/< sg1)) (rh0 >/< sg0)
      =[ allCat (_/ (rh1 >/< sg1)) (all _ rh0) (all _ sg0) >=
    all (_/ (rh1 >/< sg1)) (all (_^ thinl oi S') rh0) :+
    all (_/ (rh1 >/< sg1)) (all (_^ thinr S oi) sg0)
      =[ _:+_ $= icompoLemma THINSBSTSBST SBSTTHINSBST _ _ _ _
         ((refl ,_) $= (lefts S S' (rh1 >/< sg1)
               =[ leftis (all _ rh1) (all _ sg1) >=
               all (_^ thinl oi T') rh1
                 [QED])) rh0
             =$= icompoLemma THINSBSTSBST SBSTTHINSBST _ _ _ _
         ((refl ,_) $= (rights S S' (rh1 >/< sg1)
               =[ rightis (all _ rh1) (all _ sg1) >=
              all (_^ thinr T oi) sg1
                [QED])) sg0 >=
    all (_/ rh1) rh0 >/< all (_/ sg1) sg0
      [QED]
  {-
  lunitor MONSBST = {!!}
  runitor MONSBST = {!!}
  associator MONSBST = {!!}
  -}

module _ {l}{A : Meta -> Nat -> Nat -> Set}
            {o : forall {M} -> ObjAct l M (A M)}
            (st : SbstThen o)(ASS : ObjComp o OBJSBST OBJSBST)
            (TAA : ObjComp OBJTHIN o o)(ATA : ObjComp o OBJTHIN o)
            (ACTW : ActWeak _ o) where
  
  open Act (objAct _ o)
  open ActWeak ACTW
  module _ where
    open SbstThen st
    open ObjComp compSbst
    open ActCompo objAComp
    sas = coLib
  module _ where
    open ObjComp ASS
    open ActCompo objAComp
    as = coOb
    ass = coLib
  module _ where
    open ObjComp TAA
    open ActCompo objAComp
    ta = coOb
    taa = coLib
  module _ where
    open ObjComp ATA
    open ActCompo objAComp
    at = coOb
    ata = coLib
  ian = Act.actn INST
  iaz = Act.actz INST
  
  module PLUGINSTACT
    (nilFact : forall {M de de'}(al : A M de de') -> wks al [] == al)
    (thinFact : forall {M de de'} de0 ga (al : A M de de')(th : de0 <= ga) ->
      ta (oi ^+ th) (wks al ga) == at (wks al de0) (oi ^+ th))
    (hitFact : forall {M de de'}(al : A M de de') ga (i : <> <- ga) ->
      toLib l syn (ObjAct.objHit o (i -< thinr de oi) (wks al ga))
        == # (i -< thinr de' oi))
    (M : Meta)
    where
  
    plugActLemma : forall {ga de de'}
      (p : Pat ga)(ts : Env M (de ,P p))(al : A M de de') ->
      (act (p %P ts) (refl , wks al ga)) == (p %P acte ts al)
    plugActLemma (atom a)   (atom .a)    al = refl
    plugActLemma (cons p q) (cons ss ts) al
      rewrite plugActLemma p ss al | plugActLemma q ts al = refl
    plugActLemma {ga} (abst q)   (abst ts)    al
      rewrite wks1 al ga | plugActLemma q ts al = refl
    plugActLemma {ga}{de}{de'} (hole {de0} th)  (hole t)     al = 
      act (t ^ (oi ^+ th)) (refl , wks al ga)
        =[ taa t (refl , oi ^+ th) (refl , wks al ga) >=
      act t (refl , ta (oi ^+ th) (wks al ga))
        =[ act t $= ((refl ,_) $= thinFact de0 ga al th) >=
      act t (refl , at (wks al de0) (oi ^+ th))
        =< ata t (refl , wks al de0) (refl , oi ^+ th) ]=
      act t (refl , wks al de0) ^ (oi ^+ th)
      [QED]

    plugActLemma0 : forall {de de'} ->
      (p : Pat [])(ts : Env M (de ,P p))(al : A M de de') ->
      (act (p %P ts) (refl , al)) == (p %P acte ts al)
    plugActLemma0 p ts al
      rewrite sym (plugActLemma p ts al) | nilFact al = refl
      
    module INSTACT {N : Meta}
        (sbstFact : forall {de de'} de0 ga (al : A N de de')
        (ez : All (\ _ -> Term N (de' -+ ga) lib syn) de0) ->
        as (wks al de0) (all (_^ thinl oi ga) idsb :+ ez) ==
        (all (\ t -> act t (refl , ta (thinl oi ga) (wks al ga))) idsb :+ ez) ) 

      where
      instActLemma : forall {d ga ga'}
        (t : Term M ga lib d)
        (sg : [ N ! fst M ]/ ga')(ts : Env N (ga' ,P snd M)) ->
        forall {de'}(al : A N ga' de') ->
        act (t % (sg , ts)) (refl , wks al ga) ==
          (t % (all (\ t -> act t (refl , al)) sg , acte ts al))
      instActLemman : forall {ga ga'}
        (t : Term M ga ess syn)
        (sg : [ N ! fst M ]/ ga')(ts : Env N (ga' ,P snd M)) ->
        forall {de'}(al : A N ga' de') ->
        act (ian t (_ , refl , sg , ts)) (refl , wks al ga) ==
          ian t (_ , refl , all (\ t -> act t (refl , al)) sg , acte ts al)
      instActLemmaz : forall {ga ga' X}
        (ez : All (\ _ -> Term M ga lib syn) X)
        (sg : [ N ! fst M ]/ ga')(ts : Env N (ga' ,P snd M)) ->
        forall {de'}(al : A N ga' de') ->
        (all (\ t -> act t (refl , wks al ga)) (iaz ez (_ , refl , sg , ts))) ==
        iaz ez (_ , refl , all (\ t -> act t (refl , al)) sg , acte ts al)
      instActLemma {syn} (essl n) sg ts al rewrite instActLemman n sg ts al = refl
      instActLemma {chk} (! a) sg ts al = refl
      instActLemma {chk} (s & t) sg ts al
        rewrite instActLemma s sg ts al | instActLemma t sg ts al = refl
      instActLemma {chk} {ga} (\\ t) sg ts al
        rewrite wks1 al ga | instActLemma t sg ts al = refl
      instActLemma {ga = ga} (thnk n) sg ts al
        rewrite actThunk (ian n (_ , refl , sg , ts)) (refl , wks al ga)
              | instActLemman n sg ts al
              = refl
      instActLemma (t :: T) sg ts al
        rewrite instActLemma t sg ts al | instActLemma T sg ts al = refl
      instActLemma {ga = ga} {ga'} (_?-_ {de0} x ez) sg ts {de'} al =
        act (proje ga' x ts /
               (all (_^ thinl oi ga) idsb :+ iaz ez (_ , refl , sg , ts)))
          (refl , wks al ga)
          =[ sas (proje ga' x ts) _ _ >=
        proje ga' x ts / all (\ t -> act t (refl , wks al ga))
               (all (_^ thinl oi ga) idsb :+ iaz ez (_ , refl , sg , ts))
          =[ (proje ga' x ts /_) $= ( 
            all (\ t -> act t (refl , wks al ga))
               (all (_^ thinl oi ga) idsb :+ iaz ez (_ , refl , sg , ts))
              =[ allCat _ _ (iaz ez _) >=
            (all (\ t -> act t (refl , wks al ga)) (all (_^ thinl oi ga) idsb) :+
                all (\ t -> act t (refl , wks al ga)) (iaz ez (_ , refl , sg , ts)))
              =[ _:+_ $= sym (allCo _ _ _ (\ t -> sym (taa t _ _)) idsb)
                 =$= instActLemmaz ez sg ts al >=
            (all (\ t -> act t (refl , ta (thinl oi ga) (wks al ga))) idsb :+
              iaz ez (_ , refl , all (\ t -> act t (refl , al)) sg , acte ts al))
              =< sbstFact de0 ga al _ ]=
            (as (wks al de0)
             (all (_^ thinl oi ga) idsb :+
              iaz ez (de' , refl , all (\ t -> act t (refl , al)) sg , acte ts al)))
              [QED]
          ) >=
        proje ga' x ts /
          (as (wks al de0)
           (all (_^ thinl oi ga) idsb
            :+ iaz ez (de' , refl , all (\ t -> act t (refl , al)) sg , acte ts al)))
          =< ass (proje ga' x ts) _ _ ]=
        act (proje ga' x ts) (refl , wks al de0) /
           (all (_^ thinl oi ga) idsb
            :+ iaz ez (de' , refl , all (\ t -> act t (refl , al)) sg , acte ts al))
          =< (_/ _) $= projeActe x ts al  ]=
        proje de' x (acte ts al) /
           (all (_^ thinl oi ga) idsb
            :+ iaz ez
            (de' , refl , all (\ t -> act t (refl , al)) sg , acte ts al))
             [QED]
      instActLemman {ga} (elim e s) sg ts al
        rewrite toLibLemma trg syn
                  (elim (act (e % (sg , ts)) (refl , wks al ga))
                        (act (s % (sg , ts)) (refl , wks al ga)))
              | instActLemma e sg ts al | instActLemma s sg ts al = refl
      instActLemman {ga}{ga'} (vari i) sg ts {de'} al = hitFact al ga i
      instActLemman {ga}{ga'} (mets x) sg ts {de'} al = 
        act (project x sg ^ thinl (oi {S = ga'}) ga) (refl , wks al ga)
          =[ taa (project x sg) _ _ >=
        act (project x sg) (refl , ta (thinl oi ga) (wks al ga))
          =[ act (project x sg) $= ((refl ,_) $= (
             ta (thinl oi ga) (wks al ga)
               =[ thinFact [] ga al oe >=
             at (wks al []) (thinl oi ga)
               =[ at $= nilFact al =$ _ >=
             at al (thinl oi ga)
               [QED])) >=
        act (project x sg) (refl , at al (thinl oi ga))
          =< ata (project x sg) _ _ ]=
        act (project x sg) (refl , al) ^ thinl (oi {S = de'}) ga
          =< (_^ thinl (oi {S = de'}) ga) $= (top $= selectAll x _ sg) ]=
        project x (all (\ t -> act t (refl , al)) sg) ^ thinl (oi {S = de'}) ga
          [QED]
      instActLemmaz [] sg ts al = refl
      instActLemmaz (ez -, e) sg ts al
        rewrite instActLemmaz ez sg ts al | instActLemma e sg ts al = refl

      instActLemma0 : forall {d ga'}
        (t : Term M [] lib d)
        (sg : [ N ! fst M ]/ ga')(ts : Env N (ga' ,P snd M)) ->
        forall {de'}(al : A N ga' de') ->
        act (t % (sg , ts)) (refl , al) ==
          (t % (all (\ t -> act t (refl , al)) sg , acte ts al))
      instActLemma0 t sg ts al
        rewrite sym (instActLemma t sg ts al) | nilFact al = refl

module _ {M : Meta} where
  open Monoidal (OPEMON {One})

  open PLUGINSTACT SBSTTHENTHIN OBJTHINSBSTSBST OBJTHINTHINTHIN OBJTHINTHINTHIN
    THINWEAK
    (\ _ -> refl)
    (\ de0 ga ph th -> 
      (oi ^+ th) -< (ph ^+ oi {S = ga})
           =[ moco oi th ph oi >=
      ((oi -< ph) ^+ (th -< oi))
           =[ _^+_ $= oiLemma ph =$= sym (oiLemma th) >=
      ((ph -< oi) ^+ (oi -< th))
           =< moco ph oi oi th ]=
      (ph ^+ oi {S = de0}) -< (oi ^+ th)
        [QED])
    (\ {M}{de}{de'} th ga i -> #_ $= (
      ((i -< thinr de oi) -< (th ^+ oi {S = ga}))
        =< cocoC i (thinr de oi) (th ^+ oi {S = ga}) ]=
      (i -< (thinr de oi -< (th ^+ oi {S = ga})))
        =[ (i -<_) $= (
          thinr de oi -< (th ^+ oi {S = ga})
            =[ thinrLemma oi th (oi {S = ga}) >=
          thinr de' (oi -< oi)
            =[ thinr de' $= idcoC (oi {S = ga}) >=
          thinr de' oi
            [QED]) >=
      (i -< thinr de' oi)
        [QED]))
    M

  plugThinLemma = plugActLemma

  module _ {N : Meta} where
    open INSTACT {N} (\ {de}{de'} de0 ga th ez -> 
      select (th ^+ oi {S = de0}) (all (_^ thinl oi ga) idsb :+ ez)
        =[ selCat th (oi {S = de0}) (all _ idsb) ez >=
      select th (all (_^ thinl oi ga) idsb) :+ select oi ez
        =[ _:+_ $= (
            select th (all (_^ thinl oi ga) idsb)
              =< select th $= selIdsb (thinl oi ga) ]=
            select th (select (thinl oi ga) idsb)
              =< funCo (thinl oi ga) th idsb ]=
            select (th -< thinl oi ga) idsb
              =[ select $=(
                   (th -< thinl oi ga)
                     =[ moco th ze oi oe >=
                   (th -< oi) ^+ (ze -< oe {xz = ga})
                     =< _^+_ $= oiLemma th =$= oeU _ _ ]=
                   (oi -< th) ^+ (oe -< oi {S = ga})
                     =< moco oi oe th (oi {S = ga}) ]=
                   (thinl oi ga -< (th ^+ oi {S = ga}))
                     [QED]
               )=$ idsb >=
            select (thinl oi ga -< (th ^+ oi {S = ga})) idsb
              =[ selIdsb (thinl oi ga -< (th ^+ oi {S = ga})) >=
            all (_^ (thinl oi ga -< (th ^+ oi {S = ga}))) idsb
              [QED])
          =$= funId ez >=
      all (_^ (thinl oi ga -< (th ^+ oi {S = ga}))) idsb :+ ez
        [QED])

    instThinLemma = instActLemma

module _ {M : Meta} where
  open Monoidal (OPEMON {One})

  open PLUGINSTACT SBSTTHENSBST OBJSBSTSBSTSBST OBJTHINSBSTSBST OBJSBSTTHINSBST
    SBSTWEAK
    (allId _ (ActIden.idaId THINIDEN))
    (\ {M}{de}{de'} de0 ga sg th -> 
      select (oi ^+ th)
        (all (_^ thinl oi ga) sg :+ all (_^ thinr de' (oi {S = ga})) idsb)
        =[ selCat oi th (all _ sg) (all _ idsb) >=
      (select oi (all (_^ thinl oi ga) sg) :+
       select th (all (_^ thinr de' (oi {S = ga})) idsb))
        =[ _:+_ $= funId _ =$= (
            select th (all (_^ thinr de' (oi {S = ga})) idsb)
              =< select th $= selIdsb (thinr de' (oi {S = ga})) ]=
            select th (select (thinr de' (oi {S = ga})) idsb)
              =< funCo (thinr de' (oi {S = ga})) th idsb ]=
            select (th -< thinr de' (oi {S = ga})) idsb
              =[ select $= (
                (th -< thinr de' (oi {S = ga}))
                  =[ thinrAmmel th (oi {S = ga}) >=
                thinr de' (th -< oi)
                  =[ thinr de' $= coidC th >=
                thinr de' th
                  [QED]) =$ idsb >=
            select (thinr de' th) idsb
              [QED]) >=
      (all (_^ thinl oi ga) sg :+ select (thinr de' th) idsb)
        =[ (all (_^ thinl oi ga) sg :+_) $= selIdsb (thinr de' th) >=
      (all (_^ (thinl oi ga)) sg :+ all (_^ (thinr de' th)) idsb)
        =[ _:+_ $= allCo _ _ _ (\ t ->
                   t ^ thinl oi ga
                     =[ (t ^_) $= (
                        thinl oi ga
                          =< _^+_ $= idcoC oi =$= oeU (oe -< th) _ ]=
                        (oi -< oi) ^+ (oe -< th)
                          =< moco oi oe oi th ]=
                        thinl oi de0 -< (oi ^+ th)
                          [QED]) >=
                   t ^ (thinl oi de0 -< (oi ^+ th))
                     =< thinco t _ _ ]=
                   ((t ^ thinl oi de0) ^ (oi ^+ th))
                     [QED]) sg
               =$= allCo _ _ _ (\ t ->
                  t ^ thinr de' th
                    =[ (t ^_) $= (
                       thinr de' th
                         =< thinr de' $= idcoC th ]=
                       thinr de' (oi -< th)
                         =< thinrLemma oi oi th ]=
                       thinr de' oi -< (oi ^+ th)
                         [QED]) >=
                  t ^ (thinr de' oi -< (oi ^+ th))
                    =< thinco t _ _ ]=
                  (t ^ (thinr de' oi)) ^ (oi ^+ th)
                    [QED]) idsb >=
      (all (_^ (oi ^+ th)) (all (_^ thinl oi de0) sg) :+
       all (_^ (oi ^+ th)) (all (_^ thinr de' (oi {S = de0})) idsb))
        =< allCat _ (all _ sg) (all _ idsb) ]=
      all (_^ (oi ^+ th)) (all (_^ thinl oi de0) sg :+ all (_^ thinr de' oi) idsb)
        [QED])
    (\ {M}{de}{de'} sg ga i -> 
      project (i -< thinr de oi)
        (all (_^ thinl oi ga) sg :+ all (_^ thinr de' (oi {S = ga})) idsb)
        =[ project $= (
             i -< thinr de oi
               =[ thinrAmmel i oi >=
             thinr de (i -< oi)
               =[ thinr de $= coidC i >=
             thinr de i
               [QED])
            =$ (all (_^ thinl oi ga) sg :+ all (_^ thinr de' (oi {S = ga})) idsb) >=
      project (thinr de i)
        (all (_^ thinl oi ga) sg :+ all (_^ thinr de' (oi {S = ga})) idsb)
        =[ top $= selRight i (all _ sg) (all _ idsb) >=
      project i (all (_^ thinr de' oi) idsb)
        =< project i $= selIdsb (thinr de' oi) ]=
      project i (select (thinr de' oi) idsb)
        =< top $= funCo (thinr de' oi) i idsb ]=
      project (i -< thinr de' oi) idsb
        =[ idsbHit (i -< thinr de' oi) >=
      # (i -< thinr de' oi)
        [QED])
    M

  plugSbstLemma = plugActLemma
  plugSbstLemma0 = plugActLemma0

  module _ {N : Meta} where
    open ActWeak SBSTWEAK
    open Monoidal (MONSBST {N})
    open INSTACT {N} (
     \ {de}{de'} de0 ga sg ez -> 
      all (_/ (all (_^ thinl oi ga) idsb :+ ez)) (sg >/< idsb {de0})
        =[ allCat (_/ (all (_^ thinl oi ga) idsb :+ ez))
            (all _ sg) (all _ (idsb {de0})) >=
      all (_/ (all (_^ thinl oi ga) idsb :+ ez)) (all (_^ thinl oi de0) sg) :+
      all (_/ (all (_^ thinl oi ga) idsb :+ ez)) (all (_^ thinr de' oi) (idsb {de0}))
        =[ _:+_
          $=  (all (_/ (all (_^ thinl oi ga) idsb :+ ez)) (all (_^ thinl oi de0) sg)
                =< allCo _ _ _ (\ t ->
                   t ^ thinl oi ga
                     =< (_^ thinl oi ga) $= ActIden.idaId SBSTIDEN t ]=
                   (t / idsb) ^ thinl oi ga
                     =[ ActCompo.coLib SBSTTHINSBST t _ _ >=
                   t / all (_^ thinl oi ga) idsb
                     =< (t /_) $= leftis (all _ idsb) ez ]=
                   t / lefts de' de0 (all (_^ thinl oi ga) idsb :+ ez)
                     =< ActCompo.coLib THINSBSTSBST t _ _ ]=
                   (t ^ thinl oi de0) / (all (_^ thinl oi ga) idsb :+ ez)
                     [QED]) sg  ]=
               all (_^ thinl oi ga) sg [QED])
          =$= (all (_/ (all (_^ thinl oi ga) idsb :+ ez))
                (all (_^ thinr de' oi) (idsb {de0}))
                 =< all (_/ _) $= selIdsb (thinr de' oi) ]=
               all (_/ (all (_^ thinl oi ga) idsb :+ ez))
                 (select (thinr de' oi) (idsb {de' -+ de0}))
                 =< selectAll (thinr de' oi) (_/ _) (idsb {de' -+ de0}) ]=
               rights de' de0 (all (_/ (all (_^ thinl oi ga) idsb :+ ez)) idsb)
                 =[ rights de' de0 $= Cat.idcoC SUBSTITUTION _ >=
               rights de' de0 (all (_^ thinl oi ga) idsb :+ ez)
                 =[ rightis (all _ idsb) ez >=
               ez [QED]) >=
      all (_^ thinl oi ga) sg :+ ez
        =< (_:+ ez) $= (
          all ((_/ lefts de ga (sg >/< idsb {ga}))) idsb
            =[ Cat.idcoC SUBSTITUTION _ >=
          lefts de ga (sg >/< idsb {ga})
            =[ leftis (all _ sg) (all _ (idsb {ga})) >=
          all (_^ thinl oi ga) sg
            [QED]) ]=
      all ((_/ lefts de ga (sg >/< idsb {ga}))) idsb :+ ez
        [QED])

    instSbstLemma = instActLemma
    instSbstLemma0 = instActLemma0
  
