module ActGood where

open import Basics
open import Eq
open import Cats
open import Bwd
open import Thin
open import All
open import Term

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
      idaWkn : forall {G M} -> ida {G -, <>}{M} == wkn ida
      idaHit : forall {G M}(i : <> <- G) -> hit i (ida {G}{M}) == essTo trg (vari i)
      idaMet : forall {G M X}(x : X <- M) ez -> met x (ida {G}{M}) ez == (x ?- ez)

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
    idaz []        = refl
    idaz (ez -, e) rewrite idaz ez | idaId e = refl

module _ where
  open ActIden
  
  THINIDEN : ActIden THIN
  ida THINIDEN = oi , oi
  idaWkn THINIDEN = refl
  idaHit THINIDEN i = vari $= coidC _
  idaMet THINIDEN x ez = (_?- ez) $= coidC _

  idsbHit : forall {M G}(i : <> <- G) -> project i (idsb {G}{M}) == (# i)
  idsbHit (i no) =
    top (select i (all (_^ (oi no)) idsb)) =[ top $= selectAll i (_^ (oi no)) idsb >=
    (top (select i idsb) ^ (oi no)) =[ (_^ (oi no)) $= idsbHit i >=
    (# i ^ (oi no)) =[ #_ $= (_no $= coidC _) >=
    # (i no) [QED]
  idsbHit (i su) rewrite oeU i oe = refl

  SBSTIDEN : ActIden SBST
  ida SBSTIDEN = oi , idsb
  idaWkn SBSTIDEN = refl
  idaHit SBSTIDEN i = idsbHit i
  idaMet SBSTIDEN x ez = (_?- ez) $= coidC _

module _ {AF AB AC}(OAF : Act AF)(OAB : Act AB)(OAC : Act AC)
  where
  open Act
  record ActCompo : Set where
    field
      co : forall {MG0 MG1 MG2} -> AF MG0 MG1 -> AB MG1 MG2 -> AC MG0 MG2
      hitCo : forall {M0 G0 MG1 MG2}(i : <> <- G0)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2)
        -> act OAB (toLib (trg OAF) syn (hit OAF i f)) b ==
           toLib (trg OAC) syn (hit OAC i (co f b))
      metCo : forall {M0 G0 M1 G1 MG2 X}(x : X <- M0)(ez : All (\ _ -> Term M1 G1 lib syn) X)
        (f : AF (M0 , G0) (M1 , G1))(b : AB (M1 , G1) MG2)
        -> act OAB (met OAF x f ez) b == met OAC x (co f b) (actz OAB ez b)
      wknCo : forall {MG0 MG1 MG2}(f : AF MG0 MG1)(b : AB MG1 MG2)
        -> co (wkn OAF f) (wkn OAB b) == wkn OAC (co f b)
    coLib : forall {M0 G0 MG1 MG2 d}(t : Term M0 G0 lib d)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2) ->
            act OAB (act OAF t f) b == act OAC t (co f b)
    coCan : forall {M0 G0 MG1 MG2}(k : Term M0 G0 ess chk)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2) ->
            actk OAB (actk OAF k f) b == actk OAC k (co f b)
    coNeu : forall {M0 G0 MG1 MG2}(n : Term M0 G0 ess syn)(f : AF (M0 , G0) MG1)(b : AB MG1 MG2) ->
            act OAB (toLib (trg OAF) syn (actn OAF n f)) b == toLib (trg OAC) syn (actn OAC n (co f b))
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
            | toLibLemma (trg OAB) syn (elim (act OAB (act OAF e f) b) (act OAB (act OAF s f) b))
            | toLibLemma (trg OAC) syn (elim (act OAC e (co f b)) (act OAC s (co f b)))
            | coLib e f b | coLib s f b
            = refl
    coz []        f b = refl
    coz (ez -, e) f b rewrite coz ez f b | coLib e f b = refl

module _ {F B C : Bwd Nat -> Nat -> Nat -> Set}{fl bl cl}
  (of : forall {N} -> ObjAct fl N (F N))
  (ob : forall {N} -> ObjAct bl N (B N))
  (oc : forall {N} -> ObjAct cl N (C N))
  where
  open Act
  open ActCompo
  open POLYOBJACT

  record ObjComp : Set where
    field
      coth : forall {G0 M1 G1 M2 G2} ->
        F M1 G0 G1 -> M1 <= M2 -> B M2 G1 G2 -> C M2 G0 G2
      hitth : forall {G0 M1 G1 M2 G2}(i : <> <- G0)
        (f : F M1 G0 G1)(ph : M1 <= M2)(b : B M2 G1 G2) ->
        act (objAct _ ob) (toLib fl syn (objHit _ of i f)) (ph , b) ==
        toLib cl syn (objHit _ oc i (coth f ph b))
      wknth : forall {G0 M1 G1 M2 G2}
        (f : F M1 G0 G1)(ph : M1 <= M2)(b : B M2 G1 G2) ->
          coth (objWkn _ of f) ph (objWkn _ ob b) == objWkn _ oc (coth f ph b)

    thinAComp : ActCompo (objAct _ of) (objAct _ ob) (objAct _ oc)
    co thinAComp (th , f) (ph , b) = (th -< ph) , coth f ph b
    hitCo thinAComp i (th , f) (ph , b) = hitth i f ph b
    metCo thinAComp x ez (th , f) (ph , b) =  (_?- _) $= sym (cocoC x th ph)
    wknCo thinAComp (th , f) (ph , b) = ((th -< ph) ,_) $= wknth f ph b

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
  
  icompoLemma : forall {I}{M0 M1 M2 M3 : Bwd Nat}{G0 G1 G2 G3 : I -> Nat}
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
  coth  OBJTHINTHINTHIN th _ ph = th -< ph
  hitth OBJTHINTHINTHIN i th _ ph = #_ $= sym (cocoC i th ph)
  wknth OBJTHINTHINTHIN _ _ _ = refl
  THINTHINTHIN = thinAComp OBJTHINTHINTHIN

  thinco : forall {M G0 G1 G2 d}(t : Term M G0 lib d)(th : G0 <= G1)(ph : G1 <= G2) ->
    ((t ^ th) ^ ph) == t ^ (th -< ph)
  thinco t th ph = 
    ((t ^ th) ^ ph) =[ coLib t (oi , th) (oi , ph) >=
    (t ^^ ((oi -< oi) , (th -< ph))) =[ (t ^^_) $= (_,_ $= idcoC _ =$= refl) >=
    t ^ (th -< ph) [QED]
    where open ActCompo THINTHINTHIN


  OBJTHINSBSTSBST : ObjComp OBJTHIN OBJSBST OBJSBST
  coth  OBJTHINSBSTSBST th ph sg = select th sg
  hitth OBJTHINSBSTSBST i th ph sg = top $= funCo th i sg
  wknth OBJTHINSBSTSBST th ph sg = (_-, _) $= selectAll th (_^ (oi no)) sg
  THINSBSTSBST = thinAComp OBJTHINSBSTSBST

module _ where
  open ActCompo THINTHINTHIN
  
  idsbSel : forall {MG ND}(al : ThinA _ OBJTHIN MG ND) ->
    all (_^^ al) idsb == select (snd al) idsb
  idsbSel (th , (ph no)) = 
    all (_^^ (th , (ph no))) idsb =[ allCo _ _ _ (\ t ->
      (t ^^ (th , (ph no))) =< (t ^^_) $= (_,_ $= coidC th =$= (_no $= coidC ph)) ]=
      (t ^^ ((th -< oi) , ((ph -< oi) no))) =< coLib t (th , ph) (oi , (oi no)) ]=
      ((t ^^ (th , ph)) ^ (oi no)) [QED]) idsb >=
    all (_^ (oi no)) (all (_^^ (th , ph)) idsb) =[ all (_^ (oi no)) $= idsbSel (th , ph) >=
    all (_^ (oi no)) (select ph idsb) =< selectAll ph _ idsb ]=
    select ph (all (_^ (oi no)) idsb) [QED]
  idsbSel (th , (ph su)) = _-,_
    $=  (all (_^^ (th , (ph su))) (all (_^ (oi no)) idsb)
           =[ icompoLemma THINTHINTHIN THINTHINTHIN _ _ _ _ (_,_
                $=  oiLemma th
                =$= (_no $= oiLemma ph)) idsb >=
         all (_^ (oi no)) (all (_^^ (th , ph)) idsb) =[ all (_^ (oi no)) $= idsbSel (th , ph) >=
         all (_^ (oi no)) (select ph idsb) =< selectAll ph _ idsb ]=
         select ph (all (_^ (oi no)) idsb) [QED])
    =$= (#_ $= (_su $= oeU _ _))
  idsbSel (th , ze) = refl


module _ {A : Bwd Nat -> Nat -> Nat -> Set}{l}(OA : forall {N} -> ObjAct l N (A N)) where
  open module POLYA {N} = ObjAct (OA {N})
  open ObjComp
  open Act

  record SbstThen : Set where
    field
      hitthZero : forall {M G D}(al : A M G D) ->
        toLib l syn (objHit (oe su) (objWkn al)) == # (oe su)
      thinThen  : ObjComp OBJTHIN OA OA
      thenThin  : ObjComp OA OBJTHIN OA
      wknthThin : forall {M N G D}(ph : M <= N)(al : A N G D) ->
        coth thinThen (oi no) ph (objWkn al) == coth thenThin al oi (oi no)
    compSbst : ObjComp OBJSBST OA OBJSBST
    coth  compSbst sg ph al = all (\ t -> act (objAct _ OA) t (ph , al)) sg
    hitth compSbst i sg ph al = sym (top $= selectAll i _ sg) -- sym (top $= selectAll i _ sg)
    wknth compSbst sg ph al = _-,_
      $=  icompoLemma (thinAComp thinThen) (thinAComp thenThin) _ _ _ _
            (_,_ $= oiLemma ph =$= wknthThin ph al)
            sg
      =$= hitthZero al

module _ where
  open SbstThen
  open ObjComp

  SBSTTHENTHIN : SbstThen OBJTHIN
  hitthZero SBSTTHENTHIN _ = #_ $= (_su $= oeU _ _)
  thinThen  SBSTTHENTHIN = OBJTHINTHINTHIN
  thenThin  SBSTTHENTHIN = OBJTHINTHINTHIN
  wknthThin SBSTTHENTHIN ph th = _no $= oiLemma th

  OBJSBSTTHINSBST = compSbst SBSTTHENTHIN
  SBSTTHINSBST = thinAComp OBJSBSTTHINSBST

  SBSTTHENSBST : SbstThen OBJSBST
  hitthZero SBSTTHENSBST _ = refl
  thinThen  SBSTTHENSBST = OBJTHINSBSTSBST
  thenThin  SBSTTHENSBST = OBJSBSTTHINSBST
  wknthThin SBSTTHENSBST ph sg = funId _

  OBJSBSTSBSTSBST = compSbst SBSTTHENSBST
  SBSTSBSTSBST = thinAComp OBJSBSTSBSTSBST

module _ where
  open ActCompo THINSBSTSBST
  
  coidsb : forall {M G N D}(th : M <= N)(sg : [ N ! G ]/ D) ->
    all (_// (th , sg)) idsb == sg
  coidsb th [] = refl
  coidsb th (sg -, e) = (_-, _) $= (
    all (_// (th , (sg -, e))) (all (_^ (oi no)) idsb)
      =< allCo _ _ _ (\ t -> 
          (t // (th , sg))
            =< (t //_) $= (_,_ $= idcoC _ =$= funId _) ]=
          (t // ((oi -< th) , select oi sg))
            =< coLib t _ _ ]=
          ((t ^ (oi no)) // (th , (sg -, e))) [QED]) idsb ]=
    all (_// (th , sg)) idsb
      =[ coidsb th sg >=
    sg [QED])



module _ where
  open ActCompo
  open ObjComp

  THININSTINST : ActCompo THIN INST INST
  co THININSTINST (th , ph) (xi , sg) = select th xi , select ph sg
  hitCo THININSTINST i (th , ph) (xi , sg) = hitth OBJTHINSBSTSBST i ph oi sg
  metCo THININSTINST x ez (th , ph) b@(xi , sg)  =
    (project (x -< th) xi / _) 
      =[ _/_ $= (top $= funCo th x xi) =$= refl >=
    (project x (select th xi) / _) [QED]
  wknCo THININSTINST (th , ph) (xi , sg) = _,_
    $=  selectAll th _ xi
    =$= wknth OBJTHINSBSTSBST ph oi sg

  INSTTHININST : ActCompo INST THIN INST
  co INSTTHININST (xi , sg) (th , ph) =
    all (\ {X} -> (_^^ (th , (ph ^+ oi {S = X})))) xi , (all (_^^ (th , ph)) sg)
  hitCo INSTTHININST i (xi , sg) (th , ph) = sym (top $= selectAll i _ sg)
  metCo INSTTHININST {X = X} x ez (xi , sg) (th , ph) = 
    ((project x xi / (idsb :+ ez)) ^^ (th , ph))
      =[ coLib SBSTTHINSBST (project x xi) _ _ >=
    (project x xi // ((oi -< th) , all (_^^ (th , ph)) (idsb :+ ez)))
      =[ (project x xi //_) $= (_,_ $= oiLemma th =$= (
        all (_^^ (th , ph)) (idsb :+ ez) =[ allCat _ _ ez >=
        (all (_^^ (th , ph)) idsb :+ all (_^^ (th , ph)) ez)
          =[ _:+_
            $=  idsbSel (th , ph)
            =$= (all (_^^ (th , ph)) ez =< Act.actzAll THIN _ _ ]=
                 Act.actz THIN ez (th , ph) =< funId _ ]=
                 select oi (Act.actz THIN ez (th , ph)) [QED]) >=
        (select ph idsb :+ select oi (Act.actz THIN ez (th , ph))) =< selCat ph (oi {S = X}) idsb _ ]=
        select (ph ^+ oi {S = X}) (idsb :+ Act.actz THIN ez (th , ph)) [QED])) >=
    (project x xi // ((th -< oi) , select (ph ^+ oi {S = X}) (idsb :+ Act.actz THIN ez (th , ph))))
      =< coLib THINSBSTSBST (project x xi) _ _ ]=      
    ((project x xi ^^ (th , (ph ^+ oi {S = X}))) / (idsb :+ Act.actz THIN ez (th , ph)))
      =< (_/ (idsb :+ Act.actz THIN ez (th , ph))) $=
         (top $= selectAll x (\ {X} -> (_^^ (th , (ph ^+ oi {S = X})))) xi) ]=
    (project x (all (\ {X} -> (_^^ (th , (ph ^+ oi {S = X})))) xi)
       / (idsb :+ Act.actz THIN ez (th , ph))) [QED]
  wknCo INSTTHININST (xi , sg) (th , ph) = _,_
    $=  icompoLemma THINTHINTHIN THINTHINTHIN _ _ _ _ (\ {X} -> _,_
      $=  oiLemma th
      =$= ((((oi no) ^+ oi {S = X}) -< ((ph su) ^+ oi {S = X}))
             =[ moco (oi no) (ph su) (oi {S = X}) oi >=
           (((oi no) -< (ph su)) ^+ (oi {S = X} -< oi))
             =[ (_^+ (oi {S = X} -< oi)) $= (_no $= oiLemma ph) >=
           ((ph -< (oi no)) ^+ (oi {S = X} -< oi))
             =< moco ph (oi no) (oi {S = X}) oi ]=           
           ((ph ^+ oi {S = X}) -< ((oi no) ^+ oi {S = X})) [QED]))
      xi
    =$= (snd $= wknCo SBSTTHINSBST (oi , sg) (th , ph))

  SBSTINSTINST : ActCompo SBST INST INST
  co SBSTINSTINST (th , ta) b@(xi , sg) = select th xi , all (_%% b) ta
  hitCo SBSTINSTINST i (th , ta) b@(xi , sg) = sym (top $= selectAll i _ ta)
  metCo SBSTINSTINST x ez (th , ta) b@(xi , sg) =
    (project (x -< th) xi / _) 
      =[ _/_ $= (top $= funCo th x xi) =$= refl >=
    (project x (select th xi) / _) [QED]
  wknCo SBSTINSTINST (th , ta) (xi , sg) = _,_
    $=  selectAll th _ xi
    =$= (_-,_ $= icompoLemma THININSTINST INSTTHININST _ _ _ _
              (_,_ $= funId _ =$= funId _) ta
             =$= refl)

  module _ where
    open Act SBST
    module TI = ActIden THINIDEN
    module SI = ActIden SBSTIDEN

    
    wknsLemma : forall {M G N D}(th : M <= N)(sg : [ N ! G ]/ D) X ->
      wkns (th , sg) X == (th , (all (_^ thinl oi X) sg :+ all (_^ thinr D oi) (idsb {X})))
    wknsLemma th sg [] = (_ ,_) $= sym (allId _ TI.idaId sg)
    wknsLemma {D = D} th sg (X -, <>) rewrite wknsLemma th sg X = (th ,_) $=
      (_-,_
      $= (all (_^ (oi no)) (all (_^ thinl oi X) sg :+ all (_^ thinr D oi) (idsb {X}))
            =[ allCat _ _ (all _ (idsb {X})) >=
          (all (_^ (oi no)) (all (_^ thinl oi X) sg) :+ all (_^ (oi no)) (all (_^ thinr D oi) (idsb {X})))
            =[ _:+_
             $=
               (all (_^ (oi no)) (all (_^ thinl oi X) sg)
                 =< allCo _ _ _ (\ t -> 
                    (t ^ (thinl oi X no)) =< (t ^^_) $= (_,_ $= idcoC _ =$= (_no $= coidC _)) ]=
                    (t ^^ ((oi -< oi) , (thinl oi X -< (oi no)))) =< coLib THINTHINTHIN t _ _ ]=
                    ((t ^ thinl oi X) ^ (oi no)) [QED] ) _ ]=
                all (_^ (thinl oi X no)) sg [QED])
             =$=
               (all (_^ (oi no)) (all (_^ thinr D oi) (idsb {X}))
                  =[ icompoLemma THINTHINTHIN THINTHINTHIN _ _ _ _ (_,_ $= refl =$= (_no $= sym (oiLemma _))) idsb >=
               all (_^ (thinr D oi su)) (all (_^ (oi no)) (idsb {X})) [QED]) >=
          ((all (_^ (thinl oi X no)) sg :+ (all (_^ (thinr D oi su)) (all (_^ (oi no)) (idsb {X})))))
          [QED])
      =$= (#_ $= (_su $= oeU _ _)))
    
    INSTSBSTINST : ActCompo INST SBST INST
    co INSTSBSTINST (xi , sg) b = all (\ {X} -> (_// wkns b X)) xi , all (_// b) sg
    hitCo INSTSBSTINST i (xi , sg) b = sym (top $= selectAll i _ sg)
    metCo INSTSBSTINST {X = X} x ez (xi , sg) b@(th , ta) = 
      ((project x xi / (idsb :+ ez)) // b)
        =[ pointCompo SBSTSBSTSBST SBSTSBSTSBST _ _ _ _ (project x xi)
           (_,_ $= ((oi -< th) =[ oiLemma _ >= (th -< oi
                     ) =< (_-< oi) $= (fst $= wknsLemma th ta X) ]= (fst (wkns (th , ta) X) -< oi) [QED])
                =$= (all (_// b) (idsb :+ ez) =[ allCat _ _ ez >=
                     (all (_// b) idsb :+ all (_// b) ez) =[ _:+_
                         $= (all (_// b) idsb =[ coidsb th ta >=
                            ta =< allId _ SI.idaId ta ]=
                            all (_/ idsb) ta =< (\ z -> all (_/ z) ta) $= (
                              select (thinl oi X) (idsb :+ all _ ez) =[ selLeft oi idsb (all _ ez) >=
                              select oi idsb =[ funId _ >=
                              idsb [QED]) ]=
                            all (_/ select (thinl oi X) (idsb :+ all (_// b) ez)) ta
                              =[ allCo _ _ _ (\ t -> 
                                 (t / select (thinl oi X) (idsb :+ all (_// b) ez))
                                   =< (t //_) $= (_,_ $= idcoC _ =$= refl) ]=
                                 (t // ((oi -< oi) , select (thinl oi X) (idsb :+ all (_// b) ez)))
                                   =< coLib THINSBSTSBST t _ _ ]=
                                 ((t ^ thinl oi X) / (idsb :+ all (_// b) ez)) [QED]) ta >=
                            all (_/ (idsb :+ all (_// b) ez)) (all (_^ thinl oi X) ta) [QED])
                         =$= (all (_// b) ez
                                =< funId _ ]=
                              select oi (all (_// b) ez)
                                =< selRight oi idsb (all (_// b) ez) ]=
                              select (thinr _ oi) (idsb :+ all (_// b) ez)
                                =< coidsb _ _ ]=
                              all (_/ select (thinr _ oi) (idsb :+ all (_// b) ez)) idsb
                                =[ allCo _ _ _ (\ t -> 
                                   (t / select (thinr _ oi) (idsb :+ all (_// b) ez))
                                     =< (t //_) $= (_,_ $= idcoC _ =$= refl) ]=
                                   (t // ((oi -< oi) , select (thinr _ oi) (idsb :+ all (_// b) ez)))
                                     =< coLib THINSBSTSBST t _ _ ]=
                                   ((t ^ thinr _ oi) / (idsb :+ all (_// b) ez)) [QED] ) idsb >=
                              all (_/ (idsb :+ all (_// b) ez)) (all (_^ thinr _ oi) idsb)
                              [QED]) >=
                     (all (_/ (idsb :+ all (_// b) ez)) (all (_^ thinl oi X) ta)
                       :+ all (_/ (idsb :+ all (_// b) ez)) (all (_^ thinr _ oi) idsb))
                       =< allCat _ _ (all (_^ thinr _ oi) (idsb {X})) ]=
                     all (_/ (idsb :+ all (_// b) ez)) (all (_^ thinl oi X) ta :+ all (_^ thinr _ oi) (idsb {X}))
                        =< coth OBJSBSTSBSTSBST $= (snd $= wknsLemma th ta X) =$= refl =$= ((idsb :+_) $= actzAll ez _) ]=
                     coth OBJSBSTSBSTSBST (snd (wkns (th , ta) X)) oi
                      (idsb :+ actz ez b) [QED])) >=
      ((project x xi // wkns b X) / (idsb :+ actz ez b))
        =< (_/ (idsb :+ actz ez b)) $= (top $= selectAll x (\ {X} -> (_// wkns b X)) xi) ]=
      (project x (all (\ {X} -> (_// wkns b X)) xi) / (idsb :+ actz ez b)) [QED]
    wknCo INSTSBSTINST (xi , sg) (th , ta) = _,_
      $= icompoLemma THINSBSTSBST SBSTTHINSBST _ _ _ _ (\ {i} ->
        _,_ $= (
          (oi -< fst (wkns (wkn (th , ta)) i)) =[ (oi -<_) $= (fst $= wknsLemma th _ i) >=
          (oi -< th) =[ oiLemma th >=
          (th -< oi) =< (_-< oi) $= (fst $= wknsLemma th _ i) ]=
          (fst (wkns (th , ta) i) -< oi) [QED])
          =$= ( select ((oi no) ^+ oi {S = i}) (snd (wkns (wkn (th , ta)) i))
                  =[ select ((oi no) ^+ oi {S = i}) $= (snd $= wknsLemma th _ i) >=
                select ((oi no) ^+ oi {S = i}) (all (_^ thinl oi i) (wksb ta) :+ all (_^ thinr _ oi) (idsb {i}))
                  =[ selCat (oi no) (oi {S = i}) (all _ (wksb ta)) (all _ (idsb {i})) >=
                (select oi (all (_^ thinl oi i) (all (_^ (oi no)) ta)) :+ select oi (all (_^ thinr _ oi) (idsb {i})))
                  =[ _:+_ $= funId _ =$= funId (all _ (idsb {i})) >=
                (all (_^ thinl oi i) (all (_^ (oi no)) ta) :+ all (_^ thinr _ oi) (idsb {i}))
                  =< (_:+ all _ (idsb {i})) $= allCo _ _ _ (\ t ->
                    sym (thinco t (oi no) (thinl oi i))) _ ]=
                (all (_^ ((oi no) -< thinl oi i)) ta :+ all (_^ thinr _ oi) (idsb {i}))
                  =[ _:+_ $= allCo _ _ _ (\ t -> 
                      (t ^ ((oi no) -< thinl oi i)) =< (t ^_) $= (
                        ((oi ^+ oe {xz = i}) -< ((oi no) ^+ (oi {S = i}))) =[ moco _ _ _ (oi {S = i}) >=
                        (((oi -< oi) no) ^+ (oe -< oi {S = i}))
                          =[ _^+_ $= (_no $= idcoC _) =$= oeU _ (oe {xz = i}) >=
                        thinl (oi no) i
                          =< _^+_ $= coidC _ =$= oeU _ (oe {xz = i}) ]=
                        (((oi no) -< oi) ^+ (ze -< oe {xz = i}))
                          =< moco (oi no) oi ze (oe {xz = i}) ]=
                        ((oi no) -< thinl oi i) [QED]) ]=
                      (t ^ (thinl oi i -< ((oi no) ^+ (oi {S = i})))) =< thinco t _ _ ]=
                      ((t ^ thinl oi i) ^ ((oi no) ^+ (oi {S = i}))) [QED]
                      )
                      ta =$= allCo _ _ _ (\ t -> 
                        (t ^ thinr _ oi) =< (t ^_) $= (
                          (thinr _ oi -< ((oi no) ^+ (oi {S = i})))
                            =[ thinrLemma oi (oi no) (oi {S = i}) >=
                          thinr (_ -, <>) (oi -< oi) =[ thinr (_ -, <>) $= coidC (oi {S = i}) >=
                          thinr (_ -, <>) oi [QED]) ]=
                        (t ^ (thinr _ oi -< ((oi no) ^+ oi {S = i}))) =< thinco t _ _ ]=
                        ((t ^ thinr _ oi) ^ ((oi no) ^+ oi {S = i})) [QED]
                      ) (idsb {i}) >=
                (all (_^ ((oi no) ^+ oi {S = i})) (all (_^ thinl oi i) ta) :+
                  all (_^ ((oi no) ^+ oi {S = i})) (all (_^ thinr _ oi) (idsb {i})))
                  =< allCat (_^ ((oi no) ^+ oi {S = i})) (all (_^ thinl oi i) ta) (all (_^ thinr _ oi) (idsb {i})) ]=
                all (_^ ((oi no) ^+ oi {S = i})) (all (_^ thinl oi i) ta :+ all (_^ thinr _ oi) (idsb {i}))
                  =< all (_^ ((oi no) ^+ oi {S = i})) $= (snd $= wknsLemma th _ i) ]=
                all (_^ ((oi no) ^+ oi {S = i})) (snd (wkns (th , ta) i))  [QED]))
          xi
      =$= (snd $= wknCo SBSTSBSTSBST (oi , sg) (th , ta))

{-
module _ {A}(OA : ObjAct A) where
  open ObjAct OA
  open Act objAct 
  open ActCompo

  record SbstThen : Set where
    field
      wknZero : forall {N G D}(al : A N G D) -> objHit (oe su) (objWkn al) == # (oe su)
      thinThen : ActCompo THIN objAct objAct
      thenThin : ActCompo objAct THIN objAct
      wknThin : forall {M G N D} (ph : M <= N)(al : A N G D) ->
        co thinThen (oi , (oi no)) (wkn (ph , al)) == co thenThin (ph , al) (oi , (oi no))
                     
    compSbst : ActCompo SBST objAct SBST
    co compSbst (th , sg) (ph , al) = (th -< ph) , all (\ e -> act e (ph , al)) sg
    hitCo compSbst i (th , sg) b = sym (top $= selectAll i (\ e -> act e b) sg)
    metCo compSbst x ez (th , sg) (ph , al) = (_?- _) $= sym (cocoC x th ph)
    wknCo compSbst (th , sg) b@(ph , al) = ((th -< ph) ,_) $= (_-,_
      $= compoLemma thinThen thenThin _ _ _ _ (wknThin ph al) sg
      =$= wknZero al)
-}
{-
    record InstThen : Set where
      intComp : ActCompo INST ACTA INST
      co intComp (xi , sg) b = all (\ {X} t -> t %% {!!}) xi , all (\ t -> act t b ) sg
      hitCo intComp = {!!}
      metCo intComp = {!!}
      wknCo intComp = {!!}

-}

{-


module _ where
  open ActIden
  open POLYTHIN
  open POLYSELECT

  idsbLemma : forall {M G D}(ez : G /[ M ! D ]) -> all (_/ ez) idsb == ez
  idsbLemma [] = refl
  idsbLemma (ez -, e) = (_-, _) $= (
    all (_/ (ez -, e)) (all (_^ (oi no)) idsb)
      =< allCo _ _ _ (\ t ->
        (t // (oi , ez)) =< (t //_) $= (_,_ $= idcoC _ =$= funId ez) ]=
         (t // ((oi -< oi) , select oi ez)) =< libTSS t _ _ ]=
         ((t ^ (oi no)) / (ez -, e)) [QED]) _ ]=
    all (_/ ez) idsb
      =[ idsbLemma ez >=
    ez [QED])

  thinrLemma : forall {I P}{G X Y : Bwd I}(th : X <= Y)(az : All P G)(bz : All P Y) ->
    select (thinr G th) (az :+ bz) == select th bz
  thinrLemma (th no) az (bz -, _) = thinrLemma th az bz
  thinrLemma (th su) az (bz -, b) = (_-, _) $= thinrLemma th az bz
  thinrLemma ze [] [] = refl
  thinrLemma ze (az -, x) [] = thinrLemma oe az []

  insertLemma : forall {G}(X : Nat) ->
    (thinr G (oi {S = X}) -< ((oi no) ^+ oi {S = X})) == thinr (G -, <>) (oi {S = X})
  insertLemma [] = oeU _ _
  insertLemma (X -, x) = _su $= insertLemma X

  grrLemma : forall G {M N D}(th : M <= N)(ph : G <= D) ->
    all (_^^ (th , ph)) idsb == all (_^ ph) idsb
  grrLemma [] th ph = refl
  grrLemma (G -, <>) th ph = (_-, _) $= (
    all (_^^ (th , ph)) (all (_^ (oi no)) idsb)
      =< allCo _ _ _ (\ t -> sym (libTTT t _ _) ) _ ]=
    all (_^^ ((oi -< th), ((oi no) -< ph))) idsb
      =[ grrLemma G _ _ >=
    all (_^ ((oi no) -< ph)) idsb
      =[ allCo _ _ _ (\ t ->
        (t ^^ (oi , ((oi no) -< ph))) =< (t ^^_) $= ((_, _) $= idcoC _) ]=
         (t ^^ ((oi -< oi) , ((oi no) -< ph))) =< libTTT t _ _ ]=
         ((t ^^ (oi , (oi no))) ^^ (oi , ph)) [QED] )
        _ >=
    all (_^ ph) (all (_^ (oi no)) idsb) [QED])

  idinLemma : forall {M G X}(x : X <- M) ->
    project x (idin {M}{G}) == (x ?- all (_^ thinr G oi) idsb)
  idinLemma {G = G} (x no) = 
    project x (all (_^^ ((oi no) , oi)) idin)
      =[ top $= selectAll x _ _ >=
    (project x idin ^^ ((oi no) , oi))
      =[ (_^^ ((oi no) , oi)) $= idinLemma x >=
    ((x ?- all (_^ thinr G oi) idsb) ^^ ((oi no) , oi))
      =[ _?-_ $= (_no $= coidC _) =$= ((
        Act.actz THIN (all (_^ thinr G oi) idsb) ((oi no) , oi)
          =[ Act.actzAll THIN _ _ >=
        all (_^^ ((oi no) , oi)) (all (_^ thinr G oi) idsb) 
          =< allCo _ _ _ (\ t ->
             (t ^^ ((oi no) , thinr G oi))
               =< (t ^^_) $= (_,_ $= idcoC _ =$= coidC _) ]=
             (t ^^ ((oi -< (oi no)) , (thinr G oi -< oi)))
               =< libTTT t _ _ ]=
             ((t ^ thinr G oi) ^^ ((oi no) , oi)) [QED])
             idsb ]=
        all (_^^ ((oi no) , thinr G oi)) idsb
          =[ grrLemma _ (oi no) (thinr G oi) >=
        all (_^ thinr G oi) idsb [QED]
        )) >=
    ((x no) ?- all (_^ thinr G oi) idsb) [QED]
  idinLemma (x su) = _?-_ $= (_su $= oeU _ _) =$= refl

  INSTIDEN : ActIden INST
  ida INSTIDEN = idi
  idaWkn INSTIDEN {G}{M} = _,_ $= help M =$= refl where
    help : forall M {G} ->
       idin {M}{G -, <>} == wkin idin
    help [] = refl
    help (M -, X) {G} = _-,_
      $= (all (_^^ ((oi no) , oi)) idin
            =[ all _ $= help M >=
          all (_^^ ((oi no) , oi)) (wkin idin)
            =< allCo _ _ _ (\ {Y} t -> 
              (t ^^ ((oi no) , ((oi no) ^+ oi {S = Y})))
                =< (t ^^_) $= (_,_ $= idcoC _ =$= coidC _) ]=
              (t ^^ ((oi -< (oi no)) , (((oi no) ^+ oi {S = Y}) -< oi)))
                =< libTTT t _ _ ]=
              ((t ^^ (oi , ((oi no) ^+ oi {S = Y}))) ^^ ((oi no) , oi)) [QED]
              ) idin ]=
          all (\ {Y} -> _^^ ((oi no) , ((oi no) ^+ (oi {S = Y})))) idin
            =[ allCo _ _ _ (\ {Y} t -> 
              (t ^^ ((oi no) , ((oi no) ^+ oi {S = Y})))
                =< (t ^^_) $= (_,_ $= coidC _ =$= idcoC _) ]=
              (t ^^ (((oi no) -< oi) , (oi -< ((oi no) ^+ oi {S = Y}))))
                =< libTTT t _ _ ]=
              ((t ^^ ((oi no) , oi)) ^^ (oi , ((oi no) ^+ oi {S = Y}))) [QED]) idin >=
          all (\ {Y} -> _^^ (oi , ((oi no) ^+ (oi {S = Y}))))
            (all (_^^ ((oi no) , oi)) idin) [QED])
      =$= (_?-_ $= (_su $= oeU _ _)
      =$= (all (_^ thinr (G -, <>) oi) idsb
            =[ allCo _ _ _ (\ t ->
               (t ^ thinr (G -, <>) oi)
                 =< (t ^^_) $= (_,_ $= idcoC _ =$= insertLemma _) ]=
               (t ^^ ((oi -< oi) , (thinr G oi -< ((oi no) ^+ oi {S = X}))))
                 =< libTTT t _ _ ]=
               ((t ^ thinr G oi) ^ ((oi no) ^+ oi {S = X})) [QED]) idsb >=
          all (_^ ((oi no) ^+ oi {S = X})) (all (_^ thinr G oi) idsb)
            =< Act.actzAll THIN _ _ ]=
          Act.actz THIN (all (_^ thinr G oi) idsb) (oi , ((oi no) ^+ oi {S = X})) [QED]))
  idaHit INSTIDEN i = idsbHit i
  idaMet INSTIDEN {G} x ez rewrite idinLemma {G = G} x = _?-_
    $= coidC _
    =$= (Act.actz SBST (all (_^ thinr G oi) idsb) (oi , (idsb :+ ez))
           =[ Act.actzAll SBST _ _ >=
         all (_/ (idsb :+ ez)) (all (_^ thinr G oi) idsb)
           =< allCo _ _ _ (\ t -> 
              (t / select (thinr G oi) (idsb :+ ez))
                =[ (t //_) $= ((_, select (thinr G oi) (idsb :+ ez)) $= sym (idcoC _)) >=
              (t // ((oi -< oi) , select (thinr G oi) (idsb :+ ez)))
                =< libTSS t (oi , thinr G oi) (oi , (idsb :+ ez))  ]=
              ((t ^ (thinr G oi)) / (idsb :+ ez)) [QED]) _ ]=
         all (_/ select (thinr G oi) (idsb :+ ez)) idsb
           =[ (\ z -> all (_/ z) idsb) $= (thinrLemma oi idsb ez) >=
         all (_/ select oi ez) idsb
           =[ (\ z -> all (_/ z) idsb) $= funId ez >=
         all (_/ ez) idsb
           =[ idsbLemma ez >=
         ez [QED])

  wkis : forall {M G N D}(g : Inst (M , G) (N , D)) X -> Inst (M , (G -+ X)) (N , (D -+ X))
  wkis g []        = g
  wkis g (X -, <>) = Act.wkn INST (wkis g X)

  _-^%-_ :  forall {A B C} -> Thin A B -> Inst B C -> Inst A C
  (th , ph) -^%- (xi , sg) = select th xi , select ph sg

  module THININSTINST = COMPO.STUFF THIN INST INST _-^%-_
    (\ { i (th , ph) (xi , sg) -> top $= funCo ph i sg })
    (\ { x ez (th , ph) (xi , sg) -> 
      (project (x -< th) xi / (idsb :+ Act.actz INST ez (xi , sg)))
      =[ _/_ $= (top $= funCo th x xi) =$= refl >=
      (project x (select th xi) / (idsb :+ Act.actz INST ez (xi , sg))) [QED] })
    (\ {(th , ph) (xi , sg) -> _,_
      $=  selectAll th _ xi
      =$= (select (ph su) (wksb sg) =[ (_-, _) $= selectAll ph _ sg >=
          wksb (select ph sg) [QED]) })

  _-/%-_ : forall {A B C} -> Sbst A B -> Inst B C -> Inst A C
  (th , sg) -/%- (xi , ta) = select th xi , all (_%% (xi , ta)) sg

  module SBSTINSTINST = COMPO.STUFF SBST INST INST _-/%-_
    {!!}
    (\ { x ez (th , sg) (xi , ta) -> 
      (project (x -< th) xi / (idsb :+ Act.actz INST ez (xi , ta)))
        =[ _/_ $= (top $= funCo th x xi) =$= refl >=
      (project x (select th xi) / (idsb :+ Act.actz INST ez (xi , ta))) [QED] })
    (\ {(th , sg) (xi , ta) -> _,_
      $=  selectAll th _ xi
      =$= {!!} })

  _-%-_ : forall {A B C} -> Inst A B -> Inst B C -> Inst A C
  (xi , sg) -%- g = all (\ {X} t -> t %% wkis g X) xi , all (_%% g) sg

  module INSTINSTINST = COMPO.STUFF INST INST INST _-%-_
    (\ { i (xi , sg) b -> 
      (project i sg %% b) =< top $= selectAll i (_%% b) sg ]=
      project i (all (_%% b) sg) [QED] })
    (\ { {X = X} x ez (xi , sg) b@(ch , ta) -> 
      ((project x xi / (idsb :+ ez)) %% b) =[ {!!} >=
      ((project x xi %% wkis b X) / (idsb :+ all (_%% b) ez))
        =< _/_ $= (top $= selectAll x (\ {X} t -> t %% wkis b X) xi)
              =$= ((idsb :+_) $= Act.actzAll INST ez b) ]=
      (project x (all (\ {X} t -> t %% wkis b X) xi) / (idsb :+ Act.actz INST ez b))
        [QED] })
    (\ { (xi , sg) (ch , ta) -> _,_
      $=  {!!}
      =$= {!!} })
  
-}


