module ObjActGood where

open import Basics
open import Eq
open import Cats
open import Bwd
open import Thin
open import All
open import Term

module _ {M}{A}(OA : ObjAct M A) where
  open ObjAct OA

  record ObjActIden : Set where
    field
      ida : forall {G} -> A G G
      idaWkn : forall {G} -> ida {G -, <>} == wkn ida
      idaHit : forall {G}(i : <> <- G) -> hit i ida == # i

    module _ where

      open Cat (OPE {One})
    
    idaId : forall {G d}(t : Term M G lib d) ->
      act t (ida {G}) == t
    idaCan : forall {G}(k : Term M G ess chk) -> actk k (ida {G}) == k
    idaNeu : forall {G}(n : Term M G ess syn) -> act n (ida {G}) == essl n
    idaz : forall {G n}(ez : All (\ _ -> Term M G lib syn) n) ->
      actz ez ida == ez
    idaId {d = chk} (essl k) rewrite idaCan k = refl
    idaId {d = syn} (essl n) = idaNeu n
    idaId (thnk n)   rewrite idaNeu n = refl
    idaId (radi k T) rewrite idaCan k | idaId T = refl
    idaCan (atom a)   = refl
    idaCan (cons s t) rewrite idaId s | idaId t = refl
    idaCan (abst t)   = abst $= (
      act t (wkn ida) =< act t $= idaWkn ]=
      act t ida =[ idaId t >= t [QED])
    idaCan (meta x ez) = meta x $= idaz ez
    idaNeu (vari i)   = idaHit i
    idaNeu (elim e s) rewrite idaId e | idaId s = refl
    idaz []        = refl
    idaz (ez -, e) rewrite idaz ez | idaId e = refl

module _ {M : Bwd Nat} where
  open ObjActIden
  open Cat (OPE {One})
  THINIDEN : ObjActIden (THIN {M})
  ida THINIDEN = oi
  idaWkn THINIDEN = refl
  idaHit THINIDEN i = #_ $= coidC _

module _ {M : Bwd Nat} where
  open ObjActIden
  open Cat (OPE {One})
  SBSTIDEN : ObjActIden (SBST {M})
  ida SBSTIDEN = ids
  idaWkn SBSTIDEN = refl
  idaHit SBSTIDEN (i no) = 
    top (select i (all (_^ (oi no)) ids)) =[ top $= selectAll i (_^ (oi no)) ids >=
    (top (select i ids) ^ (oi no)) =[ (_^ (oi no)) $= idaHit SBSTIDEN i >=
    (# i ^ (oi no)) =[ #_ $= (_no $= coidC _) >=
    # (i no) [QED]
  idaHit SBSTIDEN (i su) rewrite oeU i oe = refl

module COMPO {M}{AF AB AC : Nat -> Nat -> Set}
  (OAF : ObjAct M AF)(OAB : ObjAct M AB)(OAC : ObjAct M AC)
  (co : forall {G0 G1 G2} -> AF G0 G1 -> AB G1 G2 -> AC G0 G2)
  where
  open ObjAct
  module STUFF
    (hitCo : forall {G0 G1 G2}(i : <> <- G0)(f : AF G0 G1)(b : AB G1 G2)
      -> act OAB (hit OAF i f) b == hit OAC i (co f b))
    (wknCo : forall {G0 G1 G2}(f : AF G0 G1)(b : AB G1 G2)
      -> co (wkn OAF f) (wkn OAB b) == wkn OAC (co f b))
    where
    coLib : forall {G0 G1 G2 d}(t : Term M G0 lib d)(f : AF G0 G1)(b : AB G1 G2) ->
            act OAB (act OAF t f) b == act OAC t (co f b)
    coCan : forall {G0 G1 G2}(k : Term M G0 ess chk)(f : AF G0 G1)(b : AB G1 G2) ->
            actk OAB (actk OAF k f) b == actk OAC k (co f b)
    coNeu : forall {G0 G1 G2}(n : Term M G0 ess syn)(f : AF G0 G1)(b : AB G1 G2) ->
            act OAB (act OAF n f) b == act OAC n (co f b)
    coz : forall {G0 G1 G2 n}(ez : All (\ _ -> Term M G0 lib syn) n)(f : AF G0 G1)(b : AB G1 G2) ->
            actz OAB (actz OAF ez f) b == actz OAC ez (co f b)
    coLib {d = chk} (essl k)   f b rewrite coCan k f b = refl
    coLib {d = syn} (essl n)   f b = coNeu n f b
    coLib           (thnk n)   f b
      rewrite actThunk OAB (act OAF n f) b | coNeu n f b = refl
    coLib           (radi k T) f b rewrite coCan k f b | coLib T f b = refl
    coCan (atom a)    f b = refl
    coCan (cons s t)  f b rewrite coLib s f b | coLib t f b = refl
    coCan (abst t)    f b rewrite coLib t (wkn OAF f) (wkn OAB b) | wknCo f b = refl
    coCan (meta x ez) f b = meta x $= coz ez f b
    coNeu (vari i)    f b = hitCo i f b
    coNeu (elim e s)  f b rewrite coLib e f b | coLib s f b = refl
    coz []        f b = refl
    coz (ez -, e) f b rewrite coz ez f b | coLib e f b = refl

module _ {M : Bwd Nat} where
  open Cat (OPE {One})
  module TTT = COMPO.STUFF (THIN {M}) (THIN {M}) (THIN {M}) _-<_
    (\ i f b -> #_ $= sym (cocoC i f b))
    (\ f b -> refl)
  libTTT = TTT.coLib
  
module _ {M : Bwd Nat} where
  module SELECTSBST {G} = Concrete (Select {One}{\ _ -> Term M G lib syn})
  open SELECTSBST
  module TSS = COMPO.STUFF (THIN {M}) (SBST {M}) (SBST {M}) select
    (\ i f b -> top $= funCo f i b)
    (\ f b -> (_-, _) $= selectAll f (_^ (oi no)) b)
  libTSS = TSS.coLib

module _ {M}{A : Nat -> Nat -> Set}(OA : ObjAct M A) where
  open ObjAct OA
  module SBSTTHEN
    (wknZero : forall {G D}(al : A G D) -> hit (oe su) (wkn al) == # (oe su))
    (wknThin : forall {G D}(e : Term M G lib syn)(al : A G D) ->
                 (act e al ^ (oi no)) == (act (e ^ (oi no)) (wkn al)))
    where
    module SAS = COMPO.STUFF (SBST {M}) OA (SBST {M}) (\ sg al -> all (\ e -> act e al) sg)
      (\ i f b -> 
        act (project i f) b =< top $= selectAll i (\ e -> act e b) f ]=
        project i (all (\ e -> act e b) f) [QED])
      (\ f b -> _-,_
        $= (all (\ e -> act e (wkn b)) (all (_^ (oi no)) f)
              =< allCo (_^ (oi no)) (\ e -> act e (wkn b)) (\ e -> act e b ^ (oi no))
                   (\ e -> wknThin e b) f ]=
            all (\ e -> act e b ^ (oi no)) f
              =[ allCo (\ e -> act e b) (_^ (oi no)) _ (\ _ -> refl) f >=
            all (_^ (oi no)) (all (\ e -> act e b) f)
              [QED])
        =$= wknZero b
        )

module _ {M : Bwd Nat} where
  open Cat (OPE {One})
  module STS = SBSTTHEN.SAS (THIN {M})
    (\ th -> #_ $= (_su $= oeU _ _))
    (\ e th -> 
      ((e ^ th) ^ (oi no)) =[ libTTT e th (oi no) >=
      (e ^ ((th -< oi) no)) =[ (e ^_) $= (_no $=
         ((th -< oi) =[ coidC th >= th =< idcoC th ]= (oi -< th) [QED]))
         >=
      (e ^ ((oi -< th) no)) =< libTTT e (oi no) (th su) ]=
      ((e ^ (oi no)) ^ (th su)) [QED])
  libSTS = STS.coLib

module _ {M : Bwd Nat} where
  open ObjAct (SBST {M})
  open SELECTSBST
  module SSS = SBSTTHEN.SAS (SBST {M})
    (\ _ -> refl)
    (\ e sg ->
      ((e / sg) ^ (oi no)) =[ libSTS e sg (oi no) >=
      (e / (all (_^ (oi no)) sg)) =< (e /_) $= funId _ ]=
      (e / select oi (all (_^ (oi no)) sg)) =< libTSS e (oi no) (wkn sg) ]=
      ((e ^ (oi no)) / wkn sg) [QED])
  libSSS = SSS.coLib
