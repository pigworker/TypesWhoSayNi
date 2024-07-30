module Act where

open import Eq
open import Fun
open import Basics
open import Cats
open import Bwd
open import Thin
open import Atom
open import All
open import Pat
open import Term

------------------------------------------------------------------------------
-- ACTIONS ON FREE (SCHEMATIC OR OTHERWISE) VARIABLES
------------------------------------------------------------------------------

record Act (A : Meta * Nat -> Meta * Nat -> Set) : Set where
  field
    trg : Lib
    hit : forall {M G N D} -> (<> <- G) -> A (M , G) (N , D) -> Term N D trg syn
    met : forall {M G N D X} -> (X <P- snd M) -> A (M , G) (N , D) ->
            All (\ _ -> Term N D lib syn) X -> Term N D lib chk
    mee : forall {M G N D} -> (<> <- fst M) -> A (M , G) (N , D) -> Term N D trg syn
    wkn : forall {p G q D} -> A (p , G) (q , D) -> A (p , (G -, <>)) (q , (D -, <>))

  act  : forall {M G N D d} -> Term M G lib d -> A (M , G) (N , D) -> Term N D lib d
  actk : forall {M G N D} -> Term M G ess chk -> A (M , G) (N , D) -> Term N D ess chk
  actn : forall {M G N D} -> Term M G ess syn -> A (M , G) (N , D) -> Term N D trg syn
  actz : forall {M G N D}{X} -> All (\ _ -> Term M G lib syn) X ->
                         A (M , G) (N , D) -> All (\ _ -> Term N D lib syn) X
  act  (thnk n)  al = toLib trg chk (actn n al)
  act  (t :: T)  al = act t al :: act T al
  act  (x ?- ez) al = met x al (actz ez al)
  act {d = chk} (essl t) al = essl (actk t al)
  act {d = syn} (essl t) al = toLib trg syn (actn t al)
  actk (atom a)    al = atom a
  actk (cons s t)  al = cons (act s al) (act t al)
  actk (abst t)    al = abst (act t (wkn al))
  actn (vari i)   al = hit i al
  actn (elim e s) al = essTo trg (elim (act e al) (act s al))
  actn (mets x)   al = mee x al
  actz []         al = []
  actz (ez -, e)  al = actz ez al -, act e al

  actzAll : forall {M G N D}{n}(ez : All (\ _ -> Term M G lib syn) n)
              (al : A (M , G) (N , D)) -> actz ez al == all (\ e -> act e al) ez
  actzAll []        al = refl
  actzAll (ez -, e) al = _-,_ $= actzAll ez al =$= refl

  actThunk : forall {p G q D}(e : Term p G lib syn)(al : A (p , G) (q , D)) ->
    act [ e ] al == [ act e al ]
  actThunk (essl n) al = trgLemma trg (actn n al)
  actThunk (t :: T) al = refl


------------------------------------------------------------------------------
-- ACTIONS ON FREE OBJECT VARIABLES
------------------------------------------------------------------------------


record ObjAct (trg : Lib)(M : Meta)(A : Nat -> Nat -> Set) : Set where
  field
    objHit : forall {G D}(i : <> <- G)(al : A G D) -> Term M D trg syn
    objWkn : forall {G D}(al : A G D) -> A (G -, <>) (D -, <>)
  objWkns : forall {G D}(al : A G D) X -> A (G -+ X) (D -+ X)
  objWkns al [] = al
  objWkns al (X -, x) = objWkn (objWkns al X)

module _ {l}(A : Meta -> Nat -> Nat -> Set)
            (o : forall {M} -> ObjAct l M (A M)) where
  open module POLYOBJACT {M} = ObjAct (o {M})
  open Act

  ObjA : Meta * Nat -> Meta * Nat -> Set
  ObjA (M , G) (N , D) = (M == N) * A M G D
  
  objAct : Act ObjA
  trg objAct = l
  hit objAct i (refl , al) = objHit i al
  met objAct x (refl , al) ez = x ?- ez
  mee objAct x (refl , al) = essTo l (mets x)
  wkn objAct (refl , al) = refl , objWkn al

  record ActWeak : Set where
    field
      wks : forall {M G D} -> A M G D ->
            forall X         -> A M (G -+ X) (D -+ X)
      wks1 : forall {M G D}(al : A M G D) X ->
        objWkn (wks al X) == wks al (X -, <>)

    acte : forall {X}{p : Pat X}{M G D} ->
           Env M (G ,P p) -> A M G D -> Env M (D ,P p)
    acte {p = !!! a}      (!!! .a)  al = !!! a
    acte {p = p &&& q}    (D &&& E) al = (acte D al) &&& (acte E al)
    acte {p = \\\ q}      (\\\ E)   al = \\\ (acte E al)
    acte {p = ??? x {X} th} (??? t)   al = ??? (act objAct t (refl , wks al X))

    projeActe : forall {Y X}{p : Pat X}(x : Y <P- p){M G D}
      (ts : Env M (G ,P p))(al : A M G D) ->
      proje D x (acte ts al) == act objAct (proje G x ts) (refl , wks al Y)
    projeActe ???     (??? t)    al = refl
    projeActe (car x) (ts &&& _) al = projeActe x ts al
    projeActe (cdr x) (_ &&& ts) al = projeActe x ts al
    projeActe (\\\ x) (\\\ ts)   al = projeActe x ts al


------------------------------------------------------------------------------
-- THINNING
------------------------------------------------------------------------------

module _ where
  open ObjAct
  open ActWeak
  
  OBJTHIN : forall {N} -> ObjAct ess N _<=_
  objHit OBJTHIN i th = vari (i -< th)
  objWkn OBJTHIN = _su

  THIN = objAct _ OBJTHIN
  open Act THIN

  open Cat (OPE {Nat})

  _^^_ = act

  _^_ : forall {l d M G D}(t : Term M G l d)(th : G <= D) -> Term M D l d
  _^_ {ess} {chk} t th = actk t (refl , th)
  _^_ {ess} {syn} t th = actn t (refl , th)
  _^_ {lib} {d}   t th = t ^^ (refl , th)

  THINWEAK : ActWeak _ OBJTHIN
  wks THINWEAK th X = th ^+ oi {S = X}
  wks1 THINWEAK th X = refl

  _^E_ : forall {M}{p : Pat []}{G D} ->
    Env M (G ,P p) -> G <= D -> Env M (D ,P p)
  om ^E th = acte THINWEAK om th


------------------------------------------------------------------------------
-- SUBSTITUTION
------------------------------------------------------------------------------

module _ where
  open ObjAct
  open ActWeak

  [_!_]/_ : Meta -> Nat ->  Nat -> Set
  [ M ! G ]/ D = All (\ _ -> Term M D lib syn) G

  wksb : forall {G p D} -> [ p ! G ]/ D -> [ p ! G -, <> ]/ D -, <>
  wksb sg = all (_^ (oi no)) sg -, # (oe su)

  idsb : forall {G M} ->  [ M ! G ]/ G
  idsb {[]}      = []
  idsb {G -, <>} = wksb idsb

  OBJSBST : forall {p} -> ObjAct lib p ([_!_]/_ p)
  objHit OBJSBST = project
  objWkn OBJSBST = wksb

  SBST = objAct _ OBJSBST
  open Act SBST
  
  _//_ = act

  _/_ : forall {l d M G D}(t : Term M G l d)(sg : [ M ! G ]/ D) -> Term M D lib d
  _/_ {ess} {chk} t sg = essl (actk t (refl , sg))
  _/_ {ess} {syn} t sg = actn t (refl , sg)
  _/_ {lib} {d}   t sg = t // (refl , sg)


------------------------------------------------------------------------------
-- INSTANTIATION
------------------------------------------------------------------------------

module _ where
  open Act

  Inst : Meta * Nat -> Meta * Nat -> Set
  Inst ((gas , p) , X) (N , D) = Sg _ \ G -> D == (G -+ X) *
     ([ N ! gas ]/ G) * Env N (G ,P p)

  INST : Act Inst
  trg INST = lib
  hit INST i (G , refl , _) = # (i -< thinr G oi)
  met INST {G = X} x (G , refl , _ , ts) ez =
    proje G x ts / (all (_^ thinl oi X) idsb :+ ez)
  mee INST {G = X} x (G , refl , sg , _) = project x sg ^ thinl oi X
  wkn INST (G , refl , sgts) = G , refl , sgts

  _%_ : forall {d M N X G} ->
        Term M X lib d -> ([ N ! fst M ]/ G) * Env N (G ,P snd M) ->
        Term N (G -+ X) lib d
  _%_ {G = G} t sgts = act INST t (G , refl , sgts)


------------------------------------------------------------------------------
-- PATTERN PLUGGING
------------------------------------------------------------------------------

infixl 30 _%P_

_%P_ : forall {D G M} ->
  (p : Pat G) -> Env M (D ,P p) -> Term M (D -+ G) lib chk
!!! a     %P  !!! .a    = ! a
p &&& q   %P  ss &&& ts = (p %P ss) & (q %P ts)
\\\ q     %P  \\\ ts    = \\ (q %P ts)
??? _ th  %P  ??? t = t ^ (oi ^+ th)


------------------------------------------------------------------------------
-- FROM PATTERNS TO EXPRESSIONS
------------------------------------------------------------------------------

patEnv : forall {ga M}(p : Pat ga) de ->
         (forall {de} -> de <P- p -> de <P- snd M) ->
         Env M (de ,P p)
patEnv (!!! a) de v = !!! a
patEnv (p &&& q) de v = patEnv p de (v ` car) &&& patEnv q de (v ` cdr)
patEnv (\\\ q) de v = \\\ patEnv q de (v ` \\\_)
patEnv (??? _ th) de v = ??? (v ??? ?- all (_^ thinr de oi) idsb)

patTerm : forall {ga M}(p : Pat []) ->
          (forall {de} -> de <P- p -> de <P- snd M) ->
          Term M ga lib chk
patTerm p v = p %P patEnv p _ v


------------------------------------------------------------------------------
-- THICKENING
------------------------------------------------------------------------------

thickTerm? : forall {M de ga l d}(th : de <= ga)(t : Term M ga l d) ->
  One + Sg _ \ t' -> t == (t' ^ th)  -- lazy bastard; decide this!
thickTermz? : forall {M de ga n}(th : de <= ga)
  (ez : All (\ _ -> Term M ga lib syn) n) ->
  One + Sg _ \ ez' -> ez == Act.actz THIN ez' (refl , th)
thickTerm? th (atom a) = #1 , atom a , refl
thickTerm? th (cons s t) =
  thickTerm? th s ?>= \ { (s' , refl) ->
    thickTerm? th t ?>= \ { (t' , refl) ->
      #1 , cons s' t' , refl } }
thickTerm? th (abst t) =
  thickTerm? (th su) t ?>= \ { (t' , refl) -> #1 , abst t' , refl }
thickTerm? th (vari i) with thick? th i
thickTerm? th (vari i) | #0 , a = #0 , _
thickTerm? th (vari .(j -< th)) | #1 , j , refl = #1 , vari j , refl
thickTerm? th (elim e s) =
  thickTerm? th e ?>= \ { (e' , refl) ->
    thickTerm? th s ?>= \ { (s' , refl) ->
      #1 , elim e' s' , refl } }
thickTerm? {d = chk} th (essl t) =
  thickTerm? th t ?>= \ { (t' , refl) -> #1 , essl t' , refl }
thickTerm? {d = syn} th (essl t) =
  thickTerm? th t ?>= \ { (t' , refl) -> #1 , essl t' , refl }
thickTerm? th (thnk n) =
  thickTerm? th n ?>= \ { (n' , refl) -> #1 , thnk n' , refl }
thickTerm? th (t :: T) =
  thickTerm? th t ?>= \ { (t' , refl) ->
    thickTerm? th T ?>= \ { (T' , refl) ->
      #1 , t' :: T' , refl } }
thickTerm? th (x ?- ez) =
  thickTermz? th ez ?>= \ { (ez' , refl) -> #1 , (x ?- ez') , refl }
thickTerm? th (mets x) = #1 , mets x , refl
thickTermz? th [] = #1 , [] , refl
thickTermz? th (ez -, e) =
  thickTermz? th ez ?>= \ { (ez' , refl) ->
    thickTerm? th e ?>= \ { (e' , refl) ->
      #1 , ez' -, e' , refl } }
