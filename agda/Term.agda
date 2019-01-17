module Term where

open import Eq
open import Basics
open import Bwd
open import Thin
open import Atom
open import All

data Lib : Set where ess lib : Lib
data Dir : Set where chk syn : Dir

Nat = Bwd One

data Term (M : Bwd Nat)(G : Nat) : Lib -> Dir -> Set where
  --
  atom : (a : Atom)                                   -> Term M G ess chk
  cons : (s t : Term M G lib chk)                     -> Term M G ess chk
  abst : (t : Term M (G -, <>) lib chk)               -> Term M G ess chk
  --
  vari : (i : <> <- G)                                -> Term M G ess syn
  elim : (e : Term M G lib syn)(s : Term M G lib chk) -> Term M G ess syn
  --
  essl : {d : Dir}(t : Term M G ess d)                -> Term M G lib d
  thnk : (n : Term M G ess syn)                       -> Term M G lib chk
  _::_ : (t T : Term M G lib chk)                     -> Term M G lib syn
  --
  _?-_ : forall {n}(x : n <- M) ->
         All (\ _ -> Term M G lib syn) n              -> Term M G lib chk

pattern !_ a     = essl (atom a)
pattern _&_ s t  = essl (cons s t)
pattern \\_ t    = essl (abst t)
pattern #_ i     = essl (vari i)
pattern _$_ e s  = essl (elim e s)
infixr 60 !_ #_
infixl 50 _$_
infixr 40 _&_ \\_
infixr 30 _?-_

[_] : forall {M G} -> Term M G lib syn -> Term M G lib chk
[ essl n ] = thnk n
[ t :: T ] = t

record Act (A : Bwd Nat * Nat -> Bwd Nat * Nat -> Set) : Set where
  field
    hit : forall {M G N D} -> (<> <- G) -> A (M , G) (N , D) -> Term N D lib syn
    met : forall {M G N D X} -> (X <- M) -> A (M , G) (N , D) ->
            All (\ _ -> Term N D lib syn) X -> Term N D lib chk
    wkn : forall {M G N D} -> A (M , G) (N , D) -> A (M , (G -, <>)) (N , (D -, <>))

  wkns : forall {M G N D} -> A (M , G) (N , D) -> (X : Nat) ->
    A (M , (G -+ X)) (N , (D -+ X))
  wkns al [] = al
  wkns al (X -, <>) = wkn (wkns al X)

  act : forall {M G N D l d} -> Term M G l d -> A (M , G) (N , D) -> Term N D lib d
  actk : forall {M G N D} -> Term M G ess chk -> A (M , G) (N , D) -> Term N D ess chk
  actz : forall {M G N D}{X : Nat} -> All (\ _ -> Term M G lib syn) X ->
                         A (M , G) (N , D) -> All (\ _ -> Term N D lib syn) X
  actk (atom a)    al = atom a
  actk (cons s t)  al = cons (act s al) (act t al)
  actk (abst t)    al = abst (act t (wkn al))
  act {l = ess}{d = chk} k al = essl (actk k al)
  act (vari i)    al = hit i al
  act (elim e s)  al = act e al $ act s al
  act (essl t)    al = act t al
  act (thnk n)    al = [ act n al ]
  act (x ?- ez)    al = met x al (actz ez al)
  act (t :: T)    al = act t al :: act T al
  actz []         al = []
  actz (ez -, e)  al = actz ez al -, act e al

  actzAll : forall {M G N D}{n : Nat}(ez : All (\ _ -> Term M G lib syn) n)
              (al : A (M , G) (N , D)) -> actz ez al == all (\ e -> act e al) ez
  actzAll []        al = refl
  actzAll (ez -, e) al = _-,_ $= actzAll ez al =$= refl

  actThunk : forall {M G N D}(e : Term M G lib syn)(al : A (M , G) (N , D)) ->
    act [ e ] al == [ act e al ]
  actThunk (essl n) al = refl
  actThunk (t :: T) al = refl

record ObjAct (N : Bwd Nat)(A : Nat -> Nat -> Set) : Set where
  field
    objHit : forall {G D}(i : <> <- G)(al : A G D) -> Term N D lib syn
    objWkn : forall {G D}(al : A G D) -> A (G -, <>) (D -, <>)

module _ (A : Bwd Nat -> Nat -> Nat -> Set)(o : forall {N} -> ObjAct N (A N)) where
  open module POLYOBJACT {N} = ObjAct (o {N})
  open Act

  ThinA : Bwd Nat * Nat -> Bwd Nat * Nat -> Set
  ThinA (M , G) (N , D) = (M <= N) * A N G D
  
  objAct : Act ThinA
  hit objAct i (_ , al) = objHit i al
  met objAct x (th , al) ez = (x -< th) ?- ez
  wkn objAct (th , al) = th , objWkn al
  oiAct : forall {M G D l d} -> Term M G l d -> A M G D -> Term M D lib d
  oiAct t al = act objAct t (oi , al)

module _ where
  open ObjAct
  OBJTHIN : forall {N} -> ObjAct N _<=_
  objHit OBJTHIN i th = # (i -< th)
  objWkn OBJTHIN = _su

  _^_ = oiAct _ OBJTHIN
  THIN = objAct _ OBJTHIN
  open Act THIN
  _^^_ = act

module _ where
  open ObjAct

  [_!_]/_ : Bwd Nat -> Nat ->  Nat -> Set
  [ N ! G ]/ D = All (\ _ -> Term N D lib syn) G

  wksb : forall {G N D} -> [ N ! G ]/ D -> [ N ! G -, <> ]/ D -, <>
  wksb sg = all (_^ (oi no)) sg -, # (oe su)

  idsb : forall {G N} ->  [ N ! G ]/ G
  idsb {[]}      = []
  idsb {G -, <>} = wksb idsb

  OBJSBST : forall {N} -> ObjAct N ([_!_]/_ N)
  objHit OBJSBST = project
  objWkn OBJSBST = wksb

  _/_ = oiAct _ OBJSBST
  SBST = objAct _ OBJSBST
  open Act SBST
  _//_ = act

module _ where
  open Act

  _%[_!_] : Bwd Nat -> Bwd Nat -> Nat -> Set
  M %[ N ! D ] = All (\ X -> Term N (D -+ X) lib chk) M

  wkin : forall {M N D} -> M %[ N ! D ] -> M %[ N ! D -, <> ]
  wkin = all (\ {n} t -> t ^ ((oi no) ^+ (oi {S = n})))

  idin : forall {M G} -> M %[ M ! G ]
  idin {[]}     = []
  idin {M -, X} =
    all (\ {X} t -> t ^^ ((oi no) , oi)) idin -,
    ((oe su) ?- all (_^ thinr _ oi) idsb)

  Inst : Bwd Nat * Nat -> Bwd Nat * Nat -> Set
  Inst (M , G) (N , D) = (M %[ N ! D ]) * ([ N ! G ]/ D)

  INST : Act Inst
  hit INST i (xi , sg) = project i sg
  met INST x (xi , sg) ez = project x xi / (idsb :+ ez)
  wkn INST (xi , sg) = wkin xi , wksb sg

  _%%_ = act INST

  _%_ : forall {M N G l d} -> Term M G l d -> M %[ N ! G ] -> Term N G lib d
  t % xi = t %% (xi , idsb)

  idi : forall {M G} -> Inst (M , G) (M , G)
  idi = idin , idsb
