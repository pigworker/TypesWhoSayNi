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
  meta : forall {n}(x : n <- M) ->
         All (\ _ -> Term M G lib syn) n              -> Term M G ess chk
  --
  vari : (i : <> <- G)                                -> Term M G ess syn
  elim : (e : Term M G lib syn)(s : Term M G lib chk) -> Term M G ess syn
  --
  essl : {d : Dir}(t : Term M G ess d)                -> Term M G lib d
  thnk : (n : Term M G ess syn)                       -> Term M G lib chk
  radi : (k : Term M G ess chk)(T : Term M G lib chk) -> Term M G lib syn

pattern !_ a     = essl (atom a)
pattern _&_ s t  = essl (cons s t)
pattern \\_ t    = essl (abst t)
pattern #_ i     = essl (vari i)
pattern _$_ e s  = essl (elim e s)
pattern _%_ x ez = essl (meta x ez)
infixr 60 !_ #_
infixl 50 _$_
infixr 40 _&_ \\_
infixr 30 _%_

[_] : forall {M G} -> Term M G lib syn -> Term M G lib chk
[ essl n ]   = thnk n
[ radi k T ] = essl k

_::_ : forall {M G}(t T : Term M G lib chk) -> Term M G lib syn
essl k :: T = radi k T
thnk n :: T = essl n

upsilon : forall {M G}(t T : Term M G lib chk) -> [ t :: T ] == t
upsilon (essl t) T = refl
upsilon (thnk t) T = refl

record ObjAct (M : Bwd Nat)(A : Nat -> Nat -> Set) : Set where
  field
    hit : forall {G D} -> (<> <- G) -> A G D -> Term M D lib syn
    wkn : forall {G D} -> A G D -> A (G -, <>) (D -, <>)
    emp : A [] []
    
  act : forall {G D l d} -> Term M G l d -> A G D -> Term M D lib d
  actz : forall {G D}{n : Nat} -> All (\ _ -> Term M G lib syn) n ->
                         A G D -> All (\ _ -> Term M D lib syn) n
  act (atom a)    al = ! a
  act (cons s t)  al = act s al & act t al
  act (abst t)    al = \\ act t (wkn al)
  act (meta x ez) al = x % actz ez al
  act (vari i)    al = hit i al
  act (elim e s)  al = act e al $ act s al
  act (essl t)    al = act t al
  act (thnk n)    al = [ act n al ]
  act (radi k T)  al = act k al :: act T al
  actz []         al = []
  actz (ez -, e)  al = actz ez al -, act e al

  actzAll : forall {G D}{n : Nat}(ez : All (\ _ -> Term M G lib syn) n)
              (al : A G D) -> actz ez al == all (\ e -> act e al) ez
  actzAll []        al = refl
  actzAll (ez -, e) al = _-,_ $= actzAll ez al =$= refl

module _ where
  open ObjAct
  THIN : forall {M} -> ObjAct M _<=_
  hit THIN i th = # (i -< th)
  wkn THIN th = th su
  emp THIN    = ze

  _^_ : forall {M}{G D l d} -> Term M G l d -> G <= D -> Term M D lib d
  _^_ = act THIN

module _ where
  open ObjAct
  
  Sbst : Bwd Nat -> Nat -> Nat -> Set
  Sbst M G D = All (\ _ -> Term M D lib syn) G

  SBST : forall {M} -> ObjAct M (Sbst M)
  hit SBST = project
  wkn SBST sg = all (_^ (oi no)) sg -, # (oe su)
  emp SBST = []

  _/_ : forall {M}{G D l d} -> Term M G l d -> Sbst M G D -> Term M D lib d
  _/_ = act SBST

  ids : forall {M}{G} -> Sbst M G G
  ids {G = []}     = emp SBST
  ids {G = _ -, _} = wkn SBST ids

Inst : Bwd Nat -> Bwd Nat -> Nat -> Set
Inst M N G = All (\ m -> Term N (G -+ m) lib chk) M

wki : forall {M N G} -> Inst M N G -> Inst M N (G -, <>)
wki {G = G} xi = all (\ {n} t -> t ^ ((oi no) ^+ (oi {S = n}))) xi

_%/_ : forall {M N G l d} -> Term M G l d -> Inst M N G -> Term N G lib d
_%//_ : forall {M N G n} -> All {One} (\ _ -> Term M G lib syn) n ->
          Inst M N G -> All (\ _ -> Term N G lib syn) n
atom a    %/ xi = ! a
cons s t  %/ xi = (s %/ xi) & (t %/ xi)
abst t    %/ xi = \\ (t %/ wki xi)
meta x ez %/ xi = project x xi / (ids :+ (ez %// xi))
vari i    %/ xi = # i
elim e s  %/ xi = (e %/ xi) $ (s %/ xi)
essl t    %/ xi = t %/ xi
thnk n    %/ xi = [ n %/ xi ]
radi k T  %/ xi = (k %/ xi) :: (T %/ xi)
[]        %// xi = []
(ez -, e) %// xi = (ez %// xi) -, (e %/ xi)
