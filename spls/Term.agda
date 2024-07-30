module Term where

open import String

open import Eq
open import Fun
open import Basics
open import Cats
open import Bwd
open import Thin
open import Atom
open import All
open import Pat


------------------------------------------------------------------------------
-- QUADRANTS AND TERMS
------------------------------------------------------------------------------

data Lib : Set where ess lib : Lib
data Dir : Set where chk syn : Dir

Meta = Nat * Pat []

data Term (M : Meta)(G : Nat) : Lib -> Dir -> Set where
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
  _?-_ : forall {D}(x : D <P- snd M) ->
         All (\ _ -> Term M G lib syn) D              -> Term M G lib chk
  mets : <> <- fst M                                  -> Term M G ess syn

pattern !_ a     = essl (atom a)
pattern _&_ s t  = essl (cons s t)
pattern \\_ t    = essl (abst t)
pattern #_ i     = essl (vari i)
pattern _$_ e s  = essl (elim e s)
infixr 60 !_ #_
infixl 50 _$_
infixr 40 _&_ \\_
infixr 30 _?-_


------------------------------------------------------------------------------
-- NO CONFUSION
------------------------------------------------------------------------------

TermNoConf : forall {M G l d}(t0 t1 : Term M G l d) -> Set -> Set
TermNoConf (atom a0)                     (atom a1) P = a0 == a1 -> P
TermNoConf (cons s0 t0)               (cons s1 t1) P = s0 == s1 -> t0 == t1 -> P
TermNoConf (abst t0)                     (abst t1) P = t0 == t1 -> P
TermNoConf (vari i0)                     (vari i1) P = i0 == i1 -> P
TermNoConf (elim e0 s0)               (elim e1 s1) P = e0 == e1 -> s0 == s1 -> P
TermNoConf (essl t0)                     (essl t1) P = t0 == t1 -> P
TermNoConf (thnk n0)                     (thnk n1) P = n0 == n1 -> P
TermNoConf (t0 :: T0)                   (t1 :: T1) P = t0 == t1 -> T0 == T1 -> P
TermNoConf (_?-_ {n0} x0 ez0)   (_?-_ {n1} x1 ez1) P = Pi (n0 == n1) \ { refl -> x0 == x1 -> ez0 == ez1 -> P }
TermNoConf (mets i)                       (mets j) P = i == j -> P
TermNoConf _ _ P = One

termNoConf : forall {M G l d}{t0 t1 : Term M G l d} -> t0 == t1 ->
  {P : Set} -> TermNoConf t0 t1 P -> P
termNoConf {t0 = atom a}   refl p = p refl
termNoConf {t0 = cons s t} refl p = p refl refl
termNoConf {t0 = abst t}   refl p = p refl
termNoConf {t0 = vari i}   refl p = p refl
termNoConf {t0 = elim e s} refl p = p refl refl
termNoConf {t0 = essl t}   refl p = p refl
termNoConf {t0 = thnk n}   refl p = p refl
termNoConf {t0 = t :: T}   refl p = p refl refl
termNoConf {t0 = x ?- ez}  refl p = p refl refl refl
termNoConf {t0 = mets i}   refl p = p refl


------------------------------------------------------------------------------
-- SMART EMBEDDINGS
------------------------------------------------------------------------------

[_] : forall {M G} -> Term M G lib syn -> Term M G lib chk
[ essl n ] = thnk n
[ t :: T ] = t

essTo : forall l {M G} -> Term M G ess syn -> Term M G l syn
essTo ess e = e
essTo lib e = essl e

toLib : forall l d {M G} -> Term M G l syn -> Term M G lib d
toLib ess chk n = thnk n
toLib ess syn n = essl n
toLib lib chk e = [ e ]
toLib lib syn e = e

trgLemma : forall l {M G}(e : Term M G l syn) ->
  toLib l chk e == [ toLib l syn e ]
trgLemma ess e = refl
trgLemma lib e = refl

toLibLemma : forall l d {M G}(n : Term M G ess syn) ->
  toLib l d (essTo l n) == toLib ess d n
toLibLemma ess chk n = refl
toLibLemma ess syn n = refl
toLibLemma lib chk n = refl
toLibLemma lib syn n = refl


------------------------------------------------------------------------------
-- ENVIRONMENTS
------------------------------------------------------------------------------

data Env (M : Meta){G : Nat} : Pat G -> Set where
  !!!_ : (a : Atom) -> Env M (!!! a)
  _&&&_ : {p q : Pat G} -> Env M p -> Env M q -> Env M (p &&& q)
  \\\_ : {q : Pat (G -, <>)} -> Env M q -> Env M (\\\ q)
  ??? : forall {X : Nat}{x}{th : X <= G} ->
         Term M X lib chk -> Env M (??? x th)

proje : forall D {M G}{p : Pat G}{X} -> X <P- p -> Env M (D ,P p) -> 
         Term M (D -+ X) lib chk
proje D ???     (??? t)   = t
proje D (car x) (o &&& _) = proje D x o
proje D (cdr x) (_ &&& o) = proje D x o
proje D (\\\ x) (\\\ o)   = proje D x o


------------------------------------------------------------------------------
-- STRINGING ALONG
------------------------------------------------------------------------------

_??-_ : forall {M ga}(x : String) -> let p = snd M in
         {prf : So (schemIsIn x p)} ->
         let de , v = schemVar x p prf in
         All (\ _ -> Term M ga lib syn) de -> Term M ga lib chk
_??-_ {_ , p} x {prf} sg with schemIsIn x p | schemVar x p
_??-_ {_ , p} x {()} sg | #0 | f
_??-_ {_ , p} x {prf} sg | #1 | f 
  = let de , v = f prf in v ?- sg
