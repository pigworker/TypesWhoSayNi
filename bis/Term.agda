module Term where

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
  atom : (a : Atom) -> Env M (atom a)
  cons : {p q : Pat G} -> Env M p -> Env M q -> Env M (cons p q)
  abst : {q : Pat (G -, <>)} -> Env M q -> Env M (abst q)
  hole : {X : Nat}{th : X <= G} ->
         Term M X lib chk -> Env M (hole th)

proje : forall D {M G}{p : Pat G}{X} -> X <P- p -> Env M (D ,P p) -> 
         Term M (D -+ X) lib chk
proje D hole     (hole t)   = t
proje D (car x)  (cons o _) = proje D x o
proje D (cdr x)  (cons _ o) = proje D x o
proje D (abst x) (abst o)   = proje D x o

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
    acte {p = atom a}      (atom .a)  al = atom a
    acte {p = cons p q}    (cons D E) al = cons (acte D al) (acte E al)
    acte {p = abst q}      (abst E)   al = abst (acte E al)
    acte {p = hole {X} th} (hole t)   al = hole (act objAct t (refl , wks al X))

    projeActe : forall {Y X}{p : Pat X}(x : Y <P- p){M G D}
      (ts : Env M (G ,P p))(al : A M G D) ->
      proje D x (acte ts al) == act objAct (proje G x ts) (refl , wks al Y)
    projeActe hole     (hole t)    al = refl
    projeActe (car x)  (cons ts _) al = projeActe x ts al
    projeActe (cdr x)  (cons _ ts) al = projeActe x ts al
    projeActe (abst x) (abst ts)   al = projeActe x ts al


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

_%P_ : forall {D G M} ->
  (p : Pat G) -> Env M (D ,P p) -> Term M (D -+ G) lib chk
atom a   %P atom .a    = ! a
cons p q %P cons ss ts = (p %P ss) & (q %P ts)
abst q   %P abst ts    = \\ (q %P ts)
hole th  %P hole t = t ^ (oi ^+ th)
