module Term where

open import Eq
open import Basics
open import Cats
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

Pi : (S : Set)(T : S -> Set) -> Set
Pi S T = (x : S) -> T x

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



{-
thnkLemma : forall l {M G}(n : Term M G ess syn) ->
  toLib l chk (essTo l n) == thnk n
thnkLemma ess n = refl
thnkLemma lib n = refl

esslLemma : forall l {M G}(n : Term M G ess syn) ->
  toLib l syn (essTo l n) == essl n
esslLemma ess n = refl
esslLemma lib n = refl
-}

record Act (A : Bwd Nat * Nat -> Bwd Nat * Nat -> Set) : Set where
  field
    trg : Lib
    hit : forall {M G N D} -> (<> <- G) -> A (M , G) (N , D) -> Term N D trg syn
    met : forall {M G N D X} -> (X <- M) -> A (M , G) (N , D) ->
            All (\ _ -> Term N D lib syn) X -> Term N D lib chk
    wkn : forall {M G N D} -> A (M , G) (N , D) -> A (M , (G -, <>)) (N , (D -, <>))

  wkns : forall {M G N D} -> A (M , G) (N , D) -> (X : Nat) ->
    A (M , (G -+ X)) (N , (D -+ X))
  wkns al [] = al
  wkns al (X -, <>) = wkn (wkns al X)

  act : forall {M G N D d} -> Term M G lib d -> A (M , G) (N , D) -> Term N D lib d
  actk : forall {M G N D} -> Term M G ess chk -> A (M , G) (N , D) -> Term N D ess chk
  actn : forall {M G N D} -> Term M G ess syn -> A (M , G) (N , D) -> Term N D trg syn
  actz : forall {M G N D}{X : Nat} -> All (\ _ -> Term M G lib syn) X ->
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
  actz []         al = []
  actz (ez -, e)  al = actz ez al -, act e al

  actzAll : forall {M G N D}{n : Nat}(ez : All (\ _ -> Term M G lib syn) n)
              (al : A (M , G) (N , D)) -> actz ez al == all (\ e -> act e al) ez
  actzAll []        al = refl
  actzAll (ez -, e) al = _-,_ $= actzAll ez al =$= refl

  actThunk : forall {M G N D}(e : Term M G lib syn)(al : A (M , G) (N , D)) ->
    act [ e ] al == [ act e al ]
  actThunk (essl n) al = trgLemma trg (actn n al)
  actThunk (t :: T) al = refl

record ObjAct (trg : Lib)(N : Bwd Nat)(A : Nat -> Nat -> Set) : Set where
  field
    objHit : forall {G D}(i : <> <- G)(al : A G D) -> Term N D trg syn
    objWkn : forall {G D}(al : A G D) -> A (G -, <>) (D -, <>)

module _ {l}(A : Bwd Nat -> Nat -> Nat -> Set)(o : forall {N} -> ObjAct l N (A N)) where
  open module POLYOBJACT {N} = ObjAct (o {N})
  open Act

  ThinA : Bwd Nat * Nat -> Bwd Nat * Nat -> Set
  ThinA (M , G) (N , D) = (M <= N) * A N G D
  
  objAct : Act ThinA
  trg objAct = l
  hit objAct i (_ , al) = objHit i al
  met objAct x (th , al) ez = (x -< th) ?- ez
  wkn objAct (th , al) = th , objWkn al

module _ where
  open ObjAct
  
  OBJTHIN : forall {N} -> ObjAct ess N _<=_
  objHit OBJTHIN i th = vari (i -< th)
  objWkn OBJTHIN = _su

  THIN = objAct _ OBJTHIN
  open Act THIN

  open Cat (OPE {Nat})

  _^^_ = act

  _^_ : forall {l d M G D}(t : Term M G l d)(th : G <= D) -> Term M D l d
  _^_ {ess} {chk} t th = actk t (oi , th)
  _^_ {ess} {syn} t th = actn t (oi , th)
  _^_ {lib} {d}   t th = t ^^ (oi , th)

  Dep : forall {l d M D G}(th : D <= G)(t : Term M G l d) -> Set
  Dep th t = Sg _ \ t' -> t == (t' ^ th)
  dep? : forall {l d M D G}(th : D <= G)(t : Term M G l d) -> Dec (Dep th t)
  depz? : forall {M D G}{X : Nat}(th : D <= G)(ez : All (\ _ -> Term M G lib syn) X) ->
    Dec (Sg _ \ ez' -> ez == actz ez' (oi , th))
  dep? th (atom a)   = #1 , (atom a , refl)
  dep? th (cons s t) with dep? th s | dep? th t
  dep? th (cons s t) | #0 , bad | _ = #0 ,
    \ { (atom _ , ()) ; (cons s' t' , refl) -> bad (s' , refl) ; (abst _ , ()) }
  dep? th (cons s t) | #1 , _ | #0 , bad = #0 ,
    \ { (atom _ , ()) ; (cons s' t' , refl) -> bad (t' , refl) ; (abst _ , ()) }
  dep? th (cons .(s' ^ th) .(t' ^ th)) | #1 , (s' , refl) | #1 , (t' , refl)
    = #1 , (cons s' t' , refl)
  dep? th (abst t)   with dep? (th su) t
  dep? th (abst t) | #0 , bad = #0 ,
    \ { (atom _ , ()) ; (cons _ _ , ()) ; (abst t' , refl) -> bad (t' , refl) }
  dep? th (abst .(t' ^ (th su))) | #1 , (t' , refl) = #1 , (abst t' , refl)
  dep? th (vari i)   with thick? th i
  dep? th (vari i) | #0 , bad = #0 ,
    \ { (vari i , refl) -> bad (i , refl) ; (elim _ _ , ()) }
  dep? th (vari .(j -< th)) | #1 , (j , refl) = #1 , (vari j , refl)
  dep? th (elim e s) with dep? th e | dep? th s
  dep? th (elim e s) | #0 , bad | _ = #0 ,
    \ { (vari _ , ()) ; (elim e' s' , refl) -> bad (e' , refl) }
  dep? th (elim e s) | #1 , _ | #0 , bad = #0 ,
    \ { (vari _ , ()) ; (elim e' s' , refl) -> bad (s' , refl) }
  dep? th (elim .(e' ^ th) .(s' ^ th)) | #1 , (e' , refl) | #1 , (s' , refl)
    = #1 , (elim e' s' , refl)
  dep? th (essl t)   with dep? th t
  dep? {d = chk} th (essl t) | #0 , bad = #0 ,
    \ { (essl k' , refl) -> bad (k' , refl) ; (thnk _ , ()) ; ((_ ?- _) , ()) }
  dep? {d = syn} th (essl t) | #0 , bad = #0 ,
    \ { (essl n' , refl) -> bad (n' , refl) ; ((_ :: _) , ()) }
  dep? {d = chk} th (essl .(t' ^ th)) | #1 , (t' , refl) = #1 , (essl t' , refl)
  dep? {d = syn} th (essl .(t' ^ th)) | #1 , (t' , refl) = #1 , (essl t' , refl)
  dep? th (thnk n)   with dep? th n
  dep? th (thnk n) | #0 , bad = #0 ,
    \ { (essl _ , ()) ; (thnk n' , refl) -> bad (n' , refl) ; ((_ ?- _) , ()) }
  dep? th (thnk .(n' ^ th)) | #1 , (n' , refl) = #1 , (thnk n' , refl)
  dep? th (t :: T) with dep? th t | dep? th T
  dep? th (t :: T) | #0 , bad | _ = #0 ,
    \ { (essl _ , ()) ; ((t' :: T') , refl) -> bad (t' , refl) }
  dep? th (t :: T) | #1 , _ | #0 , bad = #0 ,
    \ { (essl _ , ()) ; ((t' :: T') , refl) -> bad (T' , refl) }
  dep? th (.(t' ^ th) :: .(T' ^ th)) | #1 , (t' , refl) | #1 , (T' , refl) =
    #1 , ((t' :: T') , refl)
  dep? th (x ?- ez) with depz? th ez
  dep? th (x ?- ez) | #0 , bad = #0 ,
    \ { (essl _ , ()) ; (thnk _ , ()) ; ((x ?- ez') , refl) -> bad (ez' , refl) }
  dep? th (x ?- .(actz ez' (oi , th))) | #1 , (ez' , refl) =
    #1 , ((x ?- ez') , ((_?- _) $= sym (coidC x)))
  depz? th [] = #1 , ([] , refl)
  depz? th (ez -, e) with depz? th ez | dep? th e
  depz? th (ez -, e) | #0 , bad | _ = #0 , \ { ((ez' -, e') , refl) -> bad (ez' , refl) }
  depz? th (ez -, e) | #1 , _ | #0 , bad = #0 , \ { ((ez' -, e') , refl) -> bad (e' , refl) }
  depz? th (.(actz ez' (oi , th)) -, .(e' ^ th)) | #1 , (ez' , refl) | #1 , (e' , refl) =
    #1 , ((ez' -, e') , refl)

module _ where
  open ObjAct

  [_!_]/_ : Bwd Nat -> Nat ->  Nat -> Set
  [ N ! G ]/ D = All (\ _ -> Term N D lib syn) G

  wksb : forall {G N D} -> [ N ! G ]/ D -> [ N ! G -, <> ]/ D -, <>
  wksb sg = all (_^ (oi no)) sg -, # (oe su)

  idsb : forall {G N} ->  [ N ! G ]/ G
  idsb {[]}      = []
  idsb {G -, <>} = wksb idsb

  OBJSBST : forall {N} -> ObjAct lib N ([_!_]/_ N)
  objHit OBJSBST = project
  objWkn OBJSBST = wksb

  SBST = objAct _ OBJSBST
  open Act SBST
  
  _//_ = act

  _/_ : forall {l d M G D}(t : Term M G l d)(sg : [ M ! G ]/ D) -> Term M D lib d
  _/_ {ess} {chk} t sg = essl (actk t (oi , sg))
  _/_ {ess} {syn} t sg = actn t (oi , sg)
  _/_ {lib} {d}   t sg = t // (oi , sg)

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
  trg INST = lib
  hit INST i (xi , sg) = project i sg
  met INST x (xi , sg) ez = project x xi / (idsb :+ ez)
  wkn INST (xi , sg) = wkin xi , wksb sg

  _%%_ = act INST

  _%_ : forall {l d M N G} -> Term M G l d -> M %[ N ! G ] -> Term N G lib d
  _%_ {ess} {chk} t xi = essl (actk INST t (xi , idsb))
  _%_ {ess} {syn} t xi = actn INST t (xi , idsb)
  _%_ {lib} {d}   t xi = t %% (xi , idsb)

  idi : forall {M G} -> Inst (M , G) (M , G)
  idi = idin , idsb

