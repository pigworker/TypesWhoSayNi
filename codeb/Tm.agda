module Tm where

open import Basics
open import Atom
open import Bwd
open import Thin {One}

data Dir : Set where chk syn : Dir

data Tm (ga : Bwd One) : Dir -> Set
Chk Syn : Bwd One -> Set
Chk ga = Tm ga chk
Syn ga = Tm ga syn

data Tm ga where
  [_]  : Syn ga -> Chk ga
  atom : Atom -> Null ga -> Chk ga
  cons : (Chk ^*^ Chk) ga -> Chk ga
  abst : Scope Chk <> ga -> Chk ga
  ra   : (Chk ^*^ Chk) ga -> Syn ga
  va   : Sole <> ga -> Syn ga
  el   : (Syn ^*^ Chk) ga -> Syn ga

mT = \ d ga -> Tm ga d

data DeB {ga} : forall {d} -> mT d ^^ ga -> Set where
  [_]  : {e : Syn ^^ ga} ->
         DeB e -> DeB ([_] ^$ e)
  atom : (a : Atom) ->
         DeB (atom a null ^ noth)
  cons : {s t : Chk ^^ ga}{st : (Chk ^*^ Chk) ^^ ga} ->
         DeB s -> DeB t -> Pair s t st ->
         DeB (cons ^$ st)
  kk   : forall {t : Chk ^^ ga} ->
         DeB t -> DeB (abst ^$ (kk ^$ t))
  ll   : forall {de}{t : Chk (de -, <>)}{th : de <= ga} ->
         DeB (t ^ (th -, <>)) -> DeB (abst (ll t) ^ th)
  ra   : {t T : Chk ^^ ga}{tT : (Chk ^*^ Chk) ^^ ga} ->
         DeB t -> DeB T -> Pair t T tT ->
         DeB (ra ^$ tT)
  va   : (i : ([] -, <>) <= ga) ->
         DeB (va sole ^ i)
  el   : {e : Syn ^^ ga}{s : Chk ^^ ga}{es : (Syn ^*^ Chk) ^^ ga} ->
         DeB e -> DeB s -> Pair e s es ->
         DeB (el ^$ es)

deB : forall {de ga d}(t : Tm de d)(th : de <= ga) -> DeB (t ^ th)
deB [ e ]                th = [ deB e th ]
deB (atom a null)        th rewrite nothU th noth = atom a
deB (cons (s <^ c ^> t)) th
  with lcov c -<- th | mkTri (lcov c) th
     | rcov c -<- th | mkTri (rcov c) th
...  | lth | lv | rth | rv
  = cons (deB s lth) (deB t rth) (mkPair s t lv c rv)
deB (abst (ll t))        th = ll (deB t (th -, <>))
deB (abst (kk t))        th = kk (deB t th)
deB (ra (t <^ c ^> T))   th
  with lcov c -<- th | mkTri (lcov c) th
     | rcov c -<- th | mkTri (rcov c) th
...  | lth | lv | rth | rv
  = ra (deB t lth) (deB T rth) (mkPair t T lv c rv)
deB (va sole)            th = va th
deB (el (e <^ c ^> s))   th
  with lcov c -<- th | mkTri (lcov c) th
     | rcov c -<- th | mkTri (rcov c) th
...  | lth | lv | rth | rv
  = el (deB e lth) (deB s rth) (mkPair e s lv c rv)

deB^ : forall {ga d}(t : (\ ga -> Tm ga d) ^^ ga) -> DeB t
deB^ (t ^ th) = deB t th

_=>_ : Bwd One -> Bwd One -> Set
ga => de = Env (\ _ -> Syn ^^ de) ga

sbwk : forall {ga de} -> ga => de -> (ga -, <>) => (de -, <>)
sbwk sg = env (_^^^ <>) sg -, (va sole ^ (noth -, <>))

sbst : forall {d ga de} -> Tm ga d -> ga => de -> (\ de -> Tm de d) ^^ de
sbst [ e ] sg = [_] ^$ sbst e sg
sbst (atom a null) sg = atom a null ^ noth
sbst (cons (s <^ c ^> t)) sg =
  cons ^$ pair (sbst s (lcov c <? sg) , sbst t (rcov c <? sg))
sbst (abst (ll t)) sg = abst ^$ sco (sbst t (sbwk sg))
sbst (abst (kk t)) sg = abst ^$ (kk ^$ (sbst t sg))
sbst (ra (t <^ c ^> T)) sg =
  ra ^$ pair (sbst t (lcov c <? sg) , sbst T (rcov c <? sg))
sbst (va sole) (_ -, e) = e
sbst (el (e <^ c ^> s)) sg =
  el ^$ pair (sbst e (lcov c <? sg) , sbst s (rcov c <? sg))

sbst^ : forall {d ga de} -> mT d ^^ ga -> ga => de -> mT d ^^ de
sbst^ (t ^ th) sg = sbst t (th <? sg)

data Sbst {ga de}(sg : ga => de)
  : forall {d} -> mT d ^^ ga -> mT d ^^ de -> Set where
  [_] : forall {e : Syn ^^ ga}{e' : Syn ^^ de} ->
    Sbst sg e e' -> Sbst sg ([_] ^$ e) ([_] ^$ e')
  atom : forall a -> Sbst sg (atom a null ^ noth) (atom a null ^ noth)
  cons : forall {s s' t t' st st'} ->
    Pair s t st -> Sbst sg s s' -> Sbst sg t t' -> Pair s' t' st' ->
    Sbst sg (cons ^$ st) (cons ^$ st')
  kk : forall {t t'} ->
    Sbst sg t t' -> Sbst sg (abst ^$ (kk ^$ t)) (abst ^$ (kk ^$ t'))
  ll : forall {ga' de'}
       {t : Chk (ga' -, <>)}{th : ga' <= ga}
       {t' : Chk (de' -, <>)}{th' : de' <= de} ->
       Sbst (sbwk sg) (t ^ (th -, <>)) (t' ^ (th' -, <>)) ->
       Sbst sg (abst (ll t) ^ th) (abst (ll t') ^ th')
  ra : forall {t t' T T' tT tT'} ->
    Pair t T tT -> Sbst sg t t' -> Sbst sg T T' -> Pair t' T' tT' ->
    Sbst sg (ra ^$ tT) (ra ^$ tT')
  va : forall {i t} -> (i <? sg) == ([] -, t) ->
    Sbst sg (va sole ^ i) t
  el : forall {e e' s s' es es'} ->
    Pair e s es -> Sbst sg e e' -> Sbst sg s s' -> Pair e' s' es' ->
    Sbst sg (el ^$ es) (el ^$ es')

pairInj : forall {S T}{ga}{s0 s1 : S ^^ ga}{t0 t1 : T ^^ ga}
  {st : (S ^*^ T) ^^ ga} ->
  Pair s0 t0 st -> Pair s1 t1 st -> (s0 == s1) * (t0 == t1)
pairInj (mkPair s0 t0 lv c rv) (mkPair .s0 .t0 lu .c ru)
  rewrite triFun lv lu | triFun rv ru = refl , refl

pairFun : forall {S T}{ga}{s : S ^^ ga}{t : T ^^ ga}
  {st0 st1 : (S ^*^ T) ^^ ga} ->
  Pair s t st0 -> Pair s t st1 -> st0 == st1
pairFun (mkPair s t lv c rv) (mkPair .s .t lu b ru)
  with copQ (cop _ lv c rv) (cop _ lu b ru)
... | refl = refl

sbstFun : forall {ga de}{sg : ga => de}{d}{t : mT d ^^ ga}{t0 t1 : mT d ^^ de} ->
  Sbst sg t t0 -> Sbst sg t t1 -> t0 == t1
sbstFun [ r0 ] [ r1 ] with sbstFun r0 r1
... | refl = refl
sbstFun (atom a) (atom .a) = refl
sbstFun (cons p0 r0 r1 p1) (cons p2 r2 r3 p3) with pairInj p0 p2
... | refl , refl with sbstFun r0 r2 | sbstFun r1 r3
... | refl | refl with pairFun p1 p3
... | refl = refl
sbstFun (kk r0) (kk r1) with sbstFun r0 r1
... | refl = refl
sbstFun (ll r0) (ll r1) with sbstFun r0 r1
... | refl = refl
sbstFun (ra p0 r0 r1 p1) (ra p2 r2 r3 p3) with pairInj p0 p2
... | refl , refl with sbstFun r0 r2 | sbstFun r1 r3
... | refl | refl with pairFun p1 p3
... | refl = refl
sbstFun (va x) (va y) with _ =< x ]= _ =[ y >= _ [QED]
sbstFun (va x) (va y) | refl = refl
sbstFun (el p0 r0 r1 p1) (el p2 r2 r3 p3) with pairInj p0 p2
... | refl , refl with sbstFun r0 r2 | sbstFun r1 r3
... | refl | refl with pairFun p1 p3
... | refl = refl

mylemma : forall {de de0} {th'' : de0 <= de} {de'}
         {th : de0 <= de'} {ph : de' <= de} {dei} {ps : dei <= de} ->
       Tri th ph th'' ->
       Sg (dei <= de0) (\ th' -> Tri th' th'' ps) ->
       Sg (dei <= de') (\ th' -> Tri th' ph ps)
mylemma v (th0 , v') = let _ , _ , u = assocTri' v' v in _ , u

sbstRelv : forall {ga' ga de' de d}{th : ga' <= ga}{ph : de' <= de}
  {t : Tm ga' d}{sg : ga => de}{t' : Tm de' d} ->
  Sbst sg (t ^ th) (t' ^ ph) ->
  forall (i : ([] -, <>) <= ga'){dei}{s : Syn dei}{ps : dei <= de} ->
  (i <? (th <? sg)) == ([] -, (s ^ ps))  ->
  Sg (dei <= de') \ th' -> Tri th' ph ps
pairRelv : forall {ga de d0 d1}
  {s : mT d0 ^^ ga}{s' : mT d0 ^^ de}
  {t : mT d1 ^^ ga}{t' : mT d1 ^^ de}
  {st : (mT d0 ^*^ mT d1) ^^ ga}{st' : (mT d0 ^*^ mT d1) ^^ de}
  (sg : ga => de) ->
  Pair s t st -> Sbst sg s s' -> Sbst sg t t' -> Pair s' t' st' ->
  forall (i : ([] -, <>) <= support st){dei}{s : Syn dei}{ps : dei <= de} ->
  (i <? (thinning st <? sg)) == ([] -, (s ^ ps))  ->
  Sg _ \ th' -> Tri th' (thinning st') ps
pairRelv sg (mkPair s0 t0 lv c rv) s t (mkPair s1 t1 lu b ru) i q with cover1 i c
pairRelv sg (mkPair s0 t0 lv c rv) s t (mkPair s1 t1 lu b ru) i q
  | inl (j , v) with cossaTri v lv | sbstRelv s j
... | th0 , v0 , v1 | hs rewrite compSel v0 sg | compSel v1 sg
    = mylemma lu (hs q)
pairRelv sg (mkPair s0 t0 lv c rv) s t (mkPair s1 t1 lu b ru) i q
  | inr (j , v) with cossaTri v rv | sbstRelv t j
... | th0 , v0 , v1 | hs rewrite compSel v0 sg | compSel v1 sg
    = mylemma ru (hs q)
sbstRelv [ e ] i q = sbstRelv e i q
sbstRelv (atom a) () q
sbstRelv (cons p s' t' p') i q = pairRelv _ p s' t' p' i q
sbstRelv (kk t) i q = sbstRelv t i q
sbstRelv {th = th}{sg = sg} (ll t) i q with sbstRelv t (i -^ <>)
... | ht rewrite naturalSelection (_^^^ <>) th sg
               | naturalSelection (_^^^ <>) i (th <? sg)
               | q
               = help (ht refl)
  where
    help : forall {de dei} {ps : dei <= de} {de'} {ph : de' <= de} ->
       Sg (dei <= (de' -, <>)) (\ th' -> Tri th' (ph -, <>) (ps -^ <>)) ->
       Sg (dei <= de') (\ th' -> Tri th' ph ps)
    help (.(_ -^ <>) , (v -^, <>)) = _ , v
sbstRelv (ra p t' T' p') i q = pairRelv _ p t' T' p' i q
sbstRelv {th = th} {sg = sg} (va x) ([] -, <>) q with th <? sg
sbstRelv {th = th} {sg = sg} (va refl) ([] -, <>) refl | .([] -, (_ ^ _)) =
  _ , idTri _
sbstRelv (va x) (() -^ <>) q
sbstRelv (el p e' s' p') i q = pairRelv _ p e' s' p' i q

mkSbst' : forall {ga' ga de d}(t : Tm ga' d)(th : ga' <= ga)(sg : ga => de) ->
  Sbst sg (t ^ th) (sbst t (th <? sg))
mkSbst' [ e ] th sg = [ mkSbst' e th sg ]
mkSbst' (atom a null) th sg rewrite nothU th noth = atom a
mkSbst' (cons (s <^ c ^> t)) th sg 
 with mkTri (lcov c) th | mkSbst' s (lcov c -<- th) sg
    | mkTri (rcov c) th | mkSbst' t (rcov c -<- th) sg
... | lv | s' | rv | t'
  rewrite compSel lv sg | compSel rv sg
  = cons (mkPair _ _ lv c rv) s' t' (pairPair _ _)
mkSbst' (abst (ll t)) th sg with mkSbst' t (th -, <>) (sbwk sg)
... | ht with sbstRelv ht (noth -, <>) (rf _-,_ =$= noSel (th <? env _ sg) =$= refl)
... | ph , v rewrite naturalSelection (_^^^ <>) th sg
    = help (sbst t (sbwk (th <? sg))) ph v ht where
  help :  forall {t} (w : Chk ^^ (_ -, <>))
         (ph : ([] -, <>) <= support w) ->
       Tri ph (thinning w) (noth -, <>) ->
       Sbst (sbwk sg) (t ^ (th -, <>)) w ->
       Sbst sg (abst (ll t) ^ th)
       (abst (thing (sco w)) ^ thinning (sco w))
  help (t' ^ .(_ -, <>)) .(_ -, <>) (v -, <>) h = ll h
mkSbst' (abst (kk t)) th sg = kk (mkSbst' t th sg)
mkSbst' (ra (t <^ c ^> T)) th sg
 with mkTri (lcov c) th | mkSbst' t (lcov c -<- th) sg
    | mkTri (rcov c) th | mkSbst' T (rcov c -<- th) sg
... | lv | t' | rv | T'
  rewrite compSel lv sg | compSel rv sg
  = ra (mkPair _ _ lv c rv) t' T' (pairPair _ _)
mkSbst' (va sole) th sg with sel1 th sg
... | e , q = va (
  (th <? sg)
    =[ q >=
  ([] -, e)
    =< rf ([] -,_) =$= (rf (sbst (va sole)) =$= q) ]=
  ([] -, sbst (va sole) (th <? sg))
    [QED])
mkSbst' (el (e <^ c ^> s)) th sg
 with mkTri (lcov c) th | mkSbst' e (lcov c -<- th) sg
    | mkTri (rcov c) th | mkSbst' s (rcov c -<- th) sg
... | lv | e' | rv | s'
  rewrite compSel lv sg | compSel rv sg
  = el (mkPair _ _ lv c rv) e' s' (pairPair _ _)

mkSbst : forall {ga de d}(t : mT d ^^ ga)(sg : ga => de) ->
  Sbst sg t (sbst^ t sg)
mkSbst (t ^ th) sg = mkSbst' t th sg

thsb : forall {ga de} -> ga <= de -> ga => de
thsb [] = []
thsb (th -, x) = sbwk (thsb th)
thsb (th -^ x) = env (_^^^ <>) (thsb th)

idsb : forall {ga} -> ga => ga
idsb = thsb idth

selthsbLemma : forall {ga0 ga1 ga2}
  {th : ga0 <= ga1}{ph : ga1 <= ga2}{ps : ga0 <= ga2} ->
  Tri th ph ps ->
  (th <? thsb ph) == thsb ps
selthsbLemma [] = refl
selthsbLemma {th = th -, <>}{ph = ph -, <>} (v -, <>)
  rewrite naturalSelection (_^^^ <>) th (thsb ph)
        | selthsbLemma v
        = refl
selthsbLemma {th = th -^ <>}{ph = ph -, <>} (v -^, <>)
  rewrite naturalSelection (_^^^ <>) th (thsb ph)
        | selthsbLemma v
        = refl
selthsbLemma {th = th}{ph = ph -^ <>} (v -^ <>)
  rewrite naturalSelection (_^^^ <>) th (thsb ph)
        | selthsbLemma v
        = refl

nothLemma : forall {de}(x : [] <= de) -> thsb x == []
nothLemma [] = refl
nothLemma (x -^ <>) rewrite nothLemma x = refl

soleLemma : forall {de}(x : ([] -, <>) <= de) -> thsb x == ([] -, (va sole ^ x))
soleLemma (x -, .<>) rewrite nothU noth x | nothLemma x = refl
soleLemma (x -^ <>) rewrite soleLemma x = refl

thsbLemma' : forall {d ga de}
  {t : mT d ^^ ga} ->
  DeB t -> (th : ga <= de) -> Sbst (thsb th) t (t ^< th)
thsbLemma' [ de ] th = [ thsbLemma' de th ] 
thsbLemma' (atom a) th rewrite nothU (noth -<- th) noth = atom a
thsbLemma' (cons ds dt p) th =
  cons p (thsbLemma' ds th) (thsbLemma' dt th) (pairThin p th)
thsbLemma' (kk dt) th = kk (thsbLemma' dt th)
thsbLemma' (ll dt) th = ll (thsbLemma' dt (th -, <>))
thsbLemma' (ra dt dT p) th =
  ra p (thsbLemma' dt th) (thsbLemma' dT th) (pairThin p th)
thsbLemma' (va i) th = va (
  (i <? thsb th)
    =[ selthsbLemma (mkTri i th) >=
  thsb (i -<- th)
    =[ soleLemma (i -<- th) >=
  ([] -, ((va sole ^ i) ^< th))
    [QED])
thsbLemma' (el de ds p) th =
  el p (thsbLemma' de th) (thsbLemma' ds th) (pairThin p th)

idsbLemma : forall {d ga}(t : mT d ^^ ga) ->
  Sbst idsb t t
idsbLemma t with thsbLemma' (deB^ t) idth
... | h rewrite triFun (mkTri (thinning t) idth) (triId _) = h

_-$-_ : forall {ga0 ga1 ga2} -> ga0 => ga1 -> ga1 => ga2 -> ga0 => ga2
rh -$- sg = env (\ t -> sbst^ t sg) rh

sbshoogle : forall {ga de xi}(sg : ga => de)(th : de <= xi) ->
  env (_^^^ <>) (env (_^< th) sg) ==
  env (_^< (th -, <>)) (env (_^^^ <>) sg)
sbshoogle sg th = 
  env (_^^^ <>) (env (_^< th) sg)
    =[ envComp _ _ _ (\ _ -> refl) sg >=
  env (_^< (th -^ <>)) sg
    =< envComp _ _ _ (\ _ -> refl) sg ]=
  env (_^< (th -, <>)) (env (_^^^ <>) sg)
    [QED]

sbthLemma : forall {ga de d}{t : mT d ^^ ga}{sg : ga => de}{t' : mT d ^^ de} ->
  Sbst sg t t' -> forall {xi}(th : de <= xi) ->
  Sbst (env (\ e -> e ^< th) sg) t (t' ^< th)
sbthLemma [ e ] th = [ sbthLemma e th ]
sbthLemma (atom a) th rewrite nothU (noth -<- th) noth = atom a
sbthLemma (cons p s t p') th =
  cons p (sbthLemma s th) (sbthLemma t th) (pairThin p' th)
sbthLemma (kk t) th = kk (sbthLemma t th)
sbthLemma {sg = sg} (ll t) th = ll (sbthLemma t (th -, <>)
  [ rf (\ sg -> Sbst sg {chk})
    =$= (rf _-,_ =$= sym (sbshoogle sg th)
         =$= (rf (va sole ^_) =$= (rf (_-, <>) =$= nothU _ _)))
    =$= refl =$= refl >)
sbthLemma (ra p t T p') th =
  ra p (sbthLemma t th) (sbthLemma T th) (pairThin p' th)
sbthLemma {t = t ^ ph}{sg}{t'} (va x) i = va (
  (ph <? env (_^< i) sg)
    =[ naturalSelection (_^< i)  ph sg >=
  (env (_^< i) (ph <? sg))
    =[ rf (env (_^< i)) =$= x >=
  ([] -, (t' ^< i))
    [QED])
sbthLemma (el p e s p') th =
  el p (sbthLemma e th) (sbthLemma s th) (pairThin p' th)

sbwkLemma : forall {ga1 ga2}(e : Syn ^^ ga1)(sg : ga1 => ga2) ->
            (sbst^ e sg ^^^ <>) == sbst^ e (env (_^^^ <>) sg)
sbwkLemma e sg
  with sbst^ e sg | mkSbst e sg
     | sbst^ e (env (_^^^ <>) sg) | mkSbst e (env (_^^^ <>) sg)
... | (e0 ^ th) | r0 | e1 | r1 with sbthLemma r0 (idth -^ <>)
... | h = sbstFun (h [ rf (\ sg -> Sbst sg {syn})
        =$= envExt _ _ (\ { (f ^ ph) -> 
            rf (f ^_) =$= (rf (_-^ <>) =$= triFun (mkTri _ _) (triId _)) }) sg
        =$= refl
        =$= (rf (e0 ^_) =$= (rf (_-^ <>) =$= triFun (mkTri _ _) (triId _)))
        >) r1

cowkLemma : forall {ga0 ga1 ga2}(sg01 : ga0 => ga1)(sg12 : ga1 => ga2) ->
  (sbwk sg01 -$- sbwk sg12) == sbwk (sg01 -$- sg12)
cowkLemma sg01 sg02 = rf (_-, _) =$=
  env (\ t -> sbst^ t (sbwk sg02)) (env (_^^^ <>) sg01)
    =[ envComp _ _ _ (\ _ -> refl) sg01 >=
  env (\ t -> sbst^ t (env (_^^^ <>) sg02)) sg01
    =< envComp _ _ _ (\ e -> sbwkLemma e sg02) sg01 ]=
  env (_^^^ <>) (sg01 -$- sg02)
    [QED]

cosbLemma : forall {d ga0 ga1 ga2}
  {t0 : mT d ^^ ga0}{sg01 : ga0 => ga1}
  {t1 : mT d ^^ ga1}{sg12 : ga1 => ga2}{t2 : mT d ^^ ga2} ->
  Sbst sg01 t0 t1 -> Sbst sg12 t1 t2 -> Sbst (sg01 -$- sg12) t0 t2
cosbLemma [ r01 ] [ r12 ] = [ cosbLemma r01 r12 ]
cosbLemma (atom a) (atom .a) = atom a
cosbLemma (cons p0 s01 t01 p1) (cons p2 s12 t12 p3) with pairInj p1 p2
... | refl , refl with cosbLemma s01 s12 | cosbLemma t01 t12
... | s02 | t02 = cons p0 s02 t02 p3
cosbLemma (kk r01) (kk r12) = kk (cosbLemma r01 r12)
cosbLemma {sg01 = sg01}{sg12 = sg12} (ll r01) (ll r12) with cosbLemma r01 r12
... | r02 rewrite cowkLemma sg01 sg12 = ll r02
cosbLemma (ra p0 s01 t01 p1) (ra p2 s12 t12 p3) with pairInj p1 p2
... | refl , refl with cosbLemma s01 s12 | cosbLemma t01 t12
... | s02 | t02 = ra p0 s02 t02 p3
cosbLemma {t0 = va sole ^ i}{sg01}{t1}{sg12}{t2} (va x) r12 = va (
  (i <? env (\ t -> sbst^ t sg12) sg01)
    =[ naturalSelection _ i _ >=
  env (\ t -> sbst^ t sg12) (i <? sg01)
    =[ rf (env (\ t -> sbst^ t sg12)) =$= x >=
  ([] -, sbst^ t1 sg12)
    =[ rf ([] -,_) =$= sbstFun (mkSbst _ _) r12 >=
  ([] -, t2)
    [QED])
cosbLemma (el p0 s01 t01 p1) (el p2 s12 t12 p3) with pairInj p1 p2
... | refl , refl with cosbLemma s01 s12 | cosbLemma t01 t12
... | s02 | t02 = el p0 s02 t02 p3

