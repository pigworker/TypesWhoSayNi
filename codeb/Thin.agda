module Thin {X : Set} where

open import Basics
open import Bwd

data _<=_ : Bwd X -> Bwd X -> Set where
  [] : [] <= []
  _-,_ : forall {xz yz} ->
    xz <= yz -> forall x -> (xz -, x) <= (yz -, x)
  _-^_ : forall {xz yz} ->
    xz <= yz -> forall x ->  xz       <= (yz -, x)

idth : forall {xz} -> xz <= xz
idth {[]} = []
idth {xz -, x} = idth -, x

_-<-_ : forall {ga0 ga1 ga2} -> ga0 <= ga1 -> ga1 <= ga2 -> ga0 <= ga2
th -<- (ph -^ x) = (th -<- ph) -^ x
(th -, .x) -<- (ph -, x) = (th -<- ph) -, x
(th -^ .x) -<- (ph -, x) = (th -<- ph) -^ x
[] -<- [] = []

antisym : forall {xz yz}(th : xz <= yz)(ph : yz <= xz) ->
  Sg (xz == yz) \ { refl -> (th == idth) * (ph == idth) }
antisym [] [] = refl , refl , refl
antisym (th -, x) (ph -, .x) with antisym th ph
antisym (.idth -, x) (.idth -, .x)
  | refl , refl , refl = refl , refl , refl
antisym (th -, x) (ph -^ .x) with antisym th ((idth -^ _) -<- ph)
antisym (th -, x) ((ph -, .x) -^ .x) | refl , p , ()
antisym (th -, x) ((ph -^ _) -^ .x) | refl , p , ()
antisym (th -^ x) ph with antisym th ((idth -^ _) -<- ph)
antisym (th -^ x) (ph -, .x) | refl , p , ()
antisym (th -^ x) (ph -^ _) | refl , p , ()

_<?_ : forall {P xz yz} -> xz <= yz -> Env P yz -> Env P xz
[]        <? [] = []
(th -, x) <? (pz -, p) = (th <? pz) -, p
(th -^ x) <? (pz -, p) = th <? pz

naturalSelection : forall {P Q : X -> Set}{xz yz}
  (f : forall {x} -> P x -> Q x)(th : xz <= yz)(pz : Env P yz) ->
  (th <? (env f pz)) == (env f (th <? pz))
naturalSelection f [] [] = refl
naturalSelection f (th -, x) (pz -, p) =
  rf (_-, f p) =$= naturalSelection f th pz
naturalSelection f (th -^ x) (pz -, p) = naturalSelection f th pz

noth : forall {xz} -> [] <= xz
noth {[]} = []
noth {xz -, x} = noth -^ x

nothU : forall {xz}(th ph : [] <= xz) -> th == ph
nothU [] [] = refl
nothU (th -^ x) (ph -^ .x) rewrite nothU th ph = refl

data Tri : forall {iz jz kz}
  (th : iz <= jz)(ph : jz <= kz)(ps : iz <= kz) -> Set where
  [] : Tri [] [] []
  _-,_ : forall {iz jz kz}
   {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
   Tri th ph ps -> forall x ->
   Tri (th -, x) (ph -, x) (ps -, x)
  _-^,_ : forall {iz jz kz}
   {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
   Tri th ph ps -> forall x ->
   Tri (th -^ x) (ph -, x) (ps -^ x)
  _-^_ : forall {iz jz kz}
   {th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
   Tri th ph ps -> forall x ->
   Tri th (ph -^ x) (ps -^ x)

mkTri : forall {ga0 ga1 ga2}(th : ga0 <= ga1)(ph : ga1 <= ga2) ->
  Tri th ph (th -<- ph)
mkTri th (ph -^ x) = mkTri th ph -^ x
mkTri (th -, .x) (ph -, x) = mkTri th ph -, x
mkTri (th -^ .x) (ph -, x) = mkTri th ph -^, x
mkTri [] [] = []

triId : forall {ga de}(th : ga <= de) -> Tri th idth th
triId [] = []
triId (th -, x) = triId th -, x
triId (th -^ x) = triId th -^, x

idTri : forall {ga de}(th : ga <= de) -> Tri idth th th
idTri [] = []
idTri (th -, x) = idTri th -, x
idTri (th -^ x) = idTri th -^ x

noTri : forall {ga de}(th : ga <= de) -> Tri noth th noth
noTri [] = []
noTri (th -, x) = noTri th -^, x
noTri (th -^ x) = noTri th -^ x

assocTri : forall {ga0 ga1 ga2 ga3}
  {th01 : ga0 <= ga1}{th12 : ga1 <= ga2}{th02 : ga0 <= ga2}
  {th23 : ga2 <= ga3}{th03 : ga0 <= ga3}
  (v012 : Tri th01 th12 th02)(v023 : Tri th02 th23 th03) ->
  Sg (ga1 <= ga3) \ th13 -> Tri th01 th13 th03 * Tri th12 th23 th13
assocTri v012 (v023 -^ x) =
  let _ , v013 , v123 = assocTri v012 v023 in
  _ , (v013 -^ x) , (v123 -^ x)
assocTri (v012 -^ .x) (v023 -^, x) =
  let _ , v013 , v123 = assocTri v012 v023 in
  _ , (v013 -^ x) , (v123 -^, x)
assocTri (v012 -^, .x) (v023 -^, x) =
  let _ , v013 , v123 = assocTri v012 v023 in
  _ , (v013 -^, x) , (v123 -, x)
assocTri (v012 -, .x) (v023 -, x) =
  let _ , v013 , v123 = assocTri v012 v023 in
  _ , (v013 -, x) , (v123 -, x)
assocTri [] [] = _ , [] , []

cossaTri : forall {ga0 ga1 ga2 ga3}
  {th01 : ga0 <= ga1}{th12 : ga1 <= ga2}{th02 : ga0 <= ga2}
  {th13 : ga1 <= ga3}{th23 : ga2 <= ga3} ->
  Tri th01 th12 th02 -> Tri th12 th23 th13 ->
  Sg _ \ th03 -> Tri th01 th13 th03 * Tri th02 th23 th03
cossaTri v012 (v123 -^ x) = let _ , v013 , v023 = cossaTri v012 v123 in
  _ , (v013 -^ x) , (v023 -^ x)
cossaTri (v012 -^ .x) (v123 -^, x) = let _ , v013 , v023 = cossaTri v012 v123 in
  _ , (v013 -^ x) , (v023 -^, x)
cossaTri (v012 -^, .x) (v123 -, x) = let _ , v013 , v023 = cossaTri v012 v123 in
  _ , (v013 -^, x) , (v023 -^, x)
cossaTri (v012 -, .x) (v123 -, x) = let _ , v013 , v023 = cossaTri v012 v123 in
  _ , (v013 -, x) , (v023 -, x)
cossaTri [] [] = _ , [] , []
  
assocTri' : forall {ga0 ga1 ga2 ga3}
  {th01 : ga0 <= ga1}{th12 : ga1 <= ga2}{th03 : ga0 <= ga3}
  {th13 : ga1 <= ga3}{th23 : ga2 <= ga3} ->
  (v013 : Tri th01 th13 th03)(v123 : Tri th12 th23 th13) ->
  Sg (ga0 <= ga2) \ th02 -> Tri th01 th12 th02 * Tri th02 th23 th03
assocTri' (v013 -^ .x) (v123 -^ x) = let _ , v012 , v023 = assocTri' v013 v123 in
  _ , v012 , (v023 -^ x)
assocTri' (v013 -, .x) (v123 -, x) = let _ , v012 , v023 = assocTri' v013 v123 in
  _ , (v012 -, x) , (v023 -, x)
assocTri' (v013 -^, .x) (v123 -, x) = let _ , v012 , v023 = assocTri' v013 v123 in
  _ , (v012 -^, x) , (v023 -^, x)
assocTri' (v013 -^ .x) (v123 -^, x) = let _ , v012 , v023 = assocTri' v013 v123 in
  _ , (v012 -^ x) , (v023 -^, x)
assocTri' [] [] = _ , [] , []

triFun : forall {ga0 ga1 ga2}
  {th : ga0 <= ga1}{ph : ga1 <= ga2}{ps0 ps1 : ga0 <= ga2} ->
  Tri th ph ps0 -> Tri th ph ps1 -> ps0 == ps1
triFun [] [] = refl
triFun (v0 -, x) (v1 -, .x) rewrite triFun v0 v1 = refl
triFun (v0 -^, x) (v1 -^, .x) rewrite triFun v0 v1 = refl
triFun (v0 -^ x) (v1 -^ .x) rewrite triFun v0 v1 = refl

triMono : forall {ga0 ga1 ga2}
  {th0 th1 : ga0 <= ga1}{ph : ga1 <= ga2}{ps : ga0 <= ga2} ->
  Tri th0 ph ps -> Tri th1 ph ps -> th0 == th1
triMono [] [] = refl
triMono (v0 -, x) (v1 -, .x) rewrite triMono v0 v1 = refl
triMono (v0 -^, x) (v1 -^, .x) rewrite triMono v0 v1 = refl
triMono (v0 -^ x) (v1 -^ .x) rewrite triMono v0 v1 = refl

triComp : forall {ga0 ga1 ga2 ga3}
  {th : ga0 <= ga1}{ph : ga1 <= ga2}{ps : ga0 <= ga2}
  (v : Tri th ph ps)(xi : ga2 <= ga3) ->
  Tri th (ph -<- xi) (ps -<- xi)
triComp v xi with assocTri v (mkTri _ xi)
... | phxi' , u0 , u1 rewrite triFun u1 (mkTri _ xi) = u0

_-idth : forall {ga de}(th : ga <= de) -> (th -<- idth) == th
th -idth = triFun (mkTri th idth) (triId th)

compSel : forall {P xz yz zz}{th : xz <= yz}{ph : yz <= zz}{ps : xz <= zz}
  (t : Tri th ph ps)(pz : Env P zz) ->
  (th <? (ph <? pz)) == (ps <? pz)
compSel []        []                             = refl
compSel (t -, x)  (pz -, p) rewrite compSel t pz = refl
compSel (t -^, x) (pz -, p) rewrite compSel t pz = refl
compSel (t -^ x)  (pz -, p) rewrite compSel t pz = refl

noSel : forall {P xz}(pz : Env P xz) -> (noth <? pz) == []
noSel [] = refl
noSel (pz -, _) = noSel pz

sel1 : forall {P x xz}(i : ([] -, x) <= xz)(pz : Env P xz) ->
  Sg (P x) \ p -> (i <? pz) == ([] -, p)
sel1 (i -, x) (pz -, p) rewrite nothU i noth | noSel pz = _ , refl
sel1 (i -^ x) (pz -, _) = sel1 i pz

data Cover : forall {lz mz rz : Bwd X} ->
             lz <= mz -> rz <= mz -> Set where
  [] : Cover [] []
  _lo : forall {lz mz rz x}{th : lz <= mz}{ph : rz <= mz}
    -> Cover th ph -> Cover (th -, x) (ph -^ x)
  _ro : forall {lz mz rz x}{th : lz <= mz}{ph : rz <= mz}
    -> Cover th ph -> Cover (th -^ x) (ph -, x)
  _lr : forall {lz mz rz x}{th : lz <= mz}{ph : rz <= mz}
    -> Cover th ph -> Cover (th -, x) (ph -, x)

lcov : forall {lz mz rz : Bwd X}{th : lz <= mz}{ph : rz <= mz} ->
  Cover th ph -> lz <= mz
lcov {th = th} _ = th

rcov : forall {lz mz rz : Bwd X}{th : lz <= mz}{ph : rz <= mz} ->
  Cover th ph -> rz <= mz
rcov {ph = ph} _ = ph

cover1 : forall {lz mz rz : Bwd X}{x : X}
         (i : ([] -, x) <= mz)
         {th : lz <= mz}{ph : rz <= mz}(c : Cover th ph) ->
         (Sg (([] -, x) <= lz) \ j -> Tri j th i)
       + (Sg (([] -, x) <= rz) \ j -> Tri j ph i)
cover1 (i -, x) (c lo) rewrite nothU i noth = inl (_ , (noTri _ -, x))
cover1 (i -, x) (c ro) rewrite nothU i noth = inr (_ , (noTri _ -, x))
cover1 (i -, x) (c lr) rewrite nothU i noth = inl (_ , (noTri _ -, x))
cover1 (i -^ x) (c lo) with cover1 i c
cover1 (i -^ x) (c lo) | inl (_ , v) = inl (_ , (v -^, x))
cover1 (i -^ x) (c lo) | inr (_ , v) = inr (_ , (v -^ x))
cover1 (i -^ x) (c ro) with cover1 i c
cover1 (i -^ x) (c ro) | inl (_ , v) = inl (_ , (v -^ x))
cover1 (i -^ x) (c ro) | inr (_ , v) = inr (_ , (v -^, x))
cover1 (i -^ x) (c lr) with cover1 i c
cover1 (i -^ x) (c lr) | inl (_ , v) = inl (_ , (v -^, x))
cover1 (i -^ x) (c lr) | inr (_ , v) = inr (_ , (v -^, x))

record Coproduct {iz jz kz}(th : iz <= kz)(ph : jz <= kz) : Set where
  constructor cop
  field
    {union} : Bwd X
    {lope} : iz <= union
    {rope} : jz <= union
    somewhere : union <= kz
    ltri : Tri lope somewhere th
    covering : Cover lope rope
    rtri : Tri rope somewhere ph
open Coproduct public

coproduct : forall {iz jz kz}(th : iz <= kz)(ph : jz <= kz) -> Coproduct th ph
coproduct [] [] = cop [] [] [] []
coproduct (th -, x) (ph -, .x) with coproduct th ph
coproduct (th -, x) (ph -, .x) | cop ps ltri covering rtri =
  cop (ps -, x) (ltri -, x) (covering lr) (rtri -, x)
coproduct (th -, x) (ph -^ .x) with coproduct th ph
coproduct (th -, x) (ph -^ .x) | cop ps ltri covering rtri =
  cop (ps -, x) (ltri -, x) (covering lo) (rtri -^, x)
coproduct (th -^ x) (ph -, .x) with coproduct th ph
coproduct (th -^ x) (ph -, .x) | cop ps ltri covering rtri =
  cop (ps -, x) (ltri -^, x) (covering ro) (rtri -, x)
coproduct (th -^ x) (ph -^ .x) with coproduct th ph
coproduct (th -^ x) (ph -^ .x) | cop ps ltri covering rtri =
  cop (ps -^ x) (ltri -^ x) covering (rtri -^ x)

thinCop : forall {iz jz kz lz}{th : iz <= kz}{ph : jz <= kz} ->
  Coproduct th ph -> forall {ps : kz <= lz}{th' : iz <= lz}{ph' : jz <= lz} ->
  Tri th ps th' -> Tri ph ps ph' ->
  Coproduct th' ph'
thinCop (cop ps0 lu c ru) lv rv with assocTri lu lv | assocTri ru rv
... | th0 , lw , lx | ph0 , rw , rx rewrite triFun rx lx = cop th0 lw c rw

coproductU : forall {iz jz kz}(th : iz <= kz)(ph : jz <= kz) ->
  let cop ps lv c rv = coproduct th ph in
  forall {lz th' ph'}{ps' : lz <= kz}
  (lu : Tri th' ps' th)(ru : Tri ph' ps' ph) ->
  Sg _ \ thm -> Sg _ \ psm -> Sg _ \ phm ->
  Tri (lcov c) thm th' * Tri psm ps' ps * Tri (rcov c) phm ph'
coproductU _ _ [] [] = _ , _ , _ , [] , [] , []
coproductU _ _ (lu -, x) (ru -, .x) with coproductU _ _ lu ru
... | _ , _ , _ , lw , w , rw = _ , _ , _ , (lw -, x) , (w -, x) , (rw -, x)
coproductU _ _ (lu -, x) (ru -^, .x) with coproductU _ _ lu ru
... | _ , _ , _ , lw , w , rw = _ , _ , _ , (lw -, x) , (w -, x) , (rw -^, x)
coproductU _ _ (lu -^, x) (ru -, .x) with coproductU _ _ lu ru
... | _ , _ , _ , lw , w , rw = _ , _ , _ , (lw -^, x) , (w -, x) , (rw -, x)
coproductU _ _ (lu -^, x) (ru -^, .x) with coproductU _ _ lu ru
... | _ , _ , _ , lw , w , rw = _ , _ , _ , (lw -^ x) , (w -^, x) , (rw -^ x)
coproductU _ _ (lu -^ x) (ru -^ .x) with coproductU _ _ lu ru
... | _ , _ , _ , lw , w , rw = _ , _ , _ , lw , (w -^ x) , rw

copUnique : forall {iz jz kz lz}
  {th0 : iz <= kz}{th1 : jz <= kz}
  {ph0 : iz <= lz}{ps : kz <= lz}{ph1 : jz <= lz}
  (v0 : Tri th0 ps ph0)(c : Cover th0 th1)(v1 : Tri th1 ps ph1) ->
  coproduct ph0 ph1 == cop ps v0 c v1
copUnique (v0 -^, x) () (v1 -^, .x)
copUnique [] [] [] = refl
copUnique (v0 -, x) (c lr) (v1 -, .x) rewrite copUnique v0 c v1 = refl
copUnique (v0 -, x) (c lo) (v1 -^, .x) rewrite copUnique v0 c v1  = refl
copUnique (v0 -^, x) (c ro) (v1 -, .x) rewrite copUnique v0 c v1 = refl
copUnique (v0 -^ x) c (v1 -^ .x) rewrite copUnique v0 c v1 = refl

copQ : forall {iz jz kz}{th : iz <= kz}{ph : jz <= kz}(c c' : Coproduct th ph) ->
  c == c'
copQ (cop ps lv c rv) (cop ps' lv' c' rv')
  rewrite sym (copUnique lv c rv) = copUnique lv' c' rv'

copComp : forall {iz jz kz lz}(th : iz <= kz)(ph : jz <= kz)(ps : kz <= lz) ->
  coproduct (th -<- ps) (ph -<- ps) ==
  (let cop ps' lv c rv = coproduct th ph in
   cop (ps' -<- ps) (triComp lv ps) c (triComp rv ps))
copComp th ph ps = copQ _ _

record _^^_ (T : Bwd X -> Set)(scope : Bwd X) : Set where
  constructor _^_
  field
    {support} : Bwd X
    thing     : T support
    thinning  : support <= scope
open _^^_ public

_^$_ : forall {S T : Bwd X -> Set}(f : forall {xz} -> S xz -> T xz) ->
  forall {xz} -> S ^^ xz -> T ^^ xz
f ^$ (s ^ th) = f s ^ th

_^^^_ : forall {T xz} -> T ^^ xz -> forall x -> T ^^ (xz -, x)
(t ^ th) ^^^ x = t ^ (th -^ x)

_^<_ : forall {T xz yz}(t : T ^^ xz)(th : xz <= yz) -> T ^^ yz
(t ^ th) ^< ph = t ^ (th -<- ph)

thin1Lemma : forall {T xz x}(t : T ^^ xz) ->
  (t ^< (idth -^ x)) == (t ^^^ x)
thin1Lemma (t ^ th) = rf (t ^_) =$= (rf (_-^ _) =$= (th -idth))

data Ext (ga : Bwd X)(x : X) : Bwd X -> Set where
  kkex : Ext ga x ga
  llex : Ext ga x (ga -, x)

exth : forall {ga x de} -> Ext ga x de -> de <= (ga -, x)
exth kkex = idth -^ _
exth llex = idth

record Scope' (T : Bwd X -> Set)(x : X)(xz : Bwd X) : Set where
  constructor scop
  field
    {scsupp} : Bwd X
    scbody : T scsupp
    scex : Ext xz x scsupp
open Scope' public

data Scope (T : Bwd X -> Set)(x : X)(xz : Bwd X) : Set where
  ll : T (xz -, x) -> Scope T x xz
  kk : T xz -> Scope T x xz

sco : forall {T x xz} -> T ^^ (xz -, x) -> Scope T x ^^ xz
sco (t ^ (th -, x)) = ll t ^ th
sco (t ^ (th -^ x)) = kk t ^ th

mkExt : forall {ga de x}(th : ga <= (de -, x)) ->
  Sg _ \ ga' ->
  Sg (Ext ga' x ga) \ ex ->
  Sg (ga' <= de) \ ph ->
  Tri (exth ex) (ph -, x) th
mkExt (th -, x) = _ , llex , th , (idTri th -, x)
mkExt (th -^ x) = _ , kkex , th , (idTri th -^, x)

sco' : forall {T x xz} -> T ^^ (xz -, x) -> Scope' T x ^^ xz
sco' (t ^ th) = let ga , ex , ph , _ = mkExt th in scop t ex ^ ph


scoLemma : forall {T ga de x}
  (t : T ^^ (ga -, x))(ph : ga <= de) ->
  sco (t ^< (ph -, x)) == (sco t ^< ph)
scoLemma (t ^ (th -, x)) ph = refl
scoLemma (t ^ (th -^ x)) ph = refl

record _^*^_ (S T : Bwd X -> Set)(scope : Bwd X) : Set where
  constructor _<^_^>_
  field
    {lsupp rsupp} : Bwd X
    {lthin} : lsupp <= scope
    {rthin} : rsupp <= scope
    outl  : S lsupp
    cover : Cover lthin rthin
    outr  : T rsupp

pair : forall {S T xz} -> (S ^^ xz) * (T ^^ xz) -> (S ^*^ T) ^^ xz
pair ((s ^ th) , (t ^ ph)) with coproduct th ph
pair ((s ^ th) , (t ^ ph)) | cop ps ltri covering rtri = (s <^ covering ^> t) ^ ps

pout : forall {S T xz} -> (S ^*^ T) ^^ xz -> (S ^^ xz) * (T ^^ xz)
pout ((s <^ c ^> t) ^ th) = (s ^ (lcov c -<- th)) , (t ^ (rcov c -<- th))

pairEta : forall {S T xz}(p : (S ^*^ T) ^^ xz) -> pair (pout p) == p
pairEta ((s <^ c ^> t) ^ th)
  rewrite copUnique (mkTri (lcov c) th) c (mkTri (rcov c) th)
        = refl

data Pair {S T xz} :
  S ^^ xz -> T ^^ xz -> (S ^*^ T) ^^ xz -> Set
  where
  mkPair : forall {iz jz kz} ->
    {th : iz <= kz}{ph : jz <= kz}{ps : kz <= xz}
    {th' : iz <= xz}{ph' : jz <= xz}
    (s : S iz)(t : T jz)
    (lv : Tri th ps th')(c : Cover th ph)(rv : Tri ph ps ph') ->
    Pair (s ^ th') (t ^ ph') ((s <^ c ^> t) ^ ps)

pairPair : forall {S T xz}(s : S ^^ xz)(t : T ^^ xz) ->
  Pair s t (pair (s , t))
pairPair (s ^ th) (t ^ ph) with coproduct th ph
pairPair (s ^ th) (t ^ ph) | cop ps lv c rv = mkPair s t lv c rv

pairThin : forall
  {S T xz}{s : S ^^ xz}{t : T ^^ xz}{st : (S ^*^ T) ^^ xz} ->
  Pair s t st -> forall {yz}(th : xz <= yz) ->
  Pair (s ^< th) (t ^< th) (st ^< th)
pairThin (mkPair s t lv c rv) th = mkPair s t (triComp lv th) c (triComp rv th)

data Null : Bwd X -> Set where
  null : Null []

data Sole (x : X) : Bwd X -> Set where
  sole : Sole x ([] -, x)

