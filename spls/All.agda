module All where

open import Basics
open import Eq
open import Fun
open import Cats
open import Bwd
open import Thin
open import Ix

module _ {I : Set} where

  data All (P : I -> Set) : Bwd I -> Set where
    []   : All P []
    _-,_ : forall {iz i} -> All P iz -> P i -> All P (iz -, i)

  module _ {P : I -> Set} where
    open Concrete ; open Cat (OPE {I} op)

    _:+_ : forall {iz jz} -> All P iz -> All P jz -> All P (iz -+ jz)
    pz :+ []        = pz
    pz :+ (qz -, q) = (pz :+ qz) -, q

    top : forall {iz} -> A: All P ` (iz -,_) -:> P
    top (_ -, p) = p

    pop : forall {i} -> A: All P ` (_-, i) -:> All P
    pop (pz -, _) = pz

    pure : A: P -> A: All P
    pure p {[]}      = []
    pure p {iz -, i} = pure p -, p

    Select : Concrete (OPE op) (All P)
    fun Select (th no) pz = fun Select th (pop pz)
    fun Select (th su) pz = fun Select th (pop pz) -, top pz
    fun Select ze      pz = []
    funId Select []        = refl
    funId Select (pz -, p) = (_-, _) $= funId Select pz
    funCo Select (ph no)  th     pz = funCo Select ph th (pop pz)
    funCo Select (ph su) (th no) pz = funCo Select ph th (pop pz)
    funCo Select (ph su) (th su) pz = (_-, _) $= funCo Select ph th (pop pz)
    funCo Select ze      ze      pz = refl

    select = fun Select

    project : forall {j jz}(i : j <- jz) -> All P jz -> P j
    project i pz = top (select i pz)

    selectPure : forall {iz jz}(th : iz <= jz)(p : A: P) ->
      select th (pure p) == pure p
    selectPure (th no) p = selectPure th p
    selectPure (th su) p = (_-, _) $= selectPure th p
    selectPure ze      p = refl

    filter : ((i : I) -> Dec (P i)) -> forall jz ->
      Sg _ \ iz -> (iz <= jz) * All P iz
    filter p [] = [] , ze , []
    filter p (jz -, i) with p i | filter p jz
    filter p (jz -, i) | #0 , n | iz , th , pz = iz , (th no) , pz
    filter p (jz -, i) | #1 , y | iz , th , pz = iz -, i , (th su) , (pz -, y)

    filterU : (p : (i : I) -> Dec (P i)) -> forall jz ->
      let iz , th , pz = filter p jz in
      forall {hz}(ph : hz <= jz)(qz : All P hz) ->
      Sg (hz <= iz) \ th' -> Tri th' th ph
    filterU p [] ze [] = ze , ze
    filterU p (jz -, i) (ph no) qz with p i | filter p jz | filterU p jz ph qz
    filterU p (jz -, i) (ph no) qz | #0 , a | iz , th , pz | th' , t
      = th' , t no
    filterU p (jz -, i) (ph no) qz | #1 , a | iz , th , pz | th' , t
      = th' no , t nosuno
    filterU p (jz -, i) (ph su) (qz -, q) with p i | filter p jz | filterU p jz ph qz
    filterU p (jz -, i) (ph su) (qz -, q) | #0 , n | iz , th , pz | th' , t
      = naughty (n q)
    filterU p (jz -, i) (ph su) (qz -, q) | #1 , y | iz , th , pz | th' , t
      = th' su , t su

  module _ {S T : I -> Set} where
  
    _<*>_ : A: All (S -:> T) -:> All S -:> All T
    _<*>_ {[]}      fz sz = []
    _<*>_ {iz -, x} fz sz = pop fz <*> pop sz -, top fz (top sz)
    infixl 70 _<*>_

    selectApp : forall {iz jz}(th : iz <= jz)
      (fz : All (S -:> T) jz)(sz : All S jz) ->
      select th (fz <*> sz) == select th fz <*> select th sz
    selectApp (th no) (fz -, f) (sz -, s) = selectApp th fz sz
    selectApp (th su) (fz -, f) (sz -, s) = (_-, _) $= selectApp th fz sz
    selectApp ze      []        []        = refl

    all : A: (S -:> T) -> A: All S -:> All T
    all f sz = pure f <*> sz

    selectAll : forall {iz jz}(th : iz <= jz)
      (f : A: (S -:> T))(sz : All S jz) ->
      select th (all f sz) == all f (select th sz)
    selectAll th f sz =
      select th (all f sz)                    =[ selectApp th (pure f) sz >=
      select th (pure f) <*> select th sz  =[ (_<*> _) $= selectPure th f >=
      all f (select th sz)                                             [QED]

    allPure : forall (f : A: S -:> T)(s : A: S) {iz} ->
      all f {iz} (pure s) == pure (f s)
    allPure f s {[]}      = refl
    allPure f s {iz -, i} = (_-, _) $= allPure f s

  module _ {S T : I -> Set} where

    allInter : forall {iz}(fz : All (S -:> T) iz)(s : A: S) ->
      fz <*> pure s == all (\ f -> f s) fz
    allInter []        s = refl
    allInter (fz -, f) s = (_-, _) $= allInter fz s

  module _ {R S T : I -> Set} where

    allComp : forall {iz}(fz : All (S -:> T) iz)(gz : All (R -:> S) iz)
              (rz : All R iz) ->
              fz <*> (gz <*> rz) == (all _`_ fz <*> gz <*> rz)
    allComp []        []        []        = refl
    allComp (fz -, f) (gz -, g) (rz -, r) = (_-, _) $= allComp fz gz rz

  module _ {O _=>_}{C : Cat O _=>_}{X : O -> I -> Set}
    (F : {i : I} -> Concrete C \ o -> X o i) where
    open Concrete ; open Cat C

    ALL : {iz : Bwd I} -> Concrete C \ o -> All (X o) iz
    fun   ALL f = all (fun F f)
    funId ALL []        = refl
    funId ALL (sz -, s) = rf _-,_ =$= funId ALL sz =$= funId F s
    funCo ALL f g []        = refl
    funCo ALL f g (rz -, r) = rf _-,_ =$= funCo ALL f g rz =$= funCo F f g r
      -- deriving funCo ALL from allComp needs all's extensionality
{-
    module _ {_=>'_ : O -> O -> Set}
      (R : {s t : O} -> Reflector (s =>' t) (s => t)) where
      open Reflector

      data All' (t : O)(iz : Bwd I) : Set where
        <_>  : All (X t) iz -> All' t iz
        all' : forall {s} -> Comp' _ _=>'_ s t -> All' s iz -> All' t iz
        sel' : forall {jz} -> iz <=' jz -> All' t jz -> All' t iz

      module ALLSTUFF where
        module TH = THINSTUFF
        
        all^ : forall {s t jz} -> Comp' _ _=>'_ s t -> All' s jz -> All' t jz
        all^ f (all' g xz) = all^ (co^ g f) xz
        all^ id' xz = xz
        all^ f xz = all' f xz

        sel^ : forall {t iz jz} -> iz <=' jz -> All' t jz -> All' t iz
        sel^ th (all' f xz)  = all' f (sel^ th xz)
        sel^ th (sel' ph xz) = sel^ (th TH.-<^ ph) xz
        sel^ th xz = sel' th xz

        evalA : forall {t iz} -> All' t iz -> All (X t) iz
        evalA < xz >       = xz
        evalA (all' f xz)  = all (fun F {!!}) (evalA xz)
        evalA (sel' th xz) = select (eval THIN' th) (evalA xz)

-}

  module _ {P}(f : A: P -:> P)(q : {i : I} -> f {i} =:= id){iz : Bwd I} where
    open Concrete (ALL (\ {i} -> ID (f {i}) q) {iz})
    allId = funId {_}

  module _ {R S T}(f : A: R -:> S)(g : A: S -:> T)(h : A: R -:> T)
    (q : {i : I} -> h {i} =:= g ` f){iz : Bwd I} where
    open Concrete (ALL (\ {i} -> TRI (f {i}) g h q) {iz})
    allCo = funCo f01 f12

  module _ {S T}(f : A: S -:> T) where
    allCat : forall {xz yz}(pz : All S xz)(qz : All S yz) ->
      all f (pz :+ qz) == (all f pz :+ all f qz)
    allCat pz [] = refl
    allCat pz (qz -, q) = (_-, _) $= allCat pz qz

  module _ {P} where
    selCat : forall {az bz cz dz}(th : az <= bz)(ph : cz <= dz)
      (pz : All P bz)(qz : All P dz) ->
      select (th ^+ ph) (pz :+ qz) == (select th pz :+ select ph qz)
    selCat th (ph no) pz (qz -, q) = selCat th ph pz qz
    selCat th (ph su) pz (qz -, q) = (_-, _) $= selCat th ph pz qz
    selCat th ze pz [] = refl

    selNo : forall {az}(pz : All P az) -> select oe pz == []
    selNo [] = refl
    selNo (pz -, _) = selNo pz

    selLeft : forall {az bz cz}(th : az <= bz)(pz : All P bz)(qz : All P cz) ->
      select (thinl th cz) (pz :+ qz) == select th pz
    selLeft {cz = cz} th pz qz =
      select (th ^+ oe {xz = cz}) (pz :+ qz)
        =[ selCat th oe pz qz >=
      (select th pz :+ select oe qz)
        =[ (select th pz :+_) $= selNo qz >=
      select th pz [QED]

    selRight : forall {az bz cz}(th : az <= cz)(pz : All P bz)(qz : All P cz) ->
      select (thinr bz th) (pz :+ qz) == select th qz
    selRight {bz = bz} (th no) pz (qz -, _) = selRight th pz qz
    selRight {bz = bz} (th su) pz (qz -, q) = (_-, _) $= selRight th pz qz
    selRight {bz = bz} ze pz [] = selNo pz

    module _ where
      open module SELECTI {P} = Concrete (Select {P})
      
      lefts  : forall iz jz (pz : All P (iz -+ jz)) -> All P iz
      lefts iz jz  = select (thinl oi jz)
      leftis : forall {iz jz}(pz : All P iz)(qz : All P jz) ->
        lefts iz jz (pz :+ qz) == pz
      leftis pz []        = funId _
      leftis pz (qz -, q) = leftis pz qz

      rights : forall iz jz (pz : All P (iz -+ jz)) -> All P jz
      rights iz jz = select (thinr iz (oi {S = jz}))
      rightis : forall {iz jz}(pz : All P iz)(qz : All P jz) ->
        rights iz jz (pz :+ qz) == qz
      rightis pz []        = selNo pz
      rightis pz (qz -, q) = (_-, _) $= rightis pz qz

      split : forall iz jz (pz : All P (iz -+ jz)) ->
        pz == (lefts iz jz pz :+ rights iz jz pz)
      split iz [] pz = sym (_:+_ $= funId pz =$= selNo pz)
      split iz (jz -, j) (pz -, p) = (_-, p) $= split iz jz pz

      data Chop iz jz : (pz : All P (iz -+ jz)) -> Set where
        chopped : (pz : All P iz)(qz : All P jz) -> Chop iz jz (pz :+ qz)
      chop : forall iz jz (pz : All P (iz -+ jz)) -> Chop iz jz pz
      chop iz [] pz = chopped pz []
      chop iz (jz -, j) (pz -, q) with chop iz jz pz
      chop iz (jz -, j) (.(pz :+ qz) -, q) | chopped pz qz
        = chopped pz (qz -, q)

      chopEq : forall {iz jz}(pz : All P iz)(qz : All P jz) ->
        chop iz jz (pz :+ qz) == chopped pz qz
      chopEq pz [] = refl
      chopEq pz (qz -, q) rewrite chopEq pz qz = refl

  presence : forall iz -> All (_<- iz) iz
  presence [] = []
  presence (iz -, i) = all _no (presence iz) -, (oe su)


joinThins : forall {X}(xzz : Bwd (Bwd X)) -> All (_<= join xzz) xzz
joinThins [] = []
joinThins (xzz -, xz) = all (_-< thinl oi xz) (joinThins xzz) -, thinr (join xzz) oi

findPairCat : {X : Set}{x0 x1 : X}(xz yz : Bwd X)
  (th : ([] -, x0 -, x1) <= (xz -+ yz)) ->
  (([] -, x0 -, x1) <= xz) +
  (((x0 <- xz) * (x1 <- yz)) +
   (([] -, x0 -, x1) <= yz))
findPairCat xz [] th = #0 , th
findPairCat xz (yz -, x) (th no) with findPairCat xz yz th
findPairCat xz (yz -, x) (th no) | #0 , ph = #0 , ph
findPairCat xz (yz -, x) (th no) | #1 , #0 , ph0 , ph1 = #1 , #0 , ph0 , ph1 no
findPairCat xz (yz -, x) (th no) | #1 , #1 , ph = #1 , #1 , ph no
findPairCat xz (yz -, x) (th su) with fromCat xz yz th
findPairCat xz (yz -, x) (th su) | #0 , ph , _ = #1 , #0 , ph , (oe su)
findPairCat xz (yz -, x) (th su) | #1 , ph , _ = #1 , #1 , ph su

findOneJoin : forall {X : Set}{x}(xzz : Bwd (Bwd X)) -> x <- join xzz ->
  Sg _ \ xz -> (x <- xz) * (xz <- xzz)
findOneJoin [] ()
findOneJoin (xzz -, xz) th with fromCat (join xzz) xz th
findOneJoin (xzz -, xz) th | #0 , th' , _ with findOneJoin xzz th'
... | _ , ph0 , ph1 = _ , ph0 , ph1 no
findOneJoin (xzz -, xz) th | #1 , ph , _ = _ , ph , (oe su)

findPairJoin : {X : Set}{x0 x1 : X}(xzz : Bwd (Bwd X))
  (th : ([] -, x0 -, x1) <= join xzz) ->
  (Sg _ \ xz -> (xz <- xzz) * ([] -, x0 -, x1) <= xz)
  +
  (Sg _ \ xz0 -> Sg _ \ xz1 ->
    (([] -, xz0 -, xz1) <= xzz) *
    (x0 <- xz0) * (x1 <- xz1))
findPairJoin [] ()
findPairJoin (xzz -, xz) th with findPairCat (join xzz) xz th
findPairJoin (xzz -, xz) th | #0 , th' with findPairJoin xzz th'
findPairJoin (xzz -, xz) th | #0 , th' | #0 , _ , ph0 , ph1 = #0 , _ , ph0 no , ph1
findPairJoin (xzz -, xz) th | #0 , th' | #1 , _ , _ , ph0 , ph1 , ph2 = #1 , _ , _ , ph0 no , ph1 , ph2
findPairJoin (xzz -, xz) th | #1 , #0 , th0 , th1 with findOneJoin xzz th0
... | _ , ph0 , ph1 = #1 , _ , _ , ph1 su , ph0 , th1
findPairJoin (xzz -, xz) th | #1 , #1 , ph = #0 , _ , oe su , ph


bindThins : forall {X Y}(xz : Bwd X)(k : X -> Bwd Y) ->
  All (\ x -> k x <= (xz >>= k)) xz
bindThins [] k = []
bindThins (xz -, x) k =
  all (_-< thinl oi (k x)) (bindThins xz k) -, thinr (xz >>= k) oi

comprehension : forall {X Y}{S : X -> Set}{T : Y -> Set}
  {xz : Bwd X} -> All S xz ->
  (k : X -> Bwd Y) ->
  ({x : X} -> S x -> All T (k x)) ->
  All T (xz >>= k)
comprehension []        k g = []
comprehension (sz -, s) k g = comprehension sz k g :+ g s

Some : {X : Set} -> (X -> Set) -> Set
Some {X} P = Sg (Bwd X) \ xz -> All P xz

_S>>=_ : forall {X Y}{S : X -> Set}{T : Y -> Set} ->
  Some S -> ({x : X} -> S x -> Some T) -> Some T
(.[] , []) S>>= k = [] , []
(.(_ -, _) , (sz -, s)) S>>= k with (_ , sz) S>>= k | k s
... | yz , tz | yz' , tz' = (yz -+ yz') , (tz :+ tz')

{-
join^ : forall {X}{yzz : Bwd (Bwd X)} -> All (\ yz -> Sg _ \ xz -> xz <= yz) yzz ->
  Sg _ \ xz -> xz <= join yzz
join^ [] = [] , ze
join^ (thz -, (xz1 , th1)) with join^ thz
... | xz0 , th0 = (xz0 -+ xz1) , (th0 ^+ th1)

data InJoin^ {X}(yzz : Bwd (Bwd X)) : (Sg _ \ xz -> xz <= join yzz) -> Set where
  isJoin^ : (thz : All (\ yz -> Sg _ \ xz -> xz <= yz) yzz) ->
            InJoin^ yzz (join^ thz)

inJoin^ : forall {X}(yzz : Bwd (Bwd X)){xz}(th : xz <= join yzz) ->
          InJoin^ yzz (xz , th)
inJoin^ [] ze = isJoin^ []
inJoin^ (yzz -, yz) th with thinSplitCat yz th
inJoin^ (yzz -, yz) .(th0 ^+ th1) | xz0 , xz1 , th0 , th1 , refl , refl
  with inJoin^ yzz th0
inJoin^ (yzz -, yz) .(snd (join^ thz) ^+ th1)
  | .(fst (join^ thz)) , xz1 , .(snd (join^ thz)) , th1 , refl , refl
  | isJoin^ thz
  = isJoin^ (thz -, (_ , th1))


cart : forall {X Y} -> Bwd X -> Bwd Y -> Bwd (X * Y)
cart xz yz = xz >>= \ x -> yz >>= \ y -> [] -, (x , y)

cartIx : forall {X Y}{x : X}{y : Y} xz yz -> (x , y) <- cart xz yz ->
  (x <- xz) * (y <- yz)
cartIx xz yz ij =
  project ij (
  comprehension (presence xz) (\ x -> yz >>= \ y -> [] -, (x , y))
  \ {x} i ->
    comprehension (presence yz) (\ y -> [] -, (x , y))
    \ {y} j -> [] -, (i , j))

ixCart : forall {X Y}{x : X}{y : Y}{xz yz} ->
  (x <- xz) -> (y <- yz) -> (x , y) <- cart xz yz
ixCart {x = x}{yz = yz} i j
  with narrowing i (\ x -> yz >>= \ y -> [] -, (x , y))
     | narrowing j (\ y -> [] -, (x , y))
... | th | ph rewrite BWD.idcoC (yz >>= \ y -> [] -, (x , y))
    = ph -< th
-}
