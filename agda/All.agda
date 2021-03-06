module All where

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
