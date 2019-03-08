module Bwd where

open import Basics
open import Eq
open import Fun
open import Cats

data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X
infixl 30 _-,_

module _ {X Y : Set}{f g : Bwd X -> Bwd Y}{f' g' : X -> Y}
         (q : f [] == g [])
         (fs : forall {xz x} -> f (xz -, x) == f xz -, f' x)
         (gs : forall {xz x} -> g (xz -, x) == g xz -, g' x)
         (q' : forall {x} -> f' x == g' x) where
         
  snocInd : (xz : Bwd X) -> f xz == g xz
  snocInd []        = q
  snocInd (xz -, x) = f (xz -, x) =[ fs >= f xz -, f' x
                        =[ rf _-,_ =$= snocInd xz =$= q' >=
                      g xz -, g' x =< gs ]= g (xz -, x) [QED]

module _ (X : Set) where
  open Cat ; open Functor
  
  MonoidBwd : Monoid (Bwd X)
  idC MonoidBwd = []
  coC MonoidBwd yz []        = yz
  coC MonoidBwd yz (xz -, x) = coC MonoidBwd yz xz -, x
  idcoC MonoidBwd = snocInd refl refl refl refl
  coidC MonoidBwd _ = refl
  cocoC MonoidBwd _ _ = snocInd refl refl refl refl

module _ {X : Set} where
  open Cat (MonoidBwd X)

  _-+_ = coC {_}{_}{_}
  infixl 30 _-+_

module _ {S T : Set}(f : S -> T) where
  open Cat ; open Functor
  
  BwdHom : Functor (MonoidBwd S) (MonoidBwd T) _
  map BwdHom []        = []
  map BwdHom (sz -, s) = map BwdHom sz -, f s
  mapId BwdHom = refl
  mapCo BwdHom _ = snocInd refl refl refl refl

  bwd   = map BwdHom {_}{_}
  bwd-+ = mapCo BwdHom  {_}{_}{_}

module _ {O}{_>_}{C : Cat O _>_}{F}(K : Concrete C F) where
  open Cat C
  open Concrete

  BWD : Concrete C (Bwd ` F)
  fun   BWD = bwd ` fun K
  funId BWD = snocInd refl refl refl (funId K _)
  funCo BWD _ _ = snocInd refl refl refl (funCo K _ _ _)

module _ where
  open Concrete

  bwdId = \ {X} f q -> funId (BWD (ID{X} f q))
  bwdCo = \ {R}{S}{T} f g h q -> funCo (BWD (TRI{R}{S}{T} f g h q)) f01 f12

_>>=_ : forall {X Y} -> Bwd X -> (X -> Bwd Y) -> Bwd Y
[] >>= k = []
(xz -, x) >>= k = (xz >>= k) -+ k x

join : forall {X} -> Bwd (Bwd X) -> Bwd X
join [] = []
join (xzz -, xz) = join xzz -+ xz

guard : forall {P} -> Dec P -> Bwd P
guard (#0 , n) = []
guard (#1 , y) = [] -, y

data BwdR {X Y}(R : X -> Y -> Set) : Bwd X -> Bwd Y -> Set where
  [] : BwdR R [] []
  _-,_ : forall {xz yz x y} -> BwdR R xz yz -> R x y -> BwdR R (xz -, x) (yz -, y)
