module Basics where

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 10 !_
infixr 10 _,_ _*_
pattern !_ t = _ , t
_+_ _*_ : Set -> Set -> Set
S + T = Two >< \ { ff -> S ; tt -> T }
S * T = S >< \ _ -> T

id : forall {i}{X : Set i} -> X -> X
id x = x

_-_ : forall {i j k}
  {A : Set i}
  {B : A -> Set j}
  {C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  ->
  (a : A) -> C a (f a)
(f - g) a = g (f a)

Dec : Set -> Set
Dec X = (X -> Zero) + X

module _ {X : Set} where
  data _~_ (x : X) : X -> Set where
    r~ : x ~ x
  infix 20 _~_

  [_] [>_] <_> : (X -> Set) -> Set
  [ P ] = {x : X} -> P x
  [> P ] = (x : X) -> P x
  < P > = X >< P

  infixr 10 _*:_
  infixr 9 _+:_
  infixr 8 _-:>_
  _+:_ _*:_ _-:>_ : (X -> Set) -> (X -> Set) -> (X -> Set)
  (P +:  Q) x = P x +  Q x
  (P *:  Q) x = P x *  Q x
  (P -:> Q) x = P x -> Q x

_>><<_ : forall {S S' T T'} -> (f : S -> S')(g : [ T -:> (f - T') ])
      -> S >< T -> S' >< T'
(f >><< g) (s , t) = f s , g t

onFst : forall {S S' T} -> (S -> S') -> (S * T) -> (S' * T)
onFst f = f >><< id

onSnd : forall {S T T'} -> [ T -:> T' ] -> S >< T -> S >< T'
onSnd f = id >><< f

{-# BUILTIN EQUALITY _~_ #-}

!~_ : forall {X}(x : X) -> x ~ x
!~ _ = r~

infixl 2 _~$~_
_~$~_ : forall {X Y}
  {f g : X -> Y} -> f ~ g ->
  {a b : X} -> a ~ b ->
  f a ~ g b
r~ ~$~ r~ = r~

_~[_>_ : forall {X} (x : X) {y z} -> x ~ y -> y ~ z -> x ~ z
x ~[ r~ > q = q
_<_]~_ : forall {X} (x : X) {y z} -> y ~ x -> y ~ z -> x ~ z
x < r~ ]~ q = q
_[QED] : forall {X} (x : X) -> x ~ x
x [QED] = r~
infixr 0 _~[_>_ _<_]~_
infixl 1 _[QED]

uip : forall {X}{x y : X}(p q : x ~ y) -> p ~ q
uip r~ r~ = r~

Uniquely : Set -> Set
Uniquely X = X >< \ x -> (y z : X) -> y ~ z

record Fam (X : Set) : Set1 where
  constructor fam
  field
    Ix : Set
    el : Ix -> X
open Fam public
