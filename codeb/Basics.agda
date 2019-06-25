module Basics where

data Zero : Set where
record One : Set where constructor <>

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

Dec : Set -> Set
Dec X = (X -> Zero) + X

module _ {l}{X : Set l} where

  data _==_ (x : X) : X -> Set l where
    refl : x == x

  rf : (x : X) -> x == x
  rf x = refl

  sym : forall {x y : X} -> x == y -> y == x
  sym refl = refl

  _=[_>=_ : forall x {y z} -> x == y -> y == z -> x == z
  x =[ refl >= q = q

  _=<_]=_ : forall x {y z} -> y == x -> y == z -> x == z
  x =< refl ]= q = q

  _[QED] : forall x -> x == x
  x [QED] = refl

  infixr 30 _=[_>=_ _=<_]=_
  infixr 31 _[QED]

{-# BUILTIN EQUALITY _==_ #-}

_[_> : forall {l}{S T : Set l}(s : S)(Q : S == T) -> T
s [ refl > = s

_=$=_ : forall {k l}{X : Set k}{Y : Set l}{f g : X -> Y}{a b : X} ->
  f == g -> a == b -> f a == g b
refl =$= refl = refl

infixl 2 _=$=_


record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_
