module Eq where

open import Agda.Primitive

module _ {l}{X : Set l} where

  data _==_ (x : X) : X -> Set l where
    refl : x == x
  infix 10 _==_

  rf : (x : X) -> x == x
  rf x = refl

  sym : {x y : X} -> x == y -> y == x
  sym refl = refl

  _[QED] : (x : X) -> x == x
  x [QED] = refl

  _=[_>=_ : (x : X){y z : X} -> x == y -> y == z -> x == z
  x =[ refl >= q = q

  _=<_]=_ : (x : X){y z : X} -> y == x -> y == z -> x == z
  x =< refl ]= q = q

  infixr 10 _=[_>=_ _=<_]=_
  infixr 11 _[QED]

{-# BUILTIN EQUALITY _==_ #-}

_=$=_ : forall {k l}{X : Set k}{Y : Set l}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
refl =$= refl = refl

_$=_ : forall {k l}{S : Set k}{T : Set l} (f : S -> T)
       {x y : S} ->                       x == y ->
                                          f x == f y
f $= q = refl =$= q

_=$_ : forall {k l}{S : Set k}{T : S -> Set l}{f g : (x : S) -> T x} ->
       (f == g) -> (x : S) -> f x == g x
refl =$ x = refl

_=$: : forall {k l}{X : Set k}{Y : Set l}{f f' : .X -> Y}{x x' : X} ->
       f == f' -> f x == f' x'
refl =$: = refl

infixl 20 _=$=_ _$=_ _=$_ _=$:

module _ {k l}(Q : Set k)(V : Set l) where

  record Reflector : Set (k ⊔ l) where
    field
      eval : Q -> V
      norm : Q -> Q
      nova : (q : Q) -> eval q == eval (norm q)
    reflection : {q0 q1 : Q} -> norm q0 == norm q1 ->
      eval q0 == eval q1
    reflection {q0}{q1} nq = 
      eval q0         =[ nova q0 >=
      eval (norm q0)  =[ eval $= nq >=
      eval (norm q1)  =< nova q1 ]=
      eval q1         [QED]

module _ {k l}{Q : Set k}{V : Set l}(R : Reflector Q V) where
  open Reflector R

  record EqQ (q0 q1 : Q) : Set l where
    constructor <_>
    field
      eqQ : eval q0 == eval q1
  open EqQ public

  [_!_]' : forall {q0 q1} -> EqQ q0 q1 -> eval q0 == eval q1
  [_!_]' = eqQ

module _ {k l}{Q : Set k}{V : Set l}{R : Reflector Q V} where
  open Reflector R

  _[QED]' : forall q -> EqQ R q q
  q [QED]' = < refl >

  _=[_>='_ : forall x {y z} -> EqQ R x y -> EqQ R y z -> EqQ R x z
  x =[ < q0 > >=' < q1 > = < _ =[ q0 >= _ =[ q1 >= _ [QED] >

  _=<_]='_ : forall x {y z} -> EqQ R y x -> EqQ R y z -> EqQ R x z
  x =< < q0 > ]=' < q1 > = < _ =< q0 ]= _ =[ q1 >= _ [QED] >

  infixr 10 _=[_>='_ _=<_]='_
  infixr 11 _[QED]'

