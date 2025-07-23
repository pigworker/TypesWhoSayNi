module Basics where

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two
_<ft>_ : forall {l}{P : Two -> Set l} -> P ff -> P tt -> (b : Two) -> P b
(f <ft> t) ff = f
(f <ft> t) tt = t

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public

infixr 10 _,_ _*_ _><_
infixr 5 _+_

_*_ _+_ : Set -> Set -> Set
S * T = S >< \ _ -> T
S + T = Two >< (S <ft> T)

So : Two -> Set
So = Zero <ft> One

module _ {X : Set} where

  _-:>_ _:*_ : (X -> Set) -> (X -> Set) -> (X -> Set)
  (S -:> T) x = S x -> T x
  (S :* T) x = S x * T x
  infixr 10 _:*_
  infixr 5 _-:>_

  [:_:] <:_:> : (X -> Set) -> Set
  [: P :] = forall x -> P x
  <: P :> = X >< P

<1_1> : Set -> Set
<1 X 1> = X >< \ x -> (y : X) -> y ~ x

unique : {X : Set} -> <1 X 1> -> {y z : X} -> y ~ z
unique (x , q) {y} {z} with r~ <- q z = q y

_>>_ : forall {S T : Set} -> S -> (S -> T) -> T
s >> f = f s

Maybe = One +_

_>>=_ : forall {X Y} -> Maybe X -> (X -> Maybe Y) -> Maybe Y
(ff , <>) >>= k = ff , <>
(tt , x) >>= k = k x

definitely : {X : Set}(mx : Maybe X){p : So (mx .fst)} -> X
definitely (tt , x) = x

Dec : Set -> Set
Dec X = (X -> Zero) + X
EqDec : Set -> Set
EqDec X = (x y : X) -> Dec (x ~ y)

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
ze +N y = y
su x +N y = su (x +N y)

natEq? : EqDec Nat
natEq? ze ze = tt , r~
natEq? ze (su y) = ff , \ ()
natEq? (su x) ze = ff , \ ()
natEq? (su x) (su y) with natEq? x y
... | ff , z = ff , \ { r~ -> z r~ }
... | tt , r~ = tt , r~

kon : forall {i j}{A : Set i}{B : Set j} -> A -> B -> A
kon a _ = a

infixr 10 _,N-_
_,N-_ : {X : Set} -> X -> (Nat -> X) -> Nat -> X
(x ,N- xs) ze = x
(x ,N- xs) (su n) = xs n
