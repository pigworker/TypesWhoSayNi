module Base where

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A)
  ->
  C a (f a)
(f - g) a = g (f a)

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 30 _,_ _><_ _*_ _*:_ !_
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
_*:_ : forall {X : Set} -> (X -> Set) -> (X -> Set) -> (X -> Set)
(P *: Q) x = P x * Q x
<_> : forall {X : Set} -> (X -> Set) -> Set
< P > = _ >< P
pattern !_ t = _ , t

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
{-# BUILTIN EQUALITY _~_ #-}

data Zero : Set where
record One : Set where constructor <>

data Two : Set where ff tt : Two

Tt : Two -> Set
Tt ff = Zero
Tt tt = One

not : Two -> Two
not ff = tt
not tt = ff

_\/_ : Two -> Two -> Two
ff \/ b = b
tt \/ b = tt

_/\_ : Two -> Two -> Two
ff /\ b = ff
tt /\ b = b
