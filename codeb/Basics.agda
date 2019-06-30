module Basics where

open import Agda.Primitive

id : forall {l}{X : Set l} -> X -> X
id x = x

the : forall {l}(X : Set l) -> X -> X
the _ x = x

infixr 4 _>>_
_>>_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)(g : {a : A}(b : B a) -> C a b)(a : A) -> C a (f a)
(f >> g) a = g (f a)

data Zero : Set where
record One : Set where constructor <>

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

Dec : Set -> Set
Dec X = (X -> Zero) + X

module _ {l}{X : Set l} where

  infix 3 _~_
  data _~_ (x : X) : X -> Set l where
    r~ : x ~ x

  rf : (x : X) -> x ~ x
  rf x = r~

  sym : forall {x y : X} -> x ~ y -> y ~ x
  sym r~ = r~

  _~-~_ : forall {x y z} -> x ~ y -> y ~ z -> x ~ z
  r~ ~-~ q = q

  _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
  x ~[ r~ > q = q

  _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
  x < r~ ]~ q = q

  _[QED] : forall x -> x ~ x
  x [QED] = r~

  infixr 30 _~[_>_ _<_]~_
  infixr 31 _[QED]

{-# BUILTIN EQUALITY _~_ #-}

_[_> : forall {l}{S T : Set l}(s : S)(Q : S ~ T) -> T
s [ r~ > = s

module _ {k l}{X : Set k}{Y : Set l} where
 infixl 2 _~$~_ _$~_
 _~$~_ : {f g : X -> Y}{a b : X} -> f ~ g -> a ~ b -> f a ~ g b
 r~ ~$~ r~ = r~
 _$~_ : {a b : X}             (f : X -> Y) -> a ~ b -> f a ~ f b
 f $~ q = rf f ~$~ q

infixr 2 !_ _,_ _*_
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
infixl 40 _??
_?? = snd
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
pattern !_ t = _ , t
infix 5 _^_
pattern _^_ t th = ! t , th

infixr 1 /\_
/\_ : forall {l}{S : Set}{T : S -> Set}{P : Sg S T -> Set l} ->
      ((s : S)(t : T s) -> P (s , t)) -> (x : Sg S T) -> P x
(/\ f) (s , t) = f s t

PI Pi : (S : Set)(T : S -> Set) -> Set
PI S T = (s : S) -> T s
Pi S T = {s : S} -> T s

module _ {X : Set} where

 infixr 1 _-:>_
 infixr 2 _:+_
 infixr 3 _:*_     -- probably need to rejig everything
 _-:>_ _:*_ _:+_ : (S T : X -> Set) -> X -> Set
 (S -:> T) x = S x -> T x
 (S :* T) x = S x * T x
 (S :+ T) x = S x + T x

 [_] <_> : (T : X -> Set) -> Set
 [ T ] = Pi _ T
 < T > = Sg _ T

 YAN Yan : (S : X -> Set) -> ({x : X} -> S x -> Set) -> Set
 YAN S T = forall {x}(s : S x) -> T s
 Yan S T = forall {x}{s : S x} -> T s

 TAN Tan : (S T : X -> Set) -> ({x : X} -> S x -> T x -> Set) -> Set
 TAN S T U = forall {x}(s : S x)(t : T x) -> U s t
 Tan S T U = forall {x}{s : S x}{t : T x} -> U s t

 TETHER Tether : (S T U : X -> Set) ->
   ({x : X} -> S x -> T x -> U x -> Set) -> Set
 TETHER S T U V = forall {x}(s : S x)(t : T x)(u : U x) -> V s t u
 Tether S T U V = forall {x}{s : S x}{t : T x}{u : U x} -> V s t u
 
 
data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}


