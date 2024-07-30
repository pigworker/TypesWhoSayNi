module Basics where

data   Zero : Set where
record One  : Set where constructor <>
data   Two  : Set where #0 #1 : Two

{-# BUILTIN BOOL Two #-}
{-# BUILTIN FALSE #0 #-}
{-# BUILTIN TRUE #1 #-}


naughty : forall {l}{X : Set l} -> Zero -> X
naughty ()

_<?>_ : forall {l}{P : Two -> Set l} -> P #0 -> P #1 -> (b : Two) -> P b
(p0 <?> p1) #0 = p0
(p0 <?> p1) #1 = p1

So : Two -> Set
So = Zero <?> One

_/\_ _\/_ : Two -> Two -> Two
b /\ #1 = b
b /\ #0 = #0

b \/ #0 = b
b \/ #1 = #1

infixl 40 _\/_
infixl 50 _/\_

soOutl : forall {a b} -> So (a /\ b) -> So a
soOutr : forall {a b} -> So (a /\ b) -> So b
soOutl {b = #0} ()
soOutl {b = #1} p = p
soOutr {b = #0} ()
soOutr {b = #1} p = <>
soPair : forall {a b} -> So a -> So b -> So (a /\ b)
soPair {a} {#0} pa ()
soPair {#0} {#1} () <>
soPair {#1} {#1} <> <> = <>

soInl : forall {a b} -> So a -> So (a \/ b)
soInr : forall {a b} -> So b -> So (a \/ b)
soInl {a} {#0} pa = pa
soInl {a} {#1} pa = <>
soInr {a} {#0} ()
soInr {a} {#1} <> = <>

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
infixr 4 _,_ _*_

_*_ _+_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
S + T = Sg Two (S <?> T)

_?>=_ : forall {X Y} -> One + X -> (X -> One + Y) -> One + Y
(#0 , _) ?>= _ = #0 , _
(#1 , x) ?>= k = k x

un : forall {l}{S T}{P : Sg S T -> Set l} ->
     ((s : S)(t : T s) -> P (s , t)) -> (x : Sg S T) -> P x
un f (s , t) = f s t

Dec : Set -> Set
Dec X = (X -> Zero) + X

Pi : (S : Set)(T : S -> Set) -> Set
Pi S T = (x : S) -> T x
