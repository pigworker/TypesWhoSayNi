module Basics where

data   Zero : Set where
record One  : Set where constructor <>
data   Two  : Set where #0 #1 : Two

_<?>_ : forall {l}{P : Two -> Set l} -> P #0 -> P #1 -> (b : Two) -> P b
(p0 <?> p1) #0 = p0
(p0 <?> p1) #1 = p1

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public

_*_ _+_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
S + T = Sg Two (S <?> T)

un : forall {l}{S T}{P : Sg S T -> Set l} ->
     ((s : S)(t : T s) -> P (s , t)) -> (x : Sg S T) -> P x
un f (s , t) = f s t

Dec : Set -> Set
Dec X = (X -> Zero) + X
