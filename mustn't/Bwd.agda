module Bwd where

open import Basics

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

infixl 20 _-,_

All Any : forall {X} -> (P : X -> Set) -> Bwd X -> Set
All P [] = One
All P (xz -, x) = All P xz * P x
Any P [] = Zero
Any P (xz -, x) = Any P xz + P x

zipA : forall {X}{P : X -> Set}(xz : Bwd X)(pz : All P xz) -> Bwd (X >< P)
zipA [] <> = []
zipA (xz -, x) (pz , p) = zipA xz pz -, (x , p)
