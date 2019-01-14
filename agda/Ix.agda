module Ix where

open import Basics

module _ {I : Set} where

  _-:>_ _*:_ _+:_ : (I -> Set) -> (I -> Set) -> (I -> Set)
  (S -:> T) i = S i -> T i
  (S *:  T) i = S i *  T i
  (S +:  T) i = S i +  T i

  infixr 20 _-:>_
  infixr 30 _+:_
  infixr 40 _*:_

  A:_ E:_ : (I -> Set) -> Set
  A: T = {i : I} -> T i
  E: T = Sg I T
  infixr 10 A:_ E:_
