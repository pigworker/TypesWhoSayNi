module Atom where

open import Basics
open import Eq

data Atom : Set where
  NIL U PI SG CAR CDR : Atom

atomEq? : (x y : Atom) -> Dec (x == y)
atomEq? NIL NIL = #1 , refl
atomEq? NIL U   = #0 , \ ()
atomEq? NIL PI  = #0 , \ ()
atomEq? NIL SG  = #0 , \ ()
atomEq? NIL CAR = #0 , \ ()
atomEq? NIL CDR = #0 , \ ()
atomEq? U   NIL = #0 , \ ()
atomEq? U   U   = #1 , refl
atomEq? U   PI  = #0 , \ ()
atomEq? U   SG  = #0 , \ ()
atomEq? U   CAR = #0 , \ ()
atomEq? U   CDR = #0 , \ ()
atomEq? PI  NIL = #0 , \ ()
atomEq? PI  U   = #0 , \ ()
atomEq? PI  PI  = #1 , refl
atomEq? PI  SG  = #0 , \ ()
atomEq? PI  CAR = #0 , \ ()
atomEq? PI  CDR = #0 , \ ()
atomEq? SG  NIL = #0 , \ ()
atomEq? SG  U   = #0 , \ ()
atomEq? SG  PI  = #0 , \ ()
atomEq? SG  SG  = #1 , refl
atomEq? SG  CAR = #0 , \ ()
atomEq? SG  CDR = #0 , \ ()
atomEq? CAR NIL = #0 , \ ()
atomEq? CAR U   = #0 , \ ()
atomEq? CAR PI  = #0 , \ ()
atomEq? CAR SG  = #0 , \ ()
atomEq? CAR CAR = #1 , refl
atomEq? CAR CDR = #0 , \ ()
atomEq? CDR NIL = #0 , \ ()
atomEq? CDR U   = #0 , \ ()
atomEq? CDR PI  = #0 , \ ()
atomEq? CDR SG  = #0 , \ ()
atomEq? CDR CAR = #0 , \ ()
atomEq? CDR CDR = #1 , refl
