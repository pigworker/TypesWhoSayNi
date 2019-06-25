module Atom where

open import Basics

data Atom : Set where
  nil : Atom
  red blue : Atom -> Atom

atomEq? : (a b : Atom) -> Dec (a == b)
atomEq? nil      nil       = inr refl
atomEq? nil      (red b)   = inl \ ()
atomEq? nil      (blue b)  = inl \ ()
atomEq? (red a)  nil       = inl \ ()
atomEq? (red a)  (red b)   with atomEq? a b
atomEq? (red a)  (red b)   | inl q = inl \ { refl -> q refl }
atomEq? (red a)  (red .a)  | inr refl = inr refl
atomEq? (red a)  (blue b)  = inl \ ()
atomEq? (blue a) nil       = inl \ ()
atomEq? (blue a) (red b)   = inl \ ()
atomEq? (blue a) (blue b)  with atomEq? a b
atomEq? (blue a) (blue b)  | inl q    = inl \ { refl -> q refl }
atomEq? (blue a) (blue .a) | inr refl = inr refl
