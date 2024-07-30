module Atom where

open import Basics
open import Eq

data NAT : Set where
  zero : NAT
  suc  : NAT -> NAT
{-# BUILTIN NATURAL NAT #-}

Atom = NAT

natEq? : (x y : NAT) -> Dec (x == y)
natEq? zero zero = #1 , refl
natEq? zero (suc y) = #0 , \ ()
natEq? (suc x) zero = #0 , \ ()
natEq? (suc x) (suc y) with natEq? x y
natEq? (suc x) (suc y) | #0 , q = #0 , \ { refl -> q refl }
natEq? (suc x) (suc .x) | #1 , refl = #1 , refl

natEqLemma : (x : NAT) -> natEq? x x == (#1 , refl)
natEqLemma zero = refl
natEqLemma (suc x) rewrite natEqLemma x = refl

atomEq? = natEq?
atomEqLemma = natEqLemma
