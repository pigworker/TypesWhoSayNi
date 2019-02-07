module Atom where

open import Basics
open import Eq
open import Fun
open import Bwd
open import Thin

data NAT : Set where
  zero : NAT
  suc  : NAT -> NAT
{-# BUILTIN NATURAL NAT #-}

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

-- if you don't like uip, use Hedberg's Lemma
uip : {X : Set}{x y : X}{q0 : x == y}{q1 : x == y} -> q0 == q1
uip {q0 = refl}{q1 = refl} = refl

module ENUMERATION
  (X : Set)(f : X -> NAT)(finj : (x y : X) -> f x == f y -> x == y)
  where

  enumEq? : (x y : X) -> Dec (x == y)
  enumEq? x y with natEq? (f x) (f y)
  enumEq? x y | #0 , q = #0 , \ { refl -> q refl }
  enumEq? x y | #1 , q = #1 , finj x y q

  enumEqLemma : (x : X) -> enumEq? x x == (#1 , refl)
  enumEqLemma x rewrite natEqLemma (f x) = (#1 ,_) $= uip

data Atom : Set where
  NIL U PI SG CAR CDR : Atom

mune : NAT -> One + Atom
mune 0 = #1 , NIL
mune 1 = #1 , U
mune 2 = #1 , PI
mune 3 = #1 , SG
mune 4 = #1 , CAR
mune 5 = #1 , CDR
mune n = #0 , <>

enum : (a : Atom) -> Sg NAT \ n -> mune n == (#1 , a)
enum NIL = 0 , refl
enum U   = 1 , refl
enum PI  = 2 , refl
enum SG  = 3 , refl
enum CAR = 4 , refl
enum CDR = 5 , refl

enumFact : (x y : Atom) -> fst (enum x) == fst (enum y) -> x == y
enumFact x y q with enum x | enum y
... | n , a | m , b with
  (#1 , x) =< a ]=
  mune n =[ mune $= q >=
  mune m =[ b >=
  (#1 , y) [QED]
enumFact x .x q | n , a | m , b | refl = refl

module _ where
  open ENUMERATION Atom (\ a -> fst (enum a)) enumFact
  atomEq? = enumEq?
  atomEqLemma = enumEqLemma
