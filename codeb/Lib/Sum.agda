------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.Sum                                                        -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.Sum where

open import Lib.Zero
open import Lib.One
open import Lib.Pi


------------------------------------------------------------------------------
-- sum types
------------------------------------------------------------------------------

module _ {l} where

 data _+_ (S T : Set l) : Set l where
   inl : S -> S + T
   inr : T -> S + T

{-
I could introduce sums as dependent pairs over bits, but that has a
tendency to hide structure.

Instead, I'll do it the other way around. See below.
-}


------------------------------------------------------------------------------
-- eliminating sum types
------------------------------------------------------------------------------

 module _ {S T : Set l}{m}{P : S + T -> Set m} where

  _<?>_ : (S >> inl - P) -> (T >> inr - P) -> S + T >> P
  (l <?> r) (inl s) = l s
  (l <?> r) (inr t) = r t

{-
Again, I'm offering an alternative to fancy lambdas.
-}


------------------------------------------------------------------------------
-- Boolean values
------------------------------------------------------------------------------

Two = One + One

pattern ff = inl <>
pattern tt = inr <>

module _ {l}{P : Two -> Set l} where

  _<2>_ : P ff -> P tt -> (b : Two) -> P b
  f <2> t = ko f <?> ko t

So : Two -> Set
So = Zero <2> One

not : Two -> Two
not = tt <2> ff

if_then_else_ : forall {l}{X : Set l} ->
  (b : Two)(t : {_ : So b} -> X)(e : {_ : So (not b)} -> X) -> X
if tt then t else e = t
if ff then t else e = e

