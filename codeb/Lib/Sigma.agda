------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.Sigma                                                      -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.Sigma where

open import Lib.Pi


------------------------------------------------------------------------------
-- Dependent pair types
------------------------------------------------------------------------------

module _ {l} where

 infixr 2 _><_ _*_
 infixr 2 _,_ -- should be low, but probably not that low

 record _><_ (S : Set l)(T : S -> Set l) : Set l where
   constructor _,_
   field
     fst : S
     snd : T fst

 open _><_ public

 _*_ : Set l -> Set l -> Set l
 S * T = S >< ko T

{-
Dear Agdans, please may we have the notation

(x : S) >< T x

for dependent pairs? With the obvious unicode alternative, and the
nondependent degeneracy?

Pi gets the good treatment and it's just not fair on Sigma.
-}


------------------------------------------------------------------------------
-- Possibility
------------------------------------------------------------------------------

 <_> : {X : Set l} -> (X -> Set l) -> Set l
 < T > = _ >< T

{-
Most often used with Lib.Index, this is handy for eliding cruft.
-}


------------------------------------------------------------------------------
-- Eliminating dependent pairs
------------------------------------------------------------------------------

 module _ {m}{S : Set l}{T : S -> Set l}{P : S >< T -> Set m} where

  infixr 2 /\_ !\_
 
  /\_ : ((s : S)(t : T s) -> P (s , t)) -> (S >< T) >> P
  (/\ f) (s , t) = f s t

  !\_ : ({s : S}(t : T s) -> P (s , t)) -> (S >< T) >> P
  (!\ f) (s , t) = f {s} t

{-
These allow the construction of functions from pairs which would otherwise
rely on \ { (s , t) -> ... }, requiring a trailing brace, years later.
-}


------------------------------------------------------------------------------
-- Pattern synonyms for witness protection
------------------------------------------------------------------------------

infixr 2 !_

pattern !_ t = _ , t

{-
The job for ! is to hide inferable existential witnesses.

We should, of course, have {x : S} >< T x for that job, which we treat as
if it's T _. We'd need the corresponding {s} , t as manual override, to
give or expose the witness explicitly.
-}

infix 5 _^_

pattern _^_ t th = ! t , th

{-
I very often work with triples of a witness and two proofs, and again,
I don't want to talk about the witness.
-}


