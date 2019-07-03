------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.Dec                                                        -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.Dec where

open import Lib.Equality
open import Lib.Zero
open import Lib.Sum
open import Lib.Nat


------------------------------------------------------------------------------
-- decisions, decisions
------------------------------------------------------------------------------

Dec : forall {l} -> Set l -> Set l
Dec X = (X -> Zero) + X

{-
A decision on a set tells you whether or not it is decidable.
-}


------------------------------------------------------------------------------
-- decidable equality
------------------------------------------------------------------------------

Dec~ : forall {l} -> Set l -> Set l
Dec~ X = (x y : X) -> Dec (x ~ y)

{-
Equality is what I quite often need to decide.
-}


------------------------------------------------------------------------------
-- injections preserve decidability
------------------------------------------------------------------------------

module _ {l}{Y : Set l}(_~Y?~_ : Dec~ Y)
         {k}{X : Set k}{i : X -> Y}(inj : forall a b -> i a ~ i b -> a ~ b)
 where

 injDec : Dec~ X
 injDec a b with i a ~Y?~ i b
 ... | inl nq = inl \ q -> nq (i $~ q)
 ... | inr q  = inr (inj a b q)


------------------------------------------------------------------------------
-- decidable equality for numbers
------------------------------------------------------------------------------

_~Nat?~_ : Dec~ Nat
zo   ~Nat?~ zo   = inr r~
zo   ~Nat?~ su n = inl \ ()
su m ~Nat?~ zo   = inl \ ()
su m ~Nat?~ su n with m ~Nat?~ n
... | inl nq = inl \ { r~ -> nq r~ }
... | inr r~ = inr r~

{-
Numbers are the canonical set with a decidable equality.
-}

decViaNat = injDec _~Nat?~_
