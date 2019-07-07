------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Tm                                                      -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Tm where

open import Lib.One
open import Lib.Equality
open import Lib.Pi
open import Lib.Sigma
open import Lib.Sum
open import Lib.Index
open import Lib.Bwd
open import Thin.Data
open import Thin.Select
open import Thin.Triangle
open import Thin.Cover
open import Thin.Thinned
open import Relevant.Pair
open import Relevant.Abstraction
open import Syntax.Desc

module _
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}
 open DESC B S b2s

------------------------------------------------------------------------------
-- What makes a syntax?
------------------------------------------------------------------------------

 module TM
  (Cn : S -> Set)
  (Ds : {s : S} -> Cn s -> Desc)
  (M : S * Scope -> Set)
  where

{-
For each sort s : S, there is a set Cn s of its constructors.
Moreover, each such constructor maps to the description of its arguments.

Descriptions give product and binding structure, but now we have sum structure
as well.

Meanwhile, syntax supports a notion of *metavariable*. The kind of a
metavariable is a pair of a sort s and a scope ga, telling you which terms
may instantiate the metavariable: those of sort s in scope ga.
-}


------------------------------------------------------------------------------
-- How to make terms
------------------------------------------------------------------------------

  data TmR (s : S)(ga : Scope) : Set   -- relevance-aware terms of given sort

  Tm : Desc -> Scope -> Set            -- Tm lifts TmR from S to Desc
  Tm D = CdB TmR D

  data TmR s ga where
    va  : forall {b} -> Sole b ga -> b2s b ~ s           -> Tm (` s) ga
    _$_ : (c : Cn s)(t : Tm (Ds c) ga)                   -> Tm (` s) ga
    _%_ : forall {xi}(m : M (s , xi))(t : Tm (sp xi) ga) -> Tm (` s) ga

  pattern var = va sole r~

{-
Tm D ga is the set of terms with description D which use every variable in ga
at least once.

The idea of CodeBruijn representation is to work with Tm D :< ga, being the
terms whose support is *at most* ga. We're exploiting the way :< makes
anything freely thinnable by giving it things which refuse to be thinned.
That way, the *only* way such a term can have a support below its scope is
for that thinning to sit at the root. Alpha-equivalence is plain equality.
-}

{-
To give a variable of sort s, the context must consist of exactly one variable
whose binder maps to sort s. If
  i : b <- ga
then
  var ^ i : Tm (` b2s b) :< ga

A constructor form
  c $ t
must carry payload of description Ds c.

A metavariable instantiation
  m % t
must carry a spine of terms appropriate to m's scope.
-}
