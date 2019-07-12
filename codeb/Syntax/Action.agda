------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Action                                                  -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Action where

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
open import Syntax.Tm

module _
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}
 open DESC B S b2s
 module ACTION
  (Cn : S -> Set) -- what constructors exist for each sort
  (Ds : {s : S} -> Cn s -> Desc)
  (M : S * Scope -> Set)
  where
  open TM B S b2s Cn Ds M

------------------------------------------------------------------------------
-- actions on free variables
------------------------------------------------------------------------------

{-
If => relates source and target scopes, we can say what we need to interpret
some value in
  ga => de
as an action, mapping terms in ga to terms in de.
-}

  record Action (_=>_ : Scope -> Scope -> Set) : Set1 where
    field
      hit : forall {b ga de} -> (b <- ga) -> ga => de -> Tm (` b2s b) :< de
      wkn : forall {ga de}(sg : ga => de) b -> (ga -, b) => (de -, b)
      hitWkn0 : forall {ga de}(sg : ga => de) b ->
                  hit (noth -, b) (wkn sg b) ~ var ^ noth -, b
      hitWkn+ : forall {ga de b}(i : b <- ga)(sg : ga => de) b' ->
                  hit (i -^ b') (wkn sg b') ~ hit i sg :^ b'

{-
Specifically, we need to know
  1. how to hit a free variable, getting back a term in the target scope
  2. how to push under a binder

We further insist that when we do push under a binder, the bound source
variable maps to the bound target variable, while the free variables are
mapped as before, but are thinned at their root into the new scope.
-}

{-
Let us build some actions.
-}

  module _ where
   open Action

------------------------------------------------------------------------------
-- identity action
------------------------------------------------------------------------------

   action~ : Action _~_
   hit action~ i r~ = var ^ i
   wkn action~ r~ b = r~
   hitWkn0 action~ r~ b = r~
   hitWkn+ action~ i r~ b = r~

{-
The equality relation on scopes induces an action. Free variables map to
themselves, and continue to do so as we push under binders.
-}


------------------------------------------------------------------------------
-- substitution action
------------------------------------------------------------------------------

   Sb : Scope -> Scope -> Set
   Sb ga de = Env (\ b -> TmR (b2s b) :< de) ga

   actionSb : Action Sb
   hit actionSb i sg with i <? sg ; ... | _ -, t = t
   wkn actionSb sg b = env (_:^ b) sg -, _  -- see next line
   hitWkn0 actionSb sg b = r~
   hitWkn+ actionSb i sg b
     with i <? sg | i <? env (_:^ b) sg | nat<? (_:^ b) i sg
   ... | tz -, t | _ -, _ | r~ = r~

{-
One way to represent a substitution is as an environment of terms in at most
the target scope, one for each of the variables in the source scope.

Such a substitution acts on variables by projecting out the appropriate term.

How to go under a binder? Well, we need both to shift the target scope for our
existing environment and to tack on the image of the bound variable. In
codebruijn representation, the shift just extends the outermost thinning in
each place in the environment. The image of the bound variable is given by
its specification in hitWkn0.
-}


------------------------------------------------------------------------------
-- from spines to substitutions
------------------------------------------------------------------------------

   spSb : forall xi {de} -> Tm (sp xi) :< de -> Sb xi de
   spSb []        _                  = []
   spSb (xi -, b) (s </ u \> t ^ th) =
     spSb xi (s ^ u/ u -<- th) -, (t ^ u\ u -<- th)


------------------------------------------------------------------------------
-- postcomposition with thinning
------------------------------------------------------------------------------

{-
Every sort of action induces another, by applying the codebruijn operator,
effectively pairing the action with a thinning to be done to the result.

To hit, hit then thin.

To go under a binder, weaken the action and extend the thinning.
-}

   module THINACTION {_=>_}(X : Action _=>_) where

    Thinned : Action \ ga de -> (ga =>_) :< de
    hit Thinned i (sg ^ ph) = hit X i sg :- ph
    wkn Thinned (sg ^ ph) b = wkn X sg b ^ ph -, b
    hitWkn0 Thinned (sg ^ ph) b
      rewrite hitWkn0 X sg b | noth! (noth -<- ph) noth = r~
    hitWkn+ Thinned i (sg ^ ph) b
      with hit X i sg | hit X (i -^ b) (wkn X sg b) | hitWkn+ X i sg b
    ... | t ^ th | _ | r~ = r~


{-
But how do we *do* such an action?

That's in Syntax.Substitution.
-}
