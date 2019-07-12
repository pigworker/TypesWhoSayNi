------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Meta                                                    -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Meta where

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
open import Thin.Square
open import Thin.Pullback
open import Thin.Partition
open import Relevant.Pair
open import Relevant.Abstraction
open import Syntax.Desc
open import Syntax.Tm
open import Syntax.Action
open import Syntax.Substitution
open import Syntax.Thinning
open import Syntax.Split

module _
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}
 open DESC B S b2s
 module _
  (Cn : S -> Set) -- what constructors exist for each sort
  (Ds : {s : S} -> Cn s -> Desc)
  where
  open TM B S b2s Cn Ds
  open ACTION B S b2s Cn Ds
  open SUBSTITUTION B S b2s Cn Ds
  open THINNING B S b2s Cn Ds
  open SPLIT B S b2s Cn Ds


------------------------------------------------------------------------------
-- metavariable instantiator
------------------------------------------------------------------------------

{-
Instantiating metavariables is a matter of second-order substitution.
Suppose we are instantiating metavars in M to terms involving N, possibly
with free object vars in ze.
-}

  Meta : (M N : S * Scope -> Set)(ze : Scope) -> Set
  Meta M N ze = forall {s xi} -> M (s , xi) -> Tm N (` s) :< (ze +B xi)

{-
A metavariable m with kind (s , xi) captures variables in xi. Its instantiator
can use the ze in scope and also the captured xi. When the instantiation
happens, the ze will survive untouched and the xi will get substituted by
the spine attached to m in the source term.
-}

{-
Meanwhile, we can postcompose a regular substitution to a metavariable
instantiator, acting only on the free variables.
-}

  metaSb : forall {M N ze ze'} -> Meta M N ze -> Sb N ze ze' -> Meta M N ze'
  metaSb {M}{N}{ze}{ze'} f sg {s}{xi} m = splSbG N (` s) (f m)
    (split (tacPart xi) (thinr xi) (env (_:- thinl xi) sg))
    .fst


------------------------------------------------------------------------------
-- let's do it
------------------------------------------------------------------------------

  module _ {M N : S * Scope -> Set} where

   meta : forall D {ga ze de}
          (t : Tm M D ga)       -- a term over M and ga
          (th : ga <= de)       -- ga embeds in de, the target context
          (f : Meta M N ze)     -- we can instantiate M in terms of ze...
          (ph : ze <= de)       -- ...which also embeds in de
       -> Tm N D :< de          -- we get a term in at most de

{-
There is some craft here. I could have made f : Meta M N de, but when I
push under a binder, I have to extend de, which would force me to thin in
the middle of the context. Instead, f stays put and the "image thinning" ph
remembers the bound variables it doesn't use.
-}

   -- Structural cases are structural.

   meta (` s) (c $ t) th f ph = (c $_) :$ meta (Ds c) t th f ph
   meta un' null th f ph = null ^ noth
   meta (D *' E) (d </ u \> e) th f ph =
     meta D d (u/ u -<- th) f ph /,\ meta E e (u\ u -<- th) f ph
   meta (b >' D) (kk d) th f ph = kk :$ meta D d th f ph

   -- To go under a lambda, the source thinning includes the bound variable,
   -- but the image thinning does not.

   meta (b >' D) (ll d) th f ph = b \\ meta D d (th -, b) f (ph -^ b)

   -- When we reach an object var, thin it.   

   meta (` s) var     th f ph = var ^ th

   -- When we reach a metavar with a spine, we build a split substitution.

   meta (` s) (_%_ {xi} m t) th f ph =
     splSbG N (` s)
       (f m)                  -- m's image is what we substitute in
       (split (catPart xi)    -- ze is passive; xi is active
              ph              -- passive thinning is image thinning
              (spSb N xi (meta (sp xi) t th f ph)))
                              -- active substitution built from spine
     .fst


