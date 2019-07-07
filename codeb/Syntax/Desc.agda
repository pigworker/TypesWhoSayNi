------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Desc                                                    -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Desc where

open import Lib.One
open import Lib.Pi
open import Lib.Sigma
open import Lib.Index
open import Lib.Bwd
open import Thin.Data
open import Relevant.Pair
open import Relevant.Abstraction

module DESC
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}


------------------------------------------------------------------------------
-- Syntax Descriptions
------------------------------------------------------------------------------

 data Desc : Set where
   un'  :                      Desc  -- unit
   _*'_ : (D E : Desc)      -> Desc  -- pairing
   _>'_ : (b : B)(D : Desc) -> Desc  -- binding a variable
   `_   : (s : S)           -> Desc  -- subterm of a given sort

{-
Desc gives the necessary product and binding structures for building terms.
The sum structure appears in Syntax.Tm.
-}


------------------------------------------------------------------------------
-- Descriptions of spines
------------------------------------------------------------------------------

 sp : Scope -> Desc
 sp []         = un'
 sp (ga -, b)  = sp ga *' (` b2s b)

{-
We can turn a scope into the description of a *spine* of terms which could
instantiate that scope.
-}


------------------------------------------------------------------------------
-- deBruijn interpretation
------------------------------------------------------------------------------

 deB : (S -> Scope -> Set) -> Desc -> Scope -> Set
 deB T un'      = ko One
 deB T (D *' E) = deB T D :* deB T E
 deB T (b >' D) = (_-, b) - deB T D 
 deB T (` s)    = T s

{-
Given the meanings of the sorts (some T : S -> Scope -> Set), we can
interpret descriptions.

The deBruijn interpretation interprets unit and pairing just so,
with binding just extending the context.
-}


------------------------------------------------------------------------------
-- CodeBruijn interpretation
------------------------------------------------------------------------------

 CdB : (S -> Scope -> Set) -> Desc -> Scope -> Set
 CdB T un'      = Null
 CdB T (D *' E) = CdB T D /*\ CdB T E
 CdB T (b >' D) = b |- CdB T D
 CdB T (` s)    = T s

{-
By contrast, the CodeBruijn interpretation gives relevance-aware structures,
in which every *free* variable occurs at least once.

For unit, we insist that there are no free variables.
For pairing, we use relevant pairs, distributing the scope left and right,
but ensuring that no variable gets dropped.
For binding, we use relevant abstraction, where you bring the bound variable
into scope only if you are going to use it.
-}
