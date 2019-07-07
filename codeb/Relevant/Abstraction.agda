------------------------------------------------------------------------------
-----                                                                    -----
-----     Relevant.Abstraction                                           -----
-----                                                                    -----
------------------------------------------------------------------------------

module Relevant.Abstraction where

open import Lib.Equality
open import Lib.Sigma
open import Lib.Bwd
open import Thin.Data
open import Thin.Thinned

module _ {B : Set} where

 open THIN {B}

{-
A scoped notion of abstraction brings a newly bound variable into scope at the
local end of the context.
-}


------------------------------------------------------------------------------
-- relevance-aware abstraction
------------------------------------------------------------------------------

{-
CodeBruijn syntax is not necessarily intended to restrict the use of variables
more or less than ordinary syntax-with-binding, but it is intended to ensure
greater awareness of how variables are used.

In particular, we use types Foo ga to mean the type of Foos with support ga,
i.e., that the variables from ga not only may but must occur free in the Foo.

Now, when we bind a variable to make an abstraction of some sort, there is
nobody to tell us whether the bound variable must be used. But we must make
our minds up: if we bring it into scope, it must be used; if we do not, it
cannot be used. Let us therefore offer the choice of which to do.
-}

 infixr 8 _|-_
 data _|-_ (b : B)(T : Scope -> Set)(ga : Scope) : Set where
   ll : T (ga -, b) -> (b |- T) ga    -- two-l llambda, he's a beast
   kk : T ga        -> (b |- T) ga    -- two-k kkonstant, he's the least


------------------------------------------------------------------------------
-- smart constructor for thinned abstraction
------------------------------------------------------------------------------

 infixr 4 _\\_
 _\\_ : forall b {T : Scope -> Set}{ga} -> T :< ga -, b -> (b |- T) :< ga
 b \\ t ^ th -, .b = ll t ^ th
 b \\ t ^ th -^ .b = kk t ^ th

{-
We can tell the support of t by looking at the thinning that it is paired
with. We learn which constructor we should then use.
-}


------------------------------------------------------------------------------
-- smart destructor for thinned abstraction
------------------------------------------------------------------------------

 under : forall b {T : Scope -> Set}{ga} -> (b |- T) :< ga -> T :< ga -, b
 under b (ll t ^ th) = t ^ th -, b
 under b (kk t ^ th) = t ^ th -^ b


------------------------------------------------------------------------------
-- back and forth
------------------------------------------------------------------------------

 abstUnder : forall b {T ga}(t : (b |- T) :< ga) -> b \\ under b t ~ t
 abstUnder b (ll _ ^ th) = r~
 abstUnder b (kk _ ^ th) = r~

 underAbst : forall b {T ga}(t : T :< ga -, b) -> under b (b \\ t) ~ t
 underAbst b (_ ^ th -, .b) = r~
 underAbst b (_ ^ th -^ .b) = r~
