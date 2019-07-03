------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.Pi                                                         -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.Pi where

open import Agda.Primitive public renaming (_⊔_ to lmax)  -- damn unicode!


------------------------------------------------------------------------------
-- Pi types with an "ordinary" constructor
------------------------------------------------------------------------------

infixr 2 _>>_ _!>_

_>>_ _!>_ : forall {k l} -> (S : Set k)(T : S -> Set l) -> Set (lmax k l)
S >> T = (s : S) -> T s
S !> T = {s : S} -> T s

{-
It's sometimes useful to eschew Agda's (x : S) -> T x notation for something
more combinatory, especially when T is a function which analyses its arg in
nontrivial ways. It's also useful, partially applied, in higher-order 
settings.
-}

{-
Dear Agdans, I propose a two-step improvement programme.

Step 1. Allow as-patterns wherever you allow variable binding. E.g.

  (x@(s , t) : S * T) -> Blah s t


Step 2. Allow _@(p) to be abbreviated by (p).

The parens make the notation unambiguous:
  ((foo) : Foo) -> T     -- insists on single constructor foo
  (foo : Foo) -> T foo   -- binds a variable foo, shadowing
-}


------------------------------------------------------------------------------
-- Necessity
------------------------------------------------------------------------------

[_] : forall {l}{X : Set l} -> (X -> Set l) -> Set l
[ T ] = _ !> T

{-
This is most often used with some type family built with Lib.Index.
-}


------------------------------------------------------------------------------
-- identity functions
------------------------------------------------------------------------------

id : forall {l}{X : Set l} -> X -> X
id x = x

infix 1 _:`_

_:`_ : forall {l}(X : Set l) -> X -> X
_ :` x = x

{-
Most of the time, id does the job, but there are places where you want
to force a type onto something, and that's where :` gets used.
-}


------------------------------------------------------------------------------
-- our favourite combinators
------------------------------------------------------------------------------

module _ {i j}{A : Set i}{B : A -> Set j} where

 ko : (a : A)(b : B a) -> A
 ko a _ = a

 infixr 2 _$o_

 _$o_ : (a : A) -> A >> B -> B a
 a $o f = f a

 module _ {k}{C : (a : A) -> B a -> Set k} where

  infixl 3 _$$_   -- Schoenfinkel on the money

  _$$_ : ((a : A) -> B a >> C a) -> (s : A >> B) -> (a : A) -> C a (s a)
  (f $$ s) a = f a (s a)

{-
These combinators let us do dependently typed applicative programming in the
(A >>) idiom.
-}

------------------------------------------------------------------------------
-- diagrammatic composition (is S in disguise)
------------------------------------------------------------------------------

module _ {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} where

  infixr 4 _-_
  
  _-_ : (f : A >> B)(g : {a : A} -> B a >> C a) -> A >> C $$ f
  (f - g) a = g (f a)

{-
I like diagrammatic composition because...I like diagrams!

Now, the rhs is really g {a} (f a), so that really is S, but it specialises
to composition in the nondependent case.
-}

