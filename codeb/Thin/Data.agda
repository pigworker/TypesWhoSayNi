------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Data                                                      -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Data where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma

module THIN {B : Set} where  -- B is the type of bindings


------------------------------------------------------------------------------
-- Scopes
------------------------------------------------------------------------------

 Scope = Bwd B

{-
A scope is a sequence of bindings which grows on the right.

Fortran: asciifications of lowercase Greek letters stand for scopes, typically
ga, de and ze.
-}


------------------------------------------------------------------------------
-- Thinnings
------------------------------------------------------------------------------

 infix 4 _<=_ _<-_
 infixl 8 _-^_
 data _<=_ : Scope -> Scope -> Set where
   []   :                                               []    <=     []
   _-,_ : forall {ga de} -> ga <= de -> forall b ->  ga -, b  <=  de -, b
   _-^_ : forall {ga de} -> ga <= de -> forall b ->  ga       <=  de -, b

{-
Thinnings steal the constructors from Bwd for the cases where they are being
preserved. However, -^ allows the insertion of target elements which are not
in the source. (^ is "caret", Latin for "it is missing")

Fortran: asciifications of lowercase Greek letters stand for scopes, typically
th, ph and ps.

Thinnings thus represent order-preserving embeddings between scopes, or,
right-to-left, selections from scopes. It should thus be no surprise that
when B = One, n <= m reifies binomial coefficients as types.

I choose the notation <= because it's a proof-relevant version of "at most".

A thinning is effectively a vector of bits indexed by
 * its population count (the number of 1s)
 * its length

As ever, with dependently typed programming, I don't just use vectors of
bits and a popcount function, because I don't want to waste my life
reasoning about popcount. Turning the measure into an index helps us take
it for granted, much of the time.
-}


------------------------------------------------------------------------------
-- Singleton Thinnings
------------------------------------------------------------------------------

 _<-_ : B -> Scope -> Set
 b <- ga = [] -, b <= ga

{-
The relation of being somewhere in a list is exactly the selection of a
singleton list. I use this instead of "Fin", these days.

Fortran: singleton thinnings will be called things like i, j. They are
indices.
-}


------------------------------------------------------------------------------
-- Identity
------------------------------------------------------------------------------

 idth : forall {ga} -> ga <= ga
 idth {[]}      = []
 idth {ga -, b} = idth -, b

{-
Of course, we have the gadgets to form a category. Not just any category:
the semi-simplicial category. Compositition waits for Thin.Triangle.
-}


------------------------------------------------------------------------------
-- Antisymmetry
------------------------------------------------------------------------------

{-
We can take the "predecessor" of a thinning with a nonempty source.
-}

 pdth : forall {ga de b} -> ga -, b <= de -> ga <= de
 pdth (th -, b) = th -^ b
 pdth (th -^ b) = pdth th -^ b

{-
We may then obtain the antisymmetry property in proof-relevant form.
-}

 antisym : forall {ga de}(th : ga <= de)(ph : de <= ga) ->
   ga ~ de >< \ { r~ -> (th ~ idth) * (ph ~ idth) }
 antisym [] [] = r~ , r~ , r~
 antisym (th -, b) (ph -, .b) with antisym th ph
 antisym (.idth -, b) (.idth -, .b)
   | r~ , r~ , r~ = r~ , r~ , r~
 antisym (th -, b) (ph -^ .b) with antisym th (pdth ph)
 antisym (th -, b) ((ph -, .b) -^ .b) | r~ , p , ()
 antisym (th -, b) ((ph -^ _) -^ .b) | r~ , p , ()
 antisym (th -^ b) ph with antisym th (pdth ph)
 antisym (th -^ b) (ph -, .b) | r~ , p , ()
 antisym (th -^ b) (ph -^ _) | r~ , p , ()

{-
When we have any diagram

              -------------->
            ga               de
              <--------------

it collapses to a point.

An immediate consequence is that all thinnings from a scope to itself are
identities.
-}

 idth! : forall {ga}(th ph : ga <= ga) -> th ~ ph
 idth! th ph with antisym th ph ; ... | r~ , r~ , r~ = r~


------------------------------------------------------------------------------
-- Initiality
------------------------------------------------------------------------------

 noth : [([] <=_)]
 noth {[]}      = []
 noth {ga -, b} = noth -^ b

 noth! : forall {ga}(th ph : [] <= ga) -> th ~ ph
 noth! [] [] = r~
 noth! (th -^ b) (ph -^ .b) rewrite noth! th ph = r~

{-
There is a unique thinning from the closed scope to any other.

               ga
                ^
                !
                ! noth
                !
               []
-}


------------------------------------------------------------------------------
-- Negation
------------------------------------------------------------------------------

 neg : forall {de ga}(th : ga <= de) -> <(_<= de)>
 neg []        = ! []
 neg (th -, b) = ! neg th .snd -^ b
 neg (th -^ b) = ! neg th .snd -, b

{-
We can invert a selection.
-}


------------------------------------------------------------------------------
-- Left and Right Injections
------------------------------------------------------------------------------

 thinl : forall {ga} de -> ga <= (ga +B de)
 thinl []        = idth
 thinl (de -, b) = thinl de -^ b

 thinr : forall {ga} de -> de <= (ga +B de)
 thinr []        = noth
 thinr (de -, b) = thinr de -, b
