------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Pullback                                                  -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Pullback where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma
open import Lib.Sum
open import Thin.Data
open import Thin.Triangle
open import Thin.Square

module _ {B : Set} where  -- B is the type of bindings

 open THIN {B}

{-
If we have two subscopes of ga, their *intersection* should also be a subscope
of ga, as well as of ga0 and ga1. Moreover, it should be the *largest*
subscope of ga with this property. Such a square is...

         ga
        /|\
    th0/ | \th1
      /  |  \
  ga0<   |   >ga1
      \  |  /  
       \ | /
        \|/
      ga0^ga1

...a pullback, categorically speaking.

        /|\
    th0/ | \th1
      /  |  \
     <   |   >
      \  |  /  
       \ | /
        \^/

We should be able to define when a given square is, moreover, a pullback.
We should be able to compute pullbacks.
We should show that pullbacks have an appropriate universal property.
Let's do it!
-}


------------------------------------------------------------------------------
-- when is a square a pullback?
------------------------------------------------------------------------------

 data Pullback : forall {ga de}{a y : <(ga <=_) :* (_<= de)>} -> Square a y ->
   Set where
   []    :
         --------------------------------
           Pullback (  []    ^   []   )
   
   _-,_  : forall {ga de}{x y : <(ga <=_) :* (_<= de)>}{s : Square x y} ->
   
           let       v       ^ w       = s in Pullback s -> (b : B) ->
         ---------------------------------------------------------------
           Pullback (v -, b  ^ w -, b )
     
   _-^,_ : forall {ga de}{x y : <(ga <=_) :* (_<= de)>}{s : Square x y} ->
   
           let       v       ^ w       = s in Pullback s -> (b : B) ->
         ---------------------------------------------------------------
           Pullback (v -^ b  ^ w -^, b)
     
   _-,^_ : forall {ga de}{x y : <(ga <=_) :* (_<= de)>}{s : Square x y} ->
   
           let       v       ^ w       = s in Pullback s -> (b : B) ->
         ---------------------------------------------------------------
           Pullback (v -^, b ^ w -^ b )
     
   _-^_  : forall {ga de}{x y : <(ga <=_) :* (_<= de)>}{s : Square x y} ->
   
           let       v       ^ w       = s in Pullback s -> (b : B) ->
         ---------------------------------------------------------------
           Pullback (v -^ b  ^ w -^ b )
     
{-
The above is the definition of bitwise conjunction, obfuscated by the
retention of copious additional information about provenance. Note that in the
last three cases, the ^ in each triangle constructor means that the given b is
missing from the intersection of the scopes, because it is missing in at least
one of the subscopes. The b is only present (indicated by -,) in the case
where it is in both subscopes.

By expressing pullbacks in terms of squares, i.e., pairs of triangles sharing
a diagonal, we obtain all three embeddings (to both subscopes and the main
scope) and their commutativity.
-}

-- HOLE: prove uniqueness of pullback evidence


------------------------------------------------------------------------------
-- what is a pullback diagram?
------------------------------------------------------------------------------

 module _ {ga : Scope}(x y : Sub ga) where  -- fix two subscopes x and y
  ga0 = x .fst ; th0 = x .snd ; ga1 = y .fst ; th1 = y .snd
  -- th0 and th1 are the top half of the perimeter
  
  Plb : Set  -- what is their pullback? we need
  Plb = <(_<= ga0) :* (_<= ga1)> >< !\ /\ \ ph0 ph1       -- the bottom half
     -> Square (ph0 ^ th0) (ph1 ^ th1)    -- a square between left and right
     >< Pullback                      -- a proof that it's a pullback square


------------------------------------------------------------------------------
-- constructing pullback diagrams
------------------------------------------------------------------------------

 infix 7 _\^/_
 _\^/_ :  forall {ga0 ga ga1}(th0 : ga0 <= ga)(th1 : ga1 <= ga) ->
          Plb (! th0) (! th1)
 th0 -, b \^/ th1 -, .b = ! ! (th0 \^/ th1) .snd .snd -, b
 th0 -, b \^/ th1 -^ .b = ! ! (th0 \^/ th1) .snd .snd -,^ b
 th0 -^ b \^/ th1 -, .b = ! ! (th0 \^/ th1) .snd .snd -^, b
 th0 -^ b \^/ th1 -^ .b = ! ! (th0 \^/ th1) .snd .snd -^ b
 []       \^/ []        = ! ! []

{-
The program is short because the type is tight. We need only focus on the
pullback evidence, leaving the construction of the bottom half of the
perimeter and the square itself to the typechecker.

As you can see, we get -, in the output only when we have -, in both inputs.
If there is a ^ in either input, we get a ^ in the output, with more precise
information about whether the thing is missing from the right, the left, or
both.
-}


------------------------------------------------------------------------------
-- universal property
------------------------------------------------------------------------------

{-
If we have any old square with the same top half (th0 th1) as a pullback
square...

      /|\            /|\                     /|\    
  th0/ | \th1    th0/ | \th1             th0/ | \th1
    /  |  \        /  |  \                 /  |  \  
   <   |   >      <   |   >       =>      <   |   > 
   |   |   |       \  |  /                |\  |  /| 
   |   |   |        \ | /                 | \ | / | 
   |   |   |         \^/                  |  \^/  | 
    \  |  /                                \  !  /  
     \ | /                                  \ ! /   
      \|/                                    \!/

...then we have a subscope of th0 and of th1, so it must be a subscope of
their intersection. We get that the diagonal of our square factors uniquely
through the diagonal of the pullback, and that the mediating morphism
moreover makes the diagrams commute (i.e., we get the relevant arrows
between the subscopes in the slice category).
-}

 pullU : forall {ga} -> Sub ga !> /\ \ ga0 th0 -> Sub ga !> /\ \ ga1 th1
      -> <(_<= ga0) :* (_<= ga1)> !> !\ /\ \ ph0' ph1'
      -> (x : Square (ph0' ^ th0) (ph1' ^ th1))             -- any old square
      -> <(_<= ga0) :* (_<= ga1)> !> !\ /\ \ ph0 ph1
      -> {y : Square (ph0 ^ th0)  (ph1 ^ th1)} -> Pullback y    -- a pullback
      -> <(_& ph0 =< ph0') :* (_& fst y =< fst x) :* (_& ph1 =< ph1')>
-- in these two cases, the element is in the pullback, but is it in the other?
 pullU (v0 -, b  ^ v1 -, .b)  (p -, .b) =  -- yes it is!
   let ! w0 , w , w1 = pullU (v0 ^ v1) p in ! w0 -, b  , w -, b  , w1 -, b
 pullU (v0 -^, b ^ v1 -^, .b) (p -, .b) =  -- no it isn't!
   let ! w0 , w , w1 = pullU (v0 ^ v1) p in ! w0 -^, b , w -^, b , w1 -^, b
-- in the other three cases, it's not in the pullback and can't be in t'other
 pullU (v0 -^, b ^ v1 -^ .b) (p -,^ .b) = 
   let ! w0 , w , w1 = pullU (v0 ^ v1) p in ! w0 -^ b  , w -^ b  , w1
 pullU (v0 -^ b ^ v1 -^, .b) (p -^, .b) = 
   let ! w0 , w , w1 = pullU (v0 ^ v1) p in ! w0       , w -^ b  , w1 -^ b
 pullU (v0 -^ b ^ v1 -^ .b) (p -^ .b) = 
   let ! w0 , w , w1 = pullU (v0 ^ v1) p in ! w0       , w -^ b  , w1
-- empty to empty, as ever
 pullU ([] ^ []) [] = ! [] , [] , []

