------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Partition                                                 -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Partition where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma
open import Lib.Sum
open import Thin.Data
open import Thin.Triangle
open import Thin.Square
open import Thin.Cover
open import Thin.Pullback

module _ {B : Set} where  -- B is the type of bindings

 open THIN {B}

------------------------------------------------------------------------------
-- what is a partition?
------------------------------------------------------------------------------

 Part : forall {ga0 ga ga1}(th0 : ga0 <= ga)(th1 : ga1 <= ga) -> Set
 Part th0 th1 = th0 /u\ th1 * Pullback (no& th0 ^ no& th1)

{-
Two thinnings *partition* their shared target if they cover it and they are
disjoint. The latter is readily expressed as the property that the square of
degenerate triangles extruded from the empty scope is a pullback

              ga
             /u\
            /   \
         th0     th1
          /       \
         <         >
          \       /
           \     /
            \   /
             \^/
             []

-}


------------------------------------------------------------------------------
-- computing a subpartition
------------------------------------------------------------------------------

 infix 7 _<Part_

 _<Part_ : forall {de ga}                              (ph : de <= ga) ->
  forall {ga0 ga1}{th0 : ga0 <= ga}{th1 : ga1 <= ga} -> Part th0 th1 ->
  <(_<= ga0) :* (_<= de)> >< !\ /\ \ ph0 ps0 ->
  (Square (ph0 ^ th0) (ps0 ^ ph) >< Pullback) *
  <(_<= ga1) :* (_<= de)> >< !\ /\ \ ph1 ps1 ->
  (Square (ph1 ^ th1) (ps1 ^ ph) >< Pullback) *
  Part ps0 ps1
{-
              ga                 ga      
             /u\                /u\      
            / | \              / | \     
         th0  |  th1        th0  |  th1  
          /   |ph \          /   |ph \   
         <    |    >   =>   <    |    >   
          \       /         |   /u\   |
           \     /        ph0  /   \  ph1    
            \   /           |^ps0 ps1^|  
             \^/            |/       \|
             []              \       /  
                              \     /
                               \   /
                                \^/
                                []
-}
 ph <Part ((u -, b) , ())
 [] <Part ([] , []) = ! (! []) , ! (! []) , [] , []
 ph -, .b <Part (u -,^ b , p -,^ .b) = 
   let ! (! p0)       , ! (! p1)       , u'       , p'      = ph <Part (u , p)
   in  ! (! p0 -, b)  , ! (! p1 -^, b) , u' -,^ b , p' -,^ b
 ph -, .b <Part (u -^, b , p -^, .b) =  
   let ! (! p0)       , ! (! p1)       , u'       , p'      = ph <Part (u , p)
   in  ! (! p0 -^, b) , ! (! p1 -, b)  , u' -^, b , p' -^, b
 ph -^ .b <Part (u -,^ b , p -,^ .b) =  
   let ! (! p0)       , ! (! p1)       , u'       , p'      = ph <Part (u , p)
   in  ! (! p0 -,^ b) , ! (! p1 -^ b)  , u'       , p'
 ph -^ .b <Part (u -^, b , p -^, .b) =  
   let ! (! p0)       , ! (! p1)       , u'       , p'      = ph <Part (u , p)
   in  ! (! p0 -^ b)  , ! (! p1 -,^ b) , u'       , p'

{-
Four step cases:
  you're either being kept or being dropped (see thinning)
  you're either on the 0 side or the 1 side (see cover and pullback)

If you're being kept, you get put back in the cover and pullback, you're
marked present on your side and absent from the other side.

If you're being dropped, the cover and pullback are unextended, and you're
marked as dropped from your side and never having been on the other side.
-}


------------------------------------------------------------------------------
-- looking stuff up in a subpartition
------------------------------------------------------------------------------

{-
In the above picture, asking which side some i is on in the subpartition
should give the same answer as asking which side i -<- ph is on in the
whole partition, with appropriate diagrams commuting.
-}

 cover1Lemma : forall {de ga}{ph : de <= ga} ->
   forall {ga0 ga1}{th0 : ga0 <= ga}{th1 : ga1 <= ga} ->
   Part th0 th1 >> /\ \ u p ->
   <(_<= ga0) :* (_<= de)> !> !\ /\ \ ph0 ps0 ->
   Square (ph0 ^ th0) (ps0 ^ ph) ->
   <(_<= ga1) :* (_<= de)> !> !\ /\ \ ph1 ps1 ->
   Square (ph1 ^ th1) (ps1 ^ ph) ->
   Part ps0 ps1 >> /\ \ u' p' ->
   forall {b}(i : b <- de) ->
    (  (/\ \ j _ -> /\ \ k _ -> j & ph0 =< k)
    +R (/\ \ j _ -> /\ \ k _ -> j & ph1 =< k))
    (cover1 i u') (cover1 (i -<- ph) u)
 cover1Lemma {ph = ph} (u , p) s0 s1 (u' , p') i
   with cover1 i u' | i -&- ph | cover1 (i -<- ph) u
 cover1Lemma (u , p) (w0 ^ w1) _ (u' , p') i | inl (! v0) | ! w | inl (! v1)
   with assoc03 (v0 ^ w1)                ; ... | w2 ^ w3
   with w ~&~ w3 | assoc02 (w2 ^ w0)     ; ... | r~ , r~ | w4 ^ w5
   with w5 ~1&1~ v1                      ; ... | r~
   = inl w4
 cover1Lemma (u , p) (w0 ^ w1) _ (u' , p') i | inl (! v0) | ! w | inr (! v1)
   with assoc03 (v0 ^ w1)                ; ... | w2 ^ w3
   with w ~&~ w3 | assoc02 (w2 ^ w0)     ; ... | r~ , r~ | w4 ^ w5
   with pullU (w5 ^ v1) p                ; ... | () , _
 cover1Lemma (u , p) _ (w0 ^ w1) (u' , p') i | inr (! v0) | ! w | inl (! v1)
   with assoc03 (v0 ^ w1)                ; ... | w2 ^ w3
   with w ~&~ w3 | assoc02 (w2 ^ w0)     ; ... | r~ , r~ | w4 ^ w5
   with pullU (v1 ^ w5) p                ; ... | () , _   
 cover1Lemma (u , p) _ (w0 ^ w1) (u' , p') i | inr (! v0) | ! w | inr (! v1)
   with assoc03 (v0 ^ w1)                ; ... | w2 ^ w3
   with w ~&~ w3 | assoc02 (w2 ^ w0)     ; ... | r~ , r~ | w4 ^ w5
   with w5 ~1&1~ v1                      ; ... | r~
   = inr w4

{-
The first move is to grab the results of both cover1 tests (and triangulate
i -<- ph while we're about it).

That gives us four cases:
  in two, the tests agree, so we chase diagrams, effectively gluing the
    appropriate square to the triangle returned by the lower test and
    showing that it just is the triangle given by the upper;
  in two, the tests disagree, so we need a contradiction:
    fortunately, we have enough data (after more square gluing) to make a
    square which shows th0 and th1 have a nonempty intersection, because we
    found the same thing on both sides; said nonempty intersection needs
    must embed in the pullback, by universal property thereof... but the
    pullback is empty.
-}


------------------------------------------------------------------------------
-- partition left and right
------------------------------------------------------------------------------

 leftPart : forall ga -> Part (idth {ga}) (noth {ga})
 leftPart []        = [] , []
 leftPart (ga -, b) = let u , p = leftPart ga in u -,^ b , p -,^ b

 rightPart : forall ga -> Part (noth {ga}) (idth {ga})
 rightPart []        = [] , []
 rightPart (ga -, b) = let u , p = rightPart ga in u -^, b , p -^, b

 catPart : forall {ga} de -> Part (thinl {ga} de) (thinr {ga} de)
 catPart []        = leftPart _
 catPart (de -, b) = let u , p = catPart de in u -^, b , p -^, b
 
 tacPart : forall {ga} de -> Part (thinr {ga} de) (thinl {ga} de)
 tacPart []        = rightPart _
 tacPart (de -, b) = let u , p = tacPart de in u -,^ b , p -,^ b
 
