------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Cover                                                     -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Cover where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma
open import Lib.Sum
open import Thin.Data
open import Thin.Triangle

module _ {B : Set} where  -- B is the type of bindings

 open THIN {B}


------------------------------------------------------------------------------
-- What is a cover?
------------------------------------------------------------------------------

{-
When we have a diagram like this (arrows go upwards; sod the heads)

                ga
               / \
              /   \
           th/     \ph
            /       \
          ga0      ga1

it can be useful (e.g., in the enforcement of relevance invariants) to
know that everything in ga is hit by either th or ph, and is thus
represented in ga0 or ga1 (inclusively).

When this is true, we say that th and ph form a cover, and we draw

                ga
               ^u^
              /   \
           th/     \ph
            /       \
          ga0      ga1

Let us define covers inductively.
-}

 infix 7 _/u\_
 infixl 8 _-,^_
 data _/u\_ : forall {ga0 ga ga1} -> ga0 <= ga -> ga1 <= ga -> Set where
 
   [] :

     ---------------------
         []    /u\    []
   
   _-,^_ : forall {ga0 ga ga1}{th : ga0 <= ga}{ph : ga1 <= ga} ->
   
       th      /u\ ph      -> forall b ->
     --------------------------------------  
       th -, b /u\ ph -^ b
     
   _-^,_ : forall {ga0 ga ga1}{th : ga0 <= ga}{ph : ga1 <= ga} ->
   
       th      /u\ ph      -> forall b ->
     --------------------------------------  
       th -^ b /u\ ph -, b
     
   _-,_  : forall {ga0 ga ga1}{th : ga0 <= ga}{ph : ga1 <= ga} ->
   
       th      /u\ ph      -> forall b ->
     --------------------------------------  
       th -, b /u\ ph -, b

{-
Note the absence of a case for -^ -^. Everybody's got to be somewhere.

Fortran: covers will typically be called u.

Now, the situation where -, -, is also excluded, i.e., everything in
ga is in *exactly* one of ga0 or ga1 is called a *partition*. I'll get
back to those in Thin.Pullback, which is all about intersections. A
partition is a cover formed by thinnings with an empty intersection.
-}


------------------------------------------------------------------------------
-- Covers contain no bits
------------------------------------------------------------------------------

 infix 7 _~/u\~_

 _~/u\~_ : forall {ga0 ga ga1}{th : ga0 <= ga}{ph : ga1 <= ga}
   (u u' : th /u\ ph) -> u ~ u'
 []      ~/u\~ []                           = r~
 u -,^ b ~/u\~ u' -,^ .b rewrite u ~/u\~ u' = r~
 u -^, b ~/u\~ u' -^, .b rewrite u ~/u\~ u' = r~
 u -, b  ~/u\~ u' -, .b  rewrite u ~/u\~ u' = r~

{-
It is, however, a win to work with the evidence that two thinnings form a
cover, rather than with the thinnings themselves.
-}


------------------------------------------------------------------------------
-- Covers have left and right thinnings
------------------------------------------------------------------------------

 module _ {ga0 ga ga1}{th : ga0 <= ga}{ph : ga1 <= ga}(u : th /u\ ph)
  where
  u/ : ga0 <= ga  ;  u\ : ga1 <= ga
  u/ = th         ;  u\ = ph

{-
We can spend less effort bringing thinnings into scope if we say where they
live with respect to covers. Arguably, I should have pulled this move with
triangles.
-}


------------------------------------------------------------------------------
-- Everybody's got to be somewhere
------------------------------------------------------------------------------

{-
If we have a scope covered, every index into it factors either through
the left or the right injection of the cover.

If both, I incline to the left.
-}

 cover1 : forall {ga0 ga ga1 : Scope}{b}(i : b <- ga)
   {th : ga0 <= ga}{ph : ga1 <= ga}(u : th /u\ ph) ->
     <(_& u/ u =< i)> + <(_& u\ u =< i)>
 cover1 (i -, b) (u -,^ .b)   rewrite noth! i noth = inl (! no& _ -, b)
 cover1 (i -, b) (u -^, .b)   rewrite noth! i noth = inr (! no& _ -, b)
 cover1 (i -, b) (u -, .b)    rewrite noth! i noth = inl (! no& _ -, b)
 cover1 (i -^ b) (u -,^ .b)   with cover1 i u
 ... | inl (! v) = inl (! v -^, b)
 ... | inr (! v) = inr (! v -^ b)
 cover1 (i -^ b) (u -^, .b)   with cover1 i u
 ... | inl (! v) = inl (! v -^ b)
 ... | inr (! v) = inr (! v -^, b)
 cover1 (i -^ b) (u -, .b)    with cover1 i u
 ... | inl (! v) = inl (! v -^, b)
 ... | inr (! v) = inr (! v -^, b)


