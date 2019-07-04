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


------------------------------------------------------------------------------
-- Coproduct diagrams
------------------------------------------------------------------------------

{-
If we have two subscopes of ga, (ga0 , th) and (ga1 , ph), their union is
given by the coproduct in the slice category, Sub ga.

The coproduct of (ga0 , th) and (ga1 , ph) is some (de , ps) with injections
(th' , v0) and (ph' , v1) such that th' and ph' cover de.

In effect, ps is the union of the selections made by th and ph, but we also
know it *is* the union.
-}

 module _ {ga : Scope}(x y : Sub ga) where  -- fix two subscopes, x and y
  ga0 = x .fst ; th = x .snd ; ga1 = y .fst ; ph = y .snd
  
  Cop : Set  -- what is their coproduct?
  Cop = Sub ga >< /\ \ de ps              -- an object in Sub ga with...
     -> (ga0 <= de      * ga1 <= de     ) >< /\ \ th' ph'
     ->  th' & ps =< th * ph' & ps =< ph  -- ...morphisms from x and y...
      * th' /u\ ph'                       -- ...which form a cover

{-
Now let's compute a coproduct diagram for any two thinnings with the same
target.

In essence, it's a fancification of bitwise or, recording the evidence
that we really are computing a union.
-}

 infix 7 _/+\_
 
 _/+\_ : forall {ga0 ga ga1}(th : ga0 <= ga)(ph : ga1 <= ga) ->
         Cop (! th) (! ph)
 []      /+\ []       =     ! ! []      , []      , []      
 th -, b /+\ ph -, .b = let ! ! v       , w       , u       = th /+\ ph
                        in  ! ! v -, b  , w -, b  , u -, b  
 th -, b /+\ ph -^ .b = let ! ! v       , w       , u       = th /+\ ph
                        in  ! ! v -, b  , w -^, b , u -,^ b 
 th -^ b /+\ ph -, .b = let ! ! v       , w       , u       = th /+\ ph
                        in  ! ! v -^, b , w -, b  , u -^, b 
 th -^ b /+\ ph -^ .b = let ! ! v       , w       , u       = th /+\ ph
                        in  ! ! v -^ b  , w -^ b  , u
--   ^           ^                 ^^        ^^        ^^
--   |           |                /  \      /  \      /  \
--   X           Y               X   X|Y   Y   Y|X ; X    Y only if X|Y
{-
The left and right triangles record how the given element relates to its
injection: included, excluded though present in the union, absent.
The cover records the provenance of what is present in the union, but
says nothing about what is absent.
-}

{-
To show that this concrete definition of a coproduct diagram is rightly
named, let us check that it satisfies the universal property of a
coproduct. If we have morphisms in Sub ga from (ga0 , th) and (ga1 , ph)
to any other (de' , ps'), then there must be a unique morphism from our
(de , ps) to (de' , ps'). We get the uniqueness for free because such a
morphism is given by <(_& ps' =< ps)>, and we know (thinnings are mono)
that there is at most one such thing.
-}

 copU : forall {ga0 ga ga1}{th : ga0 <= ga}{ph : ga1 <= ga}
   {de'}{ps' : de' <= ga}{th' ph'} -> th' & ps' =< th -> ph' & ps' =< ph ->
   (c : Cop (! th) (! ph)) -> let (! ps) , _ , _ , _ , u = c in
    <(u/ u &_=< th') :* (_& ps' =< ps) :* (u\ u &_=< ph')>
  --         w0                 v                 w1
    
{-
         _,-- --,_        Given v0 : th' & ps' =< th, v1 : ph' & ps' =< ph
        /    |    \       then ps' must be *at least* the union of th and ph.
       /     |ps'  \      
    th/      |      \ph   That is, if we have any coproduct diagram for
     /  v0  /!\  v1  \    th and ph, its "union", ps (the line up the middle)
    |      /.!.\      |   must embed in ps' (triangle v, below) in a way
    | th','..!..`,ph' |   that's consistent with th' and ph' (triangles w0 and
    | ,-'w0_/u\_w1`-, |   w1).
    |/..,-'     `-,..\|
    |--'           '--|
-}

 copU [] [] (! ! [] , [] , []) = ! [] , [] , []
 copU (v0 -, b)  (v1 -, .b)  (! ! wv0 -, .b  , wv1 -, .b  , u -, .b)  =
   let ! w0       , v       , w1         = copU v0 v1 (! ! wv0 , wv1 , u)
   in  ! w0 -, b  , v -, b  , w1 -, b
 copU (v0 -, b)  (v1 -^, .b) (! ! wv0 -, .b  , wv1 -^, .b , u -,^ .b) = 
   let ! w0       , v       , w1         = copU v0 v1 (! ! wv0 , wv1 , u)
   in  ! w0 -, b  , v -, b  , w1 -^, b
 copU (v0 -^, b) (v1 -, .b)  (! ! wv0 -^, .b , wv1 -, .b  , u -^, .b) = 
   let ! w0       , v       , w1         = copU v0 v1 (! ! wv0 , wv1 , u)
   in  ! w0 -^, b , v -, b  , w1 -, b
 copU (v0 -^, b) (v1 -^, .b) (! ! wv0 -^ .b  , wv1 -^ .b  , u)        = 
   let ! w0       , v       , w1         = copU v0 v1 (! ! wv0 , wv1 , u)
   in  ! w0 -^ b  , v -^, b , w1 -^ b
 copU (v0 -^ b)  (v1 -^ .b)  (! ! wv0 -^ .b  , wv1 -^ .b  , u)        = 
   let ! w0       , v       , w1         = copU v0 v1 (! ! wv0 , wv1 , u)
   in  ! w0       , v -^ b  , w1
 copU (v0 -^, b) (v1 -^, .b) (! ! wv0 -^, .b , wv1 -^, .b , ())
 copU (v0 -^ b)  (v1 -^ .b)  (! ! wv0 -^, .b , wv1 -^, .b , ())


------------------------------------------------------------------------------
-- Coproduct diagrams are unique
------------------------------------------------------------------------------

{-
Note that the universal property applies to any coproduct diagram (not just
that computed by /+\). In fact, there is exactly one such diagram, as a
consequence of the universal property. 
-}

 copQ : forall {ga}{x y : Sub ga}(c0 c1 : Cop x y) -> c0 ~ c1
 copQ c0@(_ , (th , ph) , v00 , v01 , u0) c1@((! ps) , _ , v10 , v11 , u1)
   with copU v10 v11 c0 | copU v00 v01 c1
 ... | ps0 , w0 , v0 , w1 | ps1 , _
   with antisym ps0 ps1                  -- both mediating maps are idth
 ... | r~ , r~ , r~
   with w0 ~&~ th &id | v0 ~&~ id& ps | w1 ~&~ ph &id   -- splat
 ... | r~ , r~ | r~ , r~ | r~ , r~
   with v00 ~&~ v10 | v01 ~&~ v11 | u0 ~/u\~ u1         -- splat!
 ... | r~ , r~ | r~ , r~ | r~ = r~

