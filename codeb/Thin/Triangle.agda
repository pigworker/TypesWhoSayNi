------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Triangle                                                  -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Triangle where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma
open import Thin.Data

module _ {B : Set} where  -- B is the type of bindings

 open THIN {B}


------------------------------------------------------------------------------
-- pretriangles
------------------------------------------------------------------------------

{-
A "pretriangle" is a trio of thinnings which meet three points.

                      ze
                      /|
                   ph/ |
                    /  |
                 de< ? |ps
                    \  |
                   th\ |
                      \|
                      ga

Does the diagram commute? That is the question!
-}

 -- quantifying over "pretriangles" happens a lot, so I abstract it
 PreTri : forall {l} ->
   (forall {ga de ze} -> ga <= de -> de <= ze -> ga <= ze -> Set l) -> Set l
 PreTri T = forall {ga de ze}{th : ga <= de}{ph : de <= ze}{ps : ga <= ze} ->
   T th ph ps


------------------------------------------------------------------------------
-- Triangles
------------------------------------------------------------------------------

{-
Let's say when a pretriangle commutes.

Fortran: proofs that triangles commute are often called v and w, because
v looks a bit triangular and w is its friend.
-}

 infixl 8 _-^,_
 infix 7 _&_=<_
 
 data _&_=<_ : forall {iz jz kz}
   (th : iz <= jz)(ph : jz <= kz)(ps : iz <= kz) -> Set where
   
   []    :

     -------------------------------------
          []    &     []    =<     []
   
   _-,_  : PreTri \ th ph ps ->

       th       &  ph       =<  ps      -> forall b ->
     ---------------------------------------------------
       th -, b  &  ph -, b  =<  ps -, b
           
   _-^,_ : PreTri \ th ph ps ->

       th       &  ph       =<  ps      -> forall b ->
     ---------------------------------------------------   
       th -^ b  &  ph -, b  =<  ps -^ b
     
   _-^_  : PreTri \ th ph ps ->

       th       &  ph       =<  ps      -> forall b ->
     ---------------------------------------------------
       th       &  ph -^ b  =<  ps -^ b

 -- quantifying over triangles which commute is rather common, too.
 Tri : forall {l} -> (PreTri \ th ph ps -> th & ph =< ps -> Set l) -> Set l
 Tri T = PreTri \ th ph ps -> th & ph =< ps >> T


------------------------------------------------------------------------------
-- Triangles are the graph of the composition function
------------------------------------------------------------------------------

-- First, show that the specification is satisfiable.

 infixl 8 _-&-_
 
 _-&-_ : forall {ga de ze}(th : ga <= de)(ph : de <= ze) -> <(th & ph =<_)>
 th       -&- (ph -^ b) = ! (th -&- ph) .snd -^ b
 th -, .b -&- (ph -, b) = ! (th -&- ph) .snd -, b
 th -^ .b -&- (ph -, b) = ! (th -&- ph) .snd -^, b
 []       -&- []        = ! []

-- The composition function is the witness.

 infixl 8 _-<-_

 _-<-_ : forall {ga0 ga1 ga2} -> ga0 <= ga1 -> ga1 <= ga2 -> ga0 <= ga2
 th -<- ph = (th -&- ph) .fst

-- Now show that whenever the inputs agree, so do the outputs and proofs.

 infix 7 _~&~_
 
 _~&~_ : PreTri \ th ph ps -> forall {ps'} ->
   (v : th & ph =< ps)(w : th & ph =< ps') -> ps ~ ps' >< \ { r~ -> v ~ w }
 [] ~&~ [] = r~ , r~
 v0 -, b  ~&~ v1 -, .b  with v0 ~&~ v1 ; ... | r~ , r~ = r~ , r~
 v0 -^, b ~&~ v1 -^, .b with v0 ~&~ v1 ; ... | r~ , r~ = r~ , r~
 v0 -^ b  ~&~ v1 -^ .b  with v0 ~&~ v1 ; ... | r~ , r~ = r~ , r~

-- Gallas's "using" gadget will make the above much sweeter.

 eq& : PreTri \ th ph ps -> th & ph =< ps -> th -<- ph ~ ps
 eq& {th = th}{ph} v with th -&- ph
 ... | ! w with v ~&~ w
 ... | r~ , r~ = r~


------------------------------------------------------------------------------
-- Thinnings are monomorphisms
------------------------------------------------------------------------------

 infix 7 _~1&1~_
 
 _~1&1~_ : PreTri \ th0 ph ps -> forall {th1} ->
   th0 & ph =< ps -> th1 & ph =< ps -> th0 ~ th1
 [] ~1&1~ [] = r~
 v0 -, x  ~1&1~ v1 -, .x  rewrite v0 ~1&1~ v1 = r~
 v0 -^, x ~1&1~ v1 -^, .x rewrite v0 ~1&1~ v1 = r~
 v0 -^ x  ~1&1~ v1 -^ .x  rewrite v0 ~1&1~ v1 = r~


------------------------------------------------------------------------------
-- Degenerate triangles
------------------------------------------------------------------------------

 infix 9 _&id
 _&id : forall {ga de}(th : ga <= de) -> th & idth =< th
 []        &id = []
 (th -, x) &id = th &id -, x
 (th -^ x) &id = th &id -^, x

 id& : forall {ga de}(th : ga <= de) -> idth & th =< th
 id& []        = []
 id& (th -, x) = id& th -, x
 id& (th -^ x) = id& th -^ x

 no& : forall {ga de}(th : ga <= de) -> noth & th =< noth
 no& []        = []
 no& (th -, x) = no& th -^, x
 no& (th -^ x) = no& th -^ x

 no&' : forall {ga de}(th : [] <= ga)(ph : ga <= de)(ps : [] <= de) ->
   th & ph =< ps
 no&' th ph ps rewrite noth! th noth | noth! ps noth = no& ph


------------------------------------------------------------------------------
-- Associators
------------------------------------------------------------------------------

{-
When we have a sequence of three arrows, th , ph , ps, a commuting square must
exist, with two diagonals and four triangles.

      ph
   1----->2
   ^\    ^|
   | \  / |
   |  \/  |ps
 th|  /\  |
   | /  \ |
   |/    vv
   0----->3

Such a diagram may be completed when one of the unlabelled arrows is missing,
together with its triangles.

This amounts to witnessing associativity in various forms.
-}


 assoc03 : forall {ga0 ga1 ga2 ga3}{th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th02 : ga0 <= ga2}{th13 : ga1 <= ga3} ->
   <(th01 &_=< th02) :* (_& th23 =< th13)> ->
   <(th01 & th13 =<_) :* (th02 & th23 =<_)>
{-
   1----->2
   ^\    ^|
   | \  / |
   |  \/  |
   |  /\  |
   | /  \ |
   |/    vv
   0.....>3
-}
 assoc03 (v        ^ w -^ x)  =
   let v ^ w = assoc03 (v ^ w) in   v -^ x  ^ w -^ x
 assoc03 (v -^ .x  ^ w -^, x) =
   let v ^ w = assoc03 (v ^ w) in   v -^ x  ^ w -^, x
 assoc03 (v -^, .x ^ w -, x)  =
   let v ^ w = assoc03 (v ^ w) in   v -^, x ^ w -^, x
 assoc03 (v -, .x  ^ w -, x)  =
   let v ^ w = assoc03 (v ^ w) in   v -, x  ^ w -, x
 assoc03 ([] ^ [])            =     []      ^ []

{-
The above requires induction, not to construct candidates for the missing
triangles, but rather to show that they have the *same* missing side: that's
your actual associativity.

The other two follow as corollaries.
-}


 assoc13 : forall {ga0 ga1 ga2 ga3}{th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th12 : ga1 <= ga2}{th03 : ga0 <= ga3} ->
   <(th01 & th12 =<_) :* (_& th23 =< th03)> ->
   <(th01 &_=< th03) :* (th12 & th23 =<_)>
{-
   1----->2
   ^.    ^|
   | .  / |
   |  ./  |
   |  /.  |
   | /  . |
   |/    vv
   0----->3
-}
 assoc13 {th23 = th23}{th12 = th12} (v ^ w) with th12 -&- th23
 ... | ! w' with assoc03 (v ^ w')
 ... | v' ^ w2 with w ~&~ w2
 ... | r~ , r~ = v' ^ w'


 assoc02 : forall {ga0 ga1 ga2 ga3}{th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th03 : ga0 <= ga3}{th12 : ga1 <= ga2} ->
   <(th01 &_=< th03) :* (th12 & th23 =<_)> ->
   <(th01 & th12 =<_) :* (_& th23 =< th03)>
{-
   1----->2
   ^\    ^|
   | \  . |
   |  \.  |
   |  .\  |
   | .  \ |
   |.    vv
   0----->3
-}
 assoc02 {th01 = th01}{th12 = th12} (v ^ w) with th01 -&- th12
 ... | ! v' with assoc03 (v' ^ w)
 ... | v2 ^ w' with v ~&~ v2
 ... | r~ , r~ = v' ^ w'
   

------------------------------------------------------------------------------
-- Category laws for <= idth -<-
------------------------------------------------------------------------------

 _<id : forall {ga de}(th : ga <= de) -> th -<- idth ~ th
 th <id with th -&- idth ; ... | ! v with v ~&~ th &id ; ... | r~ , r~ = r~
 
 id< : forall {ga de}(th : ga <= de) -> idth -<- th ~ th
 id< th with idth -&- th ; ... | ! v with v ~&~ id& th ; ... | r~ , r~ = r~

 assoc< : forall {ga0 ga1 ga2 ga3}
   (th : ga0 <= ga1)(ph : ga1 <= ga2)(ps : ga2 <= ga3) ->
   th -<- (ph -<- ps) ~ (th -<- ph) -<- ps
 assoc< th ph ps with th -&- ph | ph -&- ps
 ... | thph , v | phps , w with thph -&- ps | th -&- phps | assoc03 (v ^ w)
 ... | ! v0 | ! w0 | w1 ^ v1 with v0 ~&~ v1 | w0 ~&~ w1
 ... | r~ , r~ | r~ , r~ = r~

{-
The above proofs were constructed mindlessly in approved diagram-chasing
fashion. There are two stages:
  1. If you see th -<- ph, go with th -<- ph.
  2. Now that you have only variables and triangles, degenerate the diagram
     using ~&~.
-}


------------------------------------------------------------------------------
-- Growing triangles by composition
------------------------------------------------------------------------------

 module _ {ga de xi om : _}{th : ga <= de}{ph : de <= xi}{ps : ga <= xi} where
 
  _&<_ : th & ph =< ps -> (ch : xi <= om) -> th & ph -<- ch =< ps -<- ch
  v &< ch with ph -&- ch | ps -&- ch
  ... | ! w1 | ! w with assoc03 (v ^ w1)
  ... | v' ^ w' with w ~&~ w' ; ... | r~ , r~ = v'

  _<&_ : (ch : om <= ga) -> th & ph =< ps -> ch -<- th & ph =< ch -<- ps
  ch <& v with ch -&- th | ch -&- ps
  ... | ! w | ! v0 with assoc02 (v0 ^ v)
  ... | w' ^ v' with w ~&~ w' ; ... | r~ , r~ = v'

{-
As you might expect, approved mindless style does the job again.
Abstracting the compositions gives us *three* triangles, not including
the missing one. Associativity gives us two more triangles, one of which
degenerates the diagram, the other of which we want.
-}


------------------------------------------------------------------------------
-- Growing triangles by composition
------------------------------------------------------------------------------

{-
Selections from a given subscope are given by fixing the target, forming
the slice category => / ga.
-}

 Sub : Scope -> Set
 Sub ga = <(_<= ga)>

{- Objects in Sub ga are given by (ga' , th) : <(_<= ga)>
   Morphisms from (ga' , th) to (de , ps) are given by
   (th' , v) : <(_& ps =< th)>, i.e., a thinning from ga' to de
   which makes the diagram commute.
-}

 infix 7 _<&=_
 _<&=_ : forall {ga} -> Sub ga -> Sub ga -> Set
 (! th) <&= (! ps) = <(_& ps =< th)>
 
