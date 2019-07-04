------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Is Your Journey Really Necessary?                         -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.IYJRN where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma
open import Lib.Sum
open import Thin.Data
open import Thin.Triangle
open import Thin.Cover
open import Thin.Square
open import Thin.Pullback

module _ {B : Set} where  -- B is the type of bindings

 open THIN {B}

 infix 7 _u<_  -- not the ideal name for an infix operator
 _u<_ : forall {ga0 ga1 ga}{th0 : ga0 <= ga}{th1 : ga1 <= ga} ->
   th0 /u\ th1 -> forall {de}(ps : ga <= de) ->
   (<(ga0 <=_) :* (_<= de)> * <(ga1 <=_) :* (_<= de)>) ><
   /\ !\ /\ \ ps0 ph0 -> !\ /\ \ ps1 ph1 -> ph0 /u\ ph1 *
   (Square (th0 ^ ps) (ps0 ^ ph0) * Square (th1 ^ ps) (ps1 ^ ph1)) ><
   /\ \ s0 s1 -> Pullback s0 * Pullback s1
 u        u< th -^ x = let ! u       , ! a       , b       = u u< th
                       in  ! u -, x  , ! a -^, x , b -^, x
 u -,^ .x u< th -, x = let ! u       , ! a       , b       = u u< th
                       in  ! u -,^ x , ! a -, x  , b -,^ x
 u -^, .x u< th -, x = let ! u       , ! a       , b       = u u< th
                       in  ! u -^, x , ! a -,^ x , b -, x 
 u -, .x  u< th -, x = let ! u       , ! a       , b       = u u< th
                       in  ! u -, x  , ! a -, x  , b -, x
 []       u< []      =     ! []      , ! []      , []

 infix 7 _<u_
 _<u_ : forall {ga de0 de1 de}(th : ga <= de)
   {ph0 : de0 <= de}{ph1 : de1 <= de} -> ph0 /u\ ph1 ->
   <(_<= de0) :* (_<= ga)> >< /\ \ ga0 -> /\ \ th0 ps0 ->
   <(_<= de1) :* (_<= ga)> >< /\ \ ga1 -> /\ \ th1 ps1 ->
   (Square (th0 ^ ph0) (ps0 ^ th) >< Pullback) *
   (Square (th1 ^ ph1) (ps1 ^ th) >< Pullback) *
   ps0 /u\ ps1
 []       <u []      =     ! ! (! [])      , (! [])      , []
 th -, .x <u u -,^ x = let ! ! (! a)       , (! b)       , u = th <u u
                       in  ! ! (! a -, x)  , (! b -^, x) , u -,^ x
 th -^ .x <u u -,^ x = let ! ! (! a)       , (! b)       , u = th <u u
                       in  ! ! (! a -,^ x) , (! b -^ x)  , u
 th -, .x <u u -^, x = let ! ! (! a)       , (! b)       , u = th <u u
                       in  ! ! (! a -^, x) , (! b -, x)  , u -^, x
 th -^ .x <u u -^, x = let ! ! (! a)       , (! b)       , u = th <u u
                       in  ! ! (! a -^ x)  , (! b -,^ x) , u
 th -, .x <u u -, x  = let ! ! (! a)       , (! b)       , u = th <u u
                       in  ! ! (! a -, x)  , (! b -, x)  , u -, x
 th -^ .x <u u -, x  = let ! ! (! a)       , (! b)       , u = th <u u
                       in  ! ! (! a -,^ x) , (! b -,^ x) , u

 puller : forall {ga' ga0 ga1 ga}
   {th0 : ga0 <= ga}{th1 : ga1 <= ga}{th0' : ga' <= ga0}{th1' : ga' <= ga1}
   {s : Square (th0' ^ th0) (th1' ^ th1)} -> Pullback s ->
   forall {de0}{ph0 : de0 <= ga0}{ps0 : de0 <= ga} -> ph0 & th0 =< ps0 ->
   forall {de1}{ph1 : de1 <= ga1}{ps1 : de1 <= ga} -> ph1 & th1 =< ps1 ->
   <(_<= de0) :* (_<= de1)> >< !\ /\ \ ch0 ch1 -> 
   Square (ch0 ^ ps0) (ch1 ^ ps1) >< \ s' -> Pullback s' *
   <(\ om -> Square (om ^ th0') (ch0 ^ ph0)) :* (_& fst s =< fst s') :*
    (\ om -> Square (om ^ th1') (ch1 ^ ph1))>
 puller s {ps0 = ps0} v0 {ps1 = ps1} v1 with ps0 \^/ ps1
 ... | ch0 ^ ch1 , (w0 ^ w1) , s'
   with assoc02 (w0 ^ v0) | assoc02 (w1 ^ v1)
 ... | x0 ^ y0 | x1 ^ y1 with pullU (y0 ^ y1) s
 ... | ! z0 , z , z1 = ! ! s' , ! z0 ^ x0 , z , z1 ^ x1
