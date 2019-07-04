------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Square                                                    -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Square where

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

{-
If we have two paths round a square, when does the square commute?

     ---->de
    ^     ^
    |     |
    |  ?  |
    |     |
    |     |
   ga---->

When it's a pair of triangles!

     ---->de
    ^    ^^
    |   / |
    |  /  |
    | /   |
    |/    |
   ga---->
-}


------------------------------------------------------------------------------
-- Defining squares
------------------------------------------------------------------------------

 module _ {ga de : Bwd B} where

  module _ (a b : <(ga <=_) :* (_<= de)>) where -- two paths, hiding corners

   Square : Set
   Square = let th0 ^ ph0 = a ; th1 ^ ph1 = b in
     <(th0 & ph0 =<_) :* (th1 & ph1 =<_)> -- two triangles, hiding diagonal

  -- We can flip a square on its diagonal.

  opSq : forall {a b} -> Square a b -> Square b a
  opSq (v ^ w) = w ^ v


------------------------------------------------------------------------------
-- Composing squares
------------------------------------------------------------------------------

{-
          ps2                        ps2                        ps2
         ---->                      ---->                      ---->      
       ^^    ^^^                  ^     ^^^                  ^     ^ ^    
      / | v1/ | \                /     /|| \                /      |  \   
     /  |  /  |  \              /     / /|  \              /       /   \  
    /   | /vw1|   \            /     / / |   \            /       |     \ 
   | th1|/ps1 |ph1 |          |     / |w2|    |          |        /      | 
 th| v   ---->   w |ph  =>  th| v1 |v'|w'| w1 |ph  =>  th|  v1   |   w1  |ph
   | th0^    ^^ph0 |          |    |v2|  /    |          |       /       | 
    \   |vw0/ |   /            \   |  / /    /            \     |       /
     \  |  /  |  /              \  | / /    /              \    /      /  
      \ | /w0 | /                \ || /    /                \  |      /   
       \|/    |/                  \|//    /                  \ /     /    
         ---->                      ---->                      ----> 
          ps0                        ps0                        ps0         
-}

 coSq : PreTri \ th0 th1 th -> th0 & th1 =< th ->
         PreTri \ ph0 ph1 ph -> ph0 & ph1 =< ph ->
   forall {ps0 ps1 ps2} ->
   Square (ps0 ^ ph0) (th0 ^ ps1) -> Square (ps1 ^ ph1) (th1 ^ ps2) ->
   Square (ps0 ^ ph) (th ^ ps2)
 coSq v w (w0 ^ vw0) (vw1 ^ v1)
   with assoc03 (v ^ v1) | assoc03 (vw0 ^ vw1) | assoc03 (w0 ^ w)
 ... | v2 ^ w1 | v' ^ w' | v0 ^ w2
   with v' ~&~ v2 | w' ~&~ w2
 ... | r~ , r~ | r~ , r~ = v0 ^ w1
