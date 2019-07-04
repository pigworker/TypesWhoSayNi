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
(I follow the convention (good for thinnings) that arrows go up, so
arrowheads are surplus to requirements.)

         de
        / \
       /   \
      /     \
     <   ?   >
      \     /  
       \   /
        \ /
        ga

When it's a pair of triangles!

         de
        /|\
       / | \
      /  |  \
     <   |   >
      \  |  /  
       \ | /
        \|/
        ga
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
If I have two squares, when can I paste them together?

       ,-----'/|\                ,-----'/|\                ,------'|\        
      /      / | \              /      /|| \              /        | \       
     /    ph1  |  ps2          /      / /|  ps2          /        /   ps2    
    /      /   |   \          /      / | |   \          /        |     \     
  ph      /    |    \       ph      /  | |    \       ph         |      \    
  /   w  ; wv1 | v1  >      /      | w1/ |     %      /          /       %   
 |      /|\    |    / \    |       |  |  |      \    |          |         \  
 |     / | \   |   /   |   |       |  |  |       |   |          |          | 
 |  ph0  | ps1 |  th1  |   |  w'   |w2:v2|    v' |   | w'       |       v' |
 |   /   |   \ | /     |   |       |  |  |       |   |          |          |
  \ /    |    \|/      |    \      |  |  |       |    \         |          | 
   <  w0 | wv0 ;  v   /      %     | /v0 |      /      %       /          /  
    \    |    /      th       \    | |  /      th       \      |         th  
     \   |   /      /          \   | | /      /          \     |        /    
    ps0  |  th0    /    ==>   ps0  |/ /      /    ==>   ps0   /        /    
       \ | /      /              \ ||/      /              \ |        /      
        \|/,-----'                \|/,-----'                \|,------'       
-}

 coSq : PreTri \ th0 th1 th -> th0 & th1 =< th ->
        PreTri \ ph0 ph1 ph -> ph0 & ph1 =< ph ->
        forall {ps0 ps1 ps2} ->   Square (ps0 ^ ph0) (th0 ^ ps1) ->
                                  Square (ps1 ^ ph1) (th1 ^ ps2) ->
                                  Square (ps0 ^ ph)  (th  ^ ps2)
 coSq v w (w0 ^ wv0) (wv1 ^ v1)
   with assoc03 (w0 ^ w) | assoc03 (wv0 ^ wv1) | assoc03 (v ^ v1)
 ... | w' ^ w2 | v0 ^ w1 | v2 ^ v'
   with w2 ~&~ w1 | v0 ~&~ v2
 ... | r~ , r~ | r~ , r~ = w' ^ v'

{-
Looking at the left diagram, gluing w0 to w and v to v1 should at least get
us two triangles with the correct "outsides": but do they meet in the middle?
Well, the triangles wv0 and wv1 form a commuting square, which we can
collapse. Associating w0 with w, wv0 with wv1, and v with v1, we obtain six
new triangles, including the outer triangles we want and two copies of the
same inner triangles we see in the middle diagram. At least, they have the
same components, but we need them to have the same composites, but the
former implies the latter, which causes the collapse we need.
-}
