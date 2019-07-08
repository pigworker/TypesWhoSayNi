module Thin.Diagram where

open import Lib.Equality
open import Lib.One
open import Lib.Sigma
open import Lib.Index
open import Lib.Bwd
open import Lib.Maybe
open import Thin.Data
open import Thin.Triangle
open import Thin.Select
open import Thin.Cover
open import Thin.Pullback
open import Thin.Partition

open THIN

thq? : forall {X}{x y : X}{xs}(i : x <- xs)(j : y <- xs) ->
  Maybe (x ~ y >< \ { r~ -> i ~ j })
thq? i j with i \^/ j
... | _ , _ , ([] -, b) = yes (r~ , r~)
... | _ , _ , _ = no

module DIAGRAM {B : Set} where

 data Dag : Bwd (Bwd B) -> Set where
   [] : Dag []
   _-,_ : forall {gaz de} ->
     Dag gaz -> Env (\ ga -> Bwd (ga <= de)) gaz -> Dag (gaz -, de)

 growCut : forall {ga ze : Bwd B}{gaz nuz} ->
          Env (\ de -> Bwd (de <= ga)) gaz ->
          ga <= ze ->
          Env (_<= ze) nuz ->
          nuz <= gaz ->
          <(nuz <=_) :* (_<= gaz)> >< /\ \ nuz' _ -> Env (_<= ze) nuz'
 growCut x ps nz [] = [] ^ [] , []
 growCut (x -, _) ps (nz -, n) (th -, b) with growCut x ps nz th
 ... | nu ^ ph , nz' = nu -, b ^ ph -, b , nz' -, n
 growCut (x -, []) ps nz (th -^ b) with growCut x ps nz th
 ... | nu ^ ph , nz' = nu ^ ph -^ b , nz'
 growCut (x -, (mz -, m)) ps nz (th -^ b) with growCut x ps nz th
 ... | nu ^ ph , nz' = nu -^ b ^ ph -, b , nz' -, (m -<- ps)

 nuke : forall {nuz gaz} -> nuz <= gaz -> Env (_<= []) nuz -> Dag gaz ->
   Sub gaz >< /\ \ nuz' th0 -> Sub gaz >< /\ \ gaz' th1 ->
   Env (_<= []) nuz' * nuz <= nuz' *
   Dag nuz' * Part th0 th1 * Dag gaz' *
   Env (\ ga -> Env (\ nu -> Bwd (nu <= ga)) nuz') gaz'
 nuke [] [] [] = (! []) , (! []) , [] , [] , [] , ([] , []) , [] , []
 nuke (th -, ga) (nz -, ps)  (d -, x) with growCut x ps nz th
 ... | ph ^ th' , nz' with nuke th' nz' d
 ... | (! th0) , (! th1) , nz'' , ph' , nd , (u , p) , d' , noz
     = (! th0 -, ga) , (! th1 -^ ga) , nz'' -, ps , ph -<- ph' -, ga
     , nd -, (th0 <? x) , (u -,^ ga , p -,^ ga) , d' , env (_-, []) noz
 nuke (th -^ ga) nz (d -, x) with nuke th nz d
 ... | (! th0) , (! th1) , nz' , ph , nd , (u , p) , d' , noz
     = (! th0 -^ ga) , (! th1 -, ga) , nz' , ph , nd , (u -^, ga , p -^, ga)
     , d' -, (th1 <? x) , noz -, (th0 <? x)

 postulate
   a b c d e : Bwd B
   ab1 ab2 : a <= b
   bc : b <= c
   de : d <= e
   be : b <= e
   c0 : c <= []
 
 myDag : Dag ([] -, a -, b -, c -, d -, e)
 myDag = [] -,
   [] -,
   ([] -, ([] -, ab1 -, ab2)) -,
   ([] -, [] -, ([] -, bc)) -,
   ([] -, [] -, [] -, []) -,
   ([] -, [] -, ([] -, be) -, [] -, ([] -, de))

 test = nuke (noth -, c -^ d -^ e) ([] -, c0) myDag
