module Thin.Diagram where

open import Lib.Equality
open import Lib.One
open import Lib.Pi
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

iq? : forall {X}{x y : X}{xs}(i : x <- xs)(j : y <- xs) ->
  Maybe (x ~ y >< \ { r~ -> i ~ j })
iq? i j with i \^/ j
... | _ , _ , ([] -, b) = yes (r~ , r~)
... | _ , _ , _ = no

module DIAGRAM {B : Set} where

 data Dag : Bwd (Bwd B) -> Set where
   [] : Dag []
   _-,_ : forall {gaz de} ->
     Dag gaz -> Env (\ ga -> Bwd (ga <= de)) gaz -> Dag (gaz -, de)

 growDCut : forall {ga ze : Bwd B}{gaz nuz} ->
          Env (\ de -> Bwd (de <= ga)) gaz ->
          ga <= ze ->
          Env (_<= ze) nuz ->
          nuz <= gaz ->
          <(nuz <=_) :* (_<= gaz)> >< /\ \ nuz' _ -> Env (_<= ze) nuz'
 growDCut x ps nz [] = [] ^ [] , []
 growDCut (x -, _) ps (nz -, n) (th -, b) with growDCut x ps nz th
 ... | nu ^ ph , nz' = nu -, b ^ ph -, b , nz' -, n
 growDCut (x -, []) ps nz (th -^ b) with growDCut x ps nz th
 ... | nu ^ ph , nz' = nu ^ ph -^ b , nz'
 growDCut (x -, (mz -, m)) ps nz (th -^ b) with growDCut x ps nz th
 ... | nu ^ ph , nz' = nu -^ b ^ ph -, b , nz' -, (m -<- ps)

 downCut : forall {nuz gaz} de -> Env (_<= de) nuz -> nuz <= gaz -> Dag gaz ->
   Sub gaz >< /\ \ nuz' th0 -> Sub gaz >< /\ \ gaz' th1 -> Part th0 th1 *
   nuz <= nuz' * Env (_<= de) nuz' * 
   Dag nuz' * 
   Env (\ ga -> Env (\ nu -> Bwd (nu <= ga)) nuz') gaz' *
   Dag gaz'
 downCut de nz (th -^ ga) (d -, x) with downCut de nz th d
 ... | ! ! (u        , p)        , ph , nz' , nd , noz , d'
     = ! ! (u -^, ga , p -^, ga) , ph
     , nz' , nd , noz -, (u/ u <? x) , d' -, (u\ u <? x)
 downCut de (nz -, ps) (th -, ga) (d -, x) with growDCut x ps nz th
 ... | ph ^ th' , nz' with downCut de nz' th' d
 ... | ! ! (u        , p)        , ph'              , nz''   ,  nd , noz , d'
     = ! ! (u -,^ ga , p -,^ ga) , ph -<- ph' -, ga
     , nz'' -, ps , nd -, (u/ u <? x) , env (_-, []) noz , d'
 downCut de [] [] [] = ! ! ([] , []) , [] , [] , [] , [] , []

 upCut : forall {nuz gaz} de             -- lower bound
   -> Env (de <=_) nuz -> nuz <= gaz     -- nuz is a subset of gaz above bound
   -> Dag gaz                            -- dag on the gaz
   ---------------------------------------------------------------------------
   -> Sub gaz >< /\ \ gaz' th0 -> Sub gaz >< /\ \ nuz' th1
   -> Part th0 th1 * nuz <= nuz'    -- partition of gaz, at least nuz on top
   *  Dag gaz'                      -- a dag on the bottom part
   *  Env (\ nu -> Env ((_<= nu) - Bwd) gaz') nuz'  -- the bot-to-top edges
   *  Dag nuz' * Env (de <=_) nuz'  -- a dag on the top part, all above bound

 upCut de nz (th -^ ga) (d -, x) with upCut de nz th d
 ... | ! ! (u , p) , mo , b , bt , t , t^
 -- we don't already know whether ga belongs on top, so collect its in-edges
 -- from the top-so-far
   with envBwd (purE (_-<-_ - bwd) $E t^ $E (u\ u <? x)) >B= snd
 ... | []          = ! ! (u -,^ ga , p -,^ ga) , mo    -- no edge, ga in bot
                   , b -, (u/ u <? x) , env (_-, []) bt , t , t^
 ... | _ -, ps     = ! ! (u -^, ga , p -^, ga) , mo -^ ga -- aha! ga to top!
                   , b , bt -, (u/ u <? x) , t -, (u\ u <? x) , t^ -, ps
 
 upCut de (nz -, ps) (th -, ga) (d -, x) with upCut de nz th d
 -- we already knew ga was going in the top when we started, so put it there
 ... | ! ! (u , p) , mo , b , bt , t , t^
                   = ! ! (u -^, ga , p -^, ga) , mo -, ga
                   , b , bt -, (u/ u <? x) , t -, (u\ u <? x) , t^ -, ps

 -- nothing will come of nothing
 upCut de [] [] [] = ! ! ([] , []) , [] , [] , [] , [] , [] 


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

 test0 = downCut [] ([] -, c0) (noth -, c -^ d -^ e) myDag
 test1 = downCut c ([] -, idth) (noth -, c -^ d -^ e) myDag
 test2 = upCut b ([] -, idth) (noth -, b -^ c -^ d -^ e) myDag
 
