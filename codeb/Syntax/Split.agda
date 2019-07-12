------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Split                                                   -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Split where

open import Lib.One
open import Lib.Equality
open import Lib.Pi
open import Lib.Sigma
open import Lib.Sum
open import Lib.Index
open import Lib.Bwd
open import Thin.Data
open import Thin.Select
open import Thin.Triangle
open import Thin.Cover
open import Thin.Thinned
open import Thin.Square
open import Thin.Pullback
open import Thin.Partition
open import Relevant.Pair
open import Relevant.Abstraction
open import Syntax.Desc
open import Syntax.Tm
open import Syntax.Action
open import Syntax.Substitution
open import Syntax.Thinning

module _
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}
 open DESC B S b2s
 module SPLIT
  (Cn : S -> Set) -- what constructors exist for each sort
  (Ds : {s : S} -> Cn s -> Desc)
  (M : S * Scope -> Set)
  where
  open TM B S b2s Cn Ds M
  open ACTION B S b2s Cn Ds M
  open SUBSTITUTION B S b2s Cn Ds M
  open THINNING B S b2s Cn Ds M


------------------------------------------------------------------------------
-- a more sophisticated notion of action on free variables
------------------------------------------------------------------------------

  record _=u>_ (ga de : Scope) : Set where
    constructor split
    field
      {passive active} : Scope
      {passiveTh}  : passive <= ga
      {activeTh}   : active  <= ga
      paPart       : Part passiveTh activeTh
      passiveHit   : passive <= de
      activeHit    : Sb active de

{-
This action splits its source scope into
  the passive part, which gets thinned
  the active part, which gets substituted.

As we push one of these things through a term,
  going under a binder extends the passive part
  going left or right in a pair makes a selection from both parts.

When the active part becomes empty, we can stop traversing the term and just
deploy the thinning for the passive part.
-}

  module _ where
   open Action
   
   action=u> : Action _=u>_
   hit action=u> i (split (u , _) th sg) with cover1 i u
   ... | inl (j , _) = var ^ j -<- th
   ... | inr (j , _) with j <? sg ; ... | _ -, t = t
   wkn action=u> (split (u , p) th sg) b =
     split (u -,^ b , p -,^ b) (th -, b) (env (_:^ b) sg)
   hitWkn0 action=u> {ga} (split (u , _) th sg) b
     rewrite noth! (noth -<- th) noth = r~
   hitWkn+ action=u> i (split (u , p) th sg) b with cover1 i u
   ... | inl (j , _) = r~
   ... | inr (j , _)
     with j <? sg | j <? env (_:^ b) sg | nat<? (_:^ b) j sg
   ... | _ -, t | _ -, t' | r~ = r~

{-
Note how the wkn method grows the passive part of the partition and extends
the thinning.
-}

  module _ where
   open Action
   open SBG action=u>
   open THINACTION action~ ; open THSBG action~
   private module X = SBGFUN Thinned action=u>
   private module Y = SBGFUN action=u> action=u>


------------------------------------------------------------------------------
-- restricting an action to a subscope
------------------------------------------------------------------------------

{-
To go left/right in a pair, we need to restricted the action to a subscope,
but show that the restricted action acts just the same on that subscope.
-}

   splitLemma : forall D {ga' ga de}(t : Tm D ga')(th : ga' <= ga)
     (a : ga =u> de) -> ga' =u> de >< \ a' -> Y.Hit idth a' (th -<- idth) a

-- Proceed copattern style, in order to keep left-programming after emitting
-- the first component of the action. We do not want the computational part
-- of the output to be strict in data used only for the proof. Agda's issues
-- re copattern matching after "with" means we do the same with twice.

-- For the restricted action, <Part hands us a restricted partition with the
-- embeddings we need, active and passive.

   fst (splitLemma D t th (split up ph sg)) with th <Part up
   ... | (ph0 ^ _) , _ , (ph1 ^ _) , _ , up'
     = split up' (ph0 -<- ph) (ph1 <? sg)

-- Now, to show they behave the same, we first have to get rid of some idth
-- compositions, and then we can abstract the result of looking up a var in
-- both actions: by cover1Lemma, these match up.

   snd (splitLemma D t th (split up ph sg)) i with th <Part up
   ... | (ph0 ^ _) , (s0 , _) , (ph1 ^ _) , (s1 , _) , up'
     with i -<- idth | i <id | th -<- idth | th <id ; ... | _ | r~ | _ | r~
     with cover1 i (fst up') | cover1 (i -<- th) (fst up)
        | cover1Lemma up s0 s1 up' i

-- In the passive case, we appeal to associativity of composition.

   ... | inl (j , _) | inl (k , _) | inl h = (var ^_) $~ (
     (j -<- (ph0 -<- ph)) ~[ assoc< j ph0 ph >
     (j -<- ph0 -<- ph)   ~[ (_-<- ph) $~ eq& h >
     (k -<- ph)            [QED])

-- In the active case, we appeal to functoriality of selection.

   ... | _ | _ | inr h rewrite h &<? sg = r~


------------------------------------------------------------------------------
-- implementing substitution
------------------------------------------------------------------------------

{-
We work with an action for exactly the support of our term. As ever, we must
ensure that the relational specification of substitution is satisfied.
-}

   splSb : forall D {ga de}(t : Tm D ga)(sg : ga =u> de) ->
     < SbG D (t ^ idth) sg >

{-
We immediately split on the active subscope. If that's empty, we're going
home early.
-}

   splSb D {ga} t a@(split {active = []} (u , p) ph sg) with allLeft u
   ... | r~ , r~
   
     = t ^ ph  -- just glue the thinning to the term, already!

     -- To show this is correct, we just need to show that an action whose
     -- active subscope is empty always behaves just like a thinning.
     -- We already have a proof that thinnings leave the term unchanged.
     
     , X.sbGMap (\ i ->
         (var ^ i -<- idth -<- ph)   ~[  (var ^_) $~ ((_-<- ph) $~ (i <id)) >
         (var ^ i -<- ph)             < help i ]~
         hit action=u> i a            < hit action=u> $~ i <id ~$~ rf a ]~
         hit action=u> (i -<- idth) a [QED])
       (thSbG {D} (idSbG (t ^ idth)) ph
        :[ SBG.SbG _ _ _ _ $~ ((t ^_) $~ id< ph) >)
     where
       help : forall {b}(i : b <- ga) -> hit action=u> i a ~ var ^ i -<- ph
       help i with cover1 i u
       ... | inr ((), _)
       ... | inl (j , v) with v ~&~ j &id ; ... | r~ , r~ = r~

{-
In the cases where there is active substitution happening, we must look at
the term.
-}

   -- If it is a variable, it must be the only variable, and active, to boot.

   splSb (` _) var (split {active = _ -, _} ([] -^, _ , _) ph ([] -, t)) =
     ! vaSb idth r~
   splSb (` _) var (split {active = _ -, _} (_-,^_ {ph = ()} u b , p) ph sg)
   splSb (` _) var (split {active = _ -, _} (u -, _ , ()) ph sg)

   -- The active subscope empties before we ever reach a null leaf.

   splSb un' null (split {active = _ -, _} {activeTh = ()} up ph sg)

   -- For pairs, restrict the action left and right, act recursively, then
   -- pair up the outputs. To satisfy the specification, we need to shift the
   -- induction hypotheses from being about restricted actions to being about
   -- the original action on restricted scopes. We have the lemma we need.

   splSb (D *' E) (d </ u \> e) a@(split {active = _ -, _} up ph sg) =
     let ad , dq = splitLemma D d (u/ u) a ; ae , eq = splitLemma E e (u\ u) a
         d' , ds = splSb D d ad ; e' , es = splSb E e ae
     in  (d' /,\ e') , prSb covPr (Y.sbGMap dq ds) (Y.sbGMap eq es) prPr

   -- The other cases are structural, and we can let the specification drive.

   splSb (b >' D) (ll d) a = ! \\Sb (splSb _ _ _ .snd)
   splSb (b >' D) (kk d) a = ! kkSb (splSb _ _ _ .snd)
   splSb (` s) (c $ t)   a = ! cnSb c (splSb _ _ _ .snd)
   splSb (` s) (m % t)   a = ! meSb m (splSb _ _ _ .snd)


------------------------------------------------------------------------------
-- entry point
------------------------------------------------------------------------------

   splSbG : forall D {ga de}(t : Tm D :< ga)(a : ga =u> de) -> < SbG D t a >
   splSbG D (t ^ th) a with splitLemma D t th a
   ... | a' , q with splSb D t a'
   ... | t' , h = t' , Y.sbGMap help h where
     help : Y.Hit idth a' th a
     help i with q i
     ... | h rewrite i <id | th <id = h
