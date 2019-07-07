------------------------------------------------------------------------------
-----                                                                    -----
-----     Syntax.Substitution                                            -----
-----                                                                    -----
------------------------------------------------------------------------------

module Syntax.Substitution where

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
open import Relevant.Pair
open import Relevant.Abstraction
open import Syntax.Desc
open import Syntax.Tm
open import Syntax.Action

module _
  (B : Set) -- what binders are like
  (S : Set) -- what sorts exist
  (b2s : B -> S)  -- what sort of thing each binder binds
 where
 open THIN {B}
 open DESC B S b2s
 module SUBSTITUTION
  (Cn : S -> Set) -- what constructors exist for each sort
  (Ds : {s : S} -> Cn s -> Desc)
  (M : S * Scope -> Set)
  where
  open TM B S b2s Cn Ds M
  open ACTION B S b2s Cn Ds M


------------------------------------------------------------------------------
-- A Relational Specification of Substitution
------------------------------------------------------------------------------

{-
Before implementing substitution, let us *specify* it as a three place
relation, defined inductively. SbG is the *graph* of substitution.
-}

  module SBG {_=>_}(A : Action _=>_) where  -- fix an action

   open Action A

   data SbG {ga de} : forall D -> Tm D :< ga -> ga => de -> Tm D :< de -> Set
     where                     -- input         action      output

     vaSb : forall {b}(i : b <- ga){sg t} -> hit i sg ~ t ->
  
          ----------------------------
            SbG (` _) (var ^ i) sg t

     cnSb : forall {s}(c : Cn s){t sg t'} ->

            SbG (Ds c) t sg t' ->
          ---------------------------------------------
            SbG (` s) ((c $_) :$ t) sg ((c $_) :$ t')

     meSb : forall {s xi}(m : M (s , xi)){t sg t'} ->

            SbG (sp xi) t sg t' ->
          ---------------------------------------------
            SbG (` s) ((m %_) :$ t) sg ((m %_) :$ t')

     unSb : forall {sg} ->

          ------------------------------------------
            SbG un' (null ^ noth) sg (null ^ noth)

     prSb : forall {D E de d e sg d' e' de'} ->

            Pr d e de -> SbG D d sg d' -> SbG E e sg e' -> Pr d' e' de' ->
          ------------------------------------------------------------------
            SbG (D *' E) de sg de' 

     kkSb : forall {b D t sg t'} ->

            SbG D t sg t' ->
          ----------------------------------------
            SbG (b >' D) (kk :$ t) sg (kk :$ t')

     llSb : forall {b D sg ga' t de' t'}{th : ga' <= ga}{ph : de' <= de} ->
       
            SbG D (t ^ th -, b) (wkn sg b) (t' ^ ph -, b) ->
          ----------------------------------------------------
            SbG (b >' D) (ll t ^ th) sg (ll t' ^ ph)

{-
This relation has been carefully designed to offer strong reasoning power.
I have eliminated almost all the "green slime", leaving only some noth
operations in the unSb case. The :$ operation does not count as green slime
as it cannot get stuck: I use it to avoid ugly eta-expansion.

Things to note.

 1. Variables are mapped exactly as determined by hit.
 2. Pairing and unpairing are specified relationally, rather than by smart
      constructor, so we are not particular about the provenance of coproduct
      diagrams, just their existence.
 3. We insist that relevant lambda will map to relevant lambda, because we
      know that the bound source variable does occur and will be mapped to
      the bound target variable.
-}


------------------------------------------------------------------------------
-- The Relevance Lemma
------------------------------------------------------------------------------

{-
If we have an action                         sg : ga => de
and we select the support of a source term   th : ga0 <= ga
then we can express a useful property of the support of its image in the
target, as given by some                     ph : de0 <= de.

Every variable in the source support occurs in the souce term, and will be
hit by the action. Correspondingly, the supports of their images must be
included in the support of the term we end up with.
-}

   module _ {ga0 ga de0 de}(th : ga0 <= ga)(sg : ga => de)(ph : de0 <= de)
    where
    Relv : Set
    Relv = forall {b}(i : b <- ga0) -> <(_& ph =< thin (hit (i -<- th) sg))>
      -- the target support factors through the support of the image of
      -- every variable in the source support

{-
Let us prove that every substitution permitted by the specification has
this property.
-}

   sbRelv : forall {D ga0 ga de0 de}
    {s : Tm D ga0}{th : ga0 <= ga}{sg}{t : Tm D de0}{ph : de0 <= de} ->
    SbG D (s ^ th) sg (t ^ ph) -> Relv th sg ph
   sbRelv (vaSb i r~) ([] -, b) rewrite id< i = ! id& _
   sbRelv (vaSb i r~) (() -^ b)
   sbRelv (cnSb c xs) j = sbRelv xs j
   sbRelv (meSb m xs) j = sbRelv xs j
   sbRelv unSb ()
   sbRelv (prSb (mkPr vd u ve) xd xe p') j with cover1 j u
   sbRelv {th = th} (prSb {d = _ ^ ph} (mkPr vd u ve) xd xe (mkPr wd _ _)) j
     | inl (i , v) with i -&- ph | j -&- th | assoc03 (v ^ vd) | sbRelv xd i
   ... | ! vi | ! vj | wi ^ wj | ! w with vi ~&~ wi | vj ~&~ wj
   ... | r~ , r~ | r~ , r~ = ! assoc02 (w ^ wd) .snd .snd
   sbRelv {th = th} (prSb {e = _ ^ ph} (mkPr vd u ve) xd xe (mkPr _ _ we)) j
     | inr (i , v) with i -&- ph | j -&- th | assoc03 (v ^ ve) | sbRelv xe i
   ... | ! vi | ! vj | wi ^ wj | ! w with vi ~&~ wi | vj ~&~ wj
   ... | r~ , r~ | r~ , r~ = ! assoc02 (w ^ we) .snd .snd
   sbRelv (kkSb xs) j = sbRelv xs j
   sbRelv {b >' D} {th = th}{sg} (llSb xs) j
     with hit (j -<- th) sg | hit (j -<- th -^ b) (wkn sg b)
        | hitWkn+ (j -<- th) sg b
        | sbRelv xs (j -^ _)
   ... | t | t' | r~ | ! v -^, .b = ! v

{-
When we hit a variable, we have exactly the fact we need: there is one
variable in scope, it is mapped to its image, so the support of the image is
the support of the output.

For pairing, we need to find out which way the given variable was sent, in
order to choose which induction hypothesis will solve the problem. After that,
it's just diagram chasing.

When we go under a binder, we know we can use hitWkn+ to get us in shape for
the induction hypothesis.
-}


------------------------------------------------------------------------------
-- Admissibility of Abstraction
------------------------------------------------------------------------------

{-
There is a looser rule for lambda which is more convenient, operationally.
To act on a lambda, go under the binder, weakening the action, then
reabstract the result. This rule does not insist that the reabstraction will
yield a lambda, so it's easier to use as an introduction form. We do not
want it as a constructor of the relation, because it gives correspondingly
less helpful elimination behaviour.

The right move is to keep the tighter constructor and show the looser rule
admissible.
-}

   \\Sb : forall {b D ga de}{sg : ga => de}{ga' t t'}{th : ga' <= ga} ->
       
             SbG D (t ^ th -, b) (wkn sg b) t' ->
           -----------------------------------------
             SbG (b >' D) (ll t ^ th) sg (b \\ t')
              
   \\Sb {b} {sg = sg}{th = th} s
     with noth -<- th | noth! (noth -<- th) noth | sbRelv s (noth -, b)
   ... | _ | r~ | ! v  with hit (noth -, b) (wkn sg b) | hitWkn0 sg b
   \\Sb s | _ | r~ | ! (v -, _) | _ | r~ = llSb s

{-
The proof exactly makes use of the Relevance Lemma to show that the
boudn variable's image (itself) is in the support of the output, which forces
b \\ t' to choose the ll constructor, allowing us to deploy the tighter
introduction rule.
-}


------------------------------------------------------------------------------
-- An Implementation of Substitution
------------------------------------------------------------------------------

{-
Having specified substitution by some action, let us make it go! The polite
thing to do is to prove < SbG D t sg >, leaving the actual program to Agda's
imagination.

Annoyingly, we must uncurry the input in Tm D :< ga to keep the termination
checker happy.
-}

   mkSbG : forall D {ga de}(t : Tm D :< ga)(sg : ga => de) -> < SbG D t sg >
   mkSbG D (t ^ th) = go D t th where
     go : forall D {ga' ga de}(t : Tm D ga')(th : ga' <= ga)(sg : ga => de)
       -> < SbG D (t ^ th) sg >
     go un'      null th sg rewrite noth! th noth = ! unSb
     go (D *' E) (d </ u \> e) th sg =
       ! prSb covPr (go D d (u/ u -<- th) sg .snd)
                    (go E e (u\ u -<- th) sg .snd) prPr
     go (b >' D) (ll t)  th sg = ! \\Sb (go D t (th -, b) (wkn sg b) .snd)
     go (b >' D) (kk t)  th sg = ! kkSb (go D t th sg .snd)
     go (` s)    var     i  sg = ! vaSb i r~
     go (` s)    (c $ t) th sg = ! cnSb c (go _ t th sg .snd)
     go (` s)    (m % t) th sg = ! meSb m (go _ t th sg .snd)

{-
Note that our admissible \\Sb makes the ll case easy.
-}

{-
This really isn't a super clever implementation of substitution.
Premature optimisation considered harmful.
-}


------------------------------------------------------------------------------
-- When does the same thing happen?
------------------------------------------------------------------------------

  module SBGFUN {_=X>_}{_=Y>_}(X : Action _=X>_)(Y : Action _=Y>_) where
   private module X = SBG X ; module Y = SBG Y
   open Action ; open SBG

{-
Let us have two kinds of action. When do they do the same thing to a given
input term?

When they give the same image for just the things in the input support,
regardless of what they do to the variables which do not occur.

The following is the property which matters.
-}

   Hit : forall {ga ga0 ga1 de}
     (th0 : ga <= ga0)(sg0 : ga0 =X> de)(th1 : ga <= ga1)(sg1 : ga1 =Y> de)
     -> Set
   Hit th0 sg0 th1 sg1 = forall {b}(i : b <- _) ->
       X .hit (i -<- th0) sg0 ~ Y .hit (i -<- th1) sg1

{-
Note that sg0 and sg1 do not need to have the same source *scope*. Any source
in which the source support embeds will do just fine, and that freedom will
come very much in handy.
-}

{-
Being mindful of how substitution works, we should check that the things we
do to actions in the course of duty preserve the Hit property.

Firstly, Hit is preserved by weakening.
-}

   wknHit : forall {ga ga0 ga1 de}
     {th0 : ga <= ga0}{sg0 : ga0 =X> de}{th1 : ga <= ga1}{sg1 : ga1 =Y> de}
     -> Hit th0 sg0 th1 sg1 ->
     forall {b} -> Hit (th0 -, b) (X .wkn sg0 b) (th1 -, b) (Y .wkn sg1 b)
   wknHit {th0 = th0}{sg0}{th1}{sg1} q (i -, b)
     rewrite noth! (i -<- th0) noth | noth! (i -<- th1) noth
           | X .hitWkn0 sg0 b | Y .hitWkn0 sg1 b              = r~
   wknHit {th0 = th0}{sg0}{th1}{sg1} q (i -^ b)
     rewrite X .hitWkn+ (i -<- th0) sg0 b | Y .hitWkn+ (i -<- th1) sg1 b
           | q i = r~

{- Secondly, Hit is preserved by selection. -}

   selHit : forall {ga' ga ga0 ga1 de}
     {ph0 : ga' <= ga0}{th0 : ga <= ga0}{sg0 : ga0 =X> de}
     {ph1 : ga' <= ga1}{th1 : ga <= ga1}{sg1 : ga1 =Y> de}
     {ps : ga' <= ga} -> ps & th0 =< ph0 -> ps & th1 =< ph1 ->
     Hit th0 sg0 th1 sg1 -> Hit ph0 sg0 ph1 sg1
   selHit {ph0 = ph0}{th0}{_}{ph1}{th1}{_}{ps} v0 v1 q i with i -&- ps
   ... | j , v with i -&- ph0 | i -&- ph1 | j -&- th0 | j -&- th1 | q j
   ... | ! w0 | ! w1 | ! w2 | ! w3 | q'
     with assoc02 (w0 ^ v0) | assoc02 (w1 ^ v1)
   ... | w4 ^ w5 | w6 ^ w7 with w4 ~&~ w6 | v ~&~ w6 
   ... | r~ , r~ | r~ , r~ with w2 ~&~ w5 | w3 ~&~ w7
   ... | r~ , r~ | r~ , r~ = q'

{-
Now let us prove that two actions which hit the support of the input in the
same way will agree on their output.
-}

   sbGQ : forall {D ga ga0 ga1 de}
     {th0 : ga <= ga0}{sg0 : ga0 =X> de}{th1 : ga <= ga1}{sg1 : ga1 =Y> de}
     -> Hit th0 sg0 th1 sg1
     -> forall {t : Tm D ga}{t0 t1 : Tm D :< de} ->
     X.SbG D (t ^ th0) sg0 t0 -> Y.SbG D (t ^ th1) sg1 t1 -> t0 ~ t1
   sbGQ q (vaSb i r~) (vaSb j r~) with q ([] -, _)
   ... | q' rewrite id< i | id< j = q'
   sbGQ q (cnSb c xs) (cnSb .c ys) with sbGQ q xs ys ; ... | r~ = r~
   sbGQ q (meSb m xs) (meSb .m ys) with sbGQ q xs ys ; ... | r~ = r~
   sbGQ q unSb unSb = r~
   sbGQ q (prSb px0@(mkPr vd u0 ve) xd xe px1)
          (prSb py0@(mkPr wd u1 we) yd ye py1)
     with sbGQ (selHit vd wd q) xd yd | sbGQ (selHit ve we q) xe ye
   ... | r~ | r~ with px1 ~Pr~ py1 ; ... | r~ , r~ = r~
   sbGQ q (kkSb xs) (kkSb ys) with sbGQ q xs ys ; ... | r~ = r~
   sbGQ q (llSb xs) (llSb ys) with sbGQ (wknHit q) xs ys ; ... | r~ = r~


------------------------------------------------------------------------------
-- Identity action is identity
------------------------------------------------------------------------------

  module _ where

   open Action action~ ; open SBG action~

   idSbG : forall {D ga}(t : Tm D :< ga) -> SbG D t r~ t
   idSbG {D} (t ^ th) = go D t th where
     go : forall D {ga de}(t : Tm D ga)(th : ga <= de) ->
          SbG D (t ^ th) r~ (t ^ th)
     go un' null th rewrite noth! th noth = unSb
     go (D *' E) (d </ u \> e) th =
       prSb covPr (go D d (u/ u -<- th)) (go E e (u\ u -<- th)) covPr
     go (b >' D) (kk d) th = kkSb (go D d th)
     go (b >' D) (ll d) th = llSb (go D d (th -, b))
     go (` s) var     i  = vaSb i r~
     go (` s) (c $ t) th = cnSb c (go _ t th)
     go (` s) (m % t) th = meSb m (go _ t th)
