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
open import Thin.IYJRN
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
 module _
  (Cn : S -> Set) -- what constructors exist for each sort
  (Ds : {s : S} -> Cn s -> Desc)
  (M : S * Scope -> Set)
  where
  open TM B S b2s Cn Ds M
  open ACTION B S b2s Cn Ds M
  open SUBSTITUTION B S b2s Cn Ds M
  open THINNING B S b2s Cn Ds M

  record _=u>_ (ga de : Scope) : Set where
    constructor split
    field
      {passive active} : Scope
      {passiveTh}  : passive <= ga
      {activeTh}   : active  <= ga
      paCover      : passiveTh /u\ activeTh
      paPart       : Pullback (no& passiveTh ^ no& activeTh)
      passiveHit   : passive <= de
      activeHit    : Sb active de

  module _ where
   open Action
   
   action=u> : Action _=u>_
   hit action=u> i (split u _ th sg) with cover1 i u
   ... | inl (j , _) = var ^ j -<- th
   ... | inr (j , _) with j <? sg ; ... | _ -, t = t
   wkn action=u> (split u p th sg) b =
     split (u -,^ b) (p -,^ b) (th -, b) (env (_:^ b) sg)
   hitWkn0 action=u> {ga} (split u _ th sg) b
     rewrite noth! (noth -<- th) noth = r~
   hitWkn+ action=u> i (split u p th sg) b with cover1 i u
   ... | inl (j , _) = r~
   ... | inr (j , _)
     with j <? sg | j <? env (_:^ b) sg | nat<? (_:^ b) j sg
   ... | _ -, t | _ -, t' | r~ = r~

  module _ where
   open Action action=u>

   selSplit : forall {ga de ze}(ps : ga <= de)(sg : de =u> ze) ->
     ga =u> ze >< \ rh ->
     forall {b}(i : b <- ga) -> hit i rh ~ hit (i -<- ps) sg
   fst (selSplit ps (split u p th sg)) with ps <u u
   ... | (th0 ^ ph0) , (th1 ^ ph1) , (s0 , p0) , (s1 , p1) , u'
       = split u' (pb s0 s1 p) (th0 -<- th) (th1 <? sg)
     where
     pb : forall {ga0 ga ga1 de0 de de1}
       {ps0 : de0 <= de}{ps1 : de1 <= de}
       {th0 : ga0 <= de0}{th : ga <= de}{th1 : ga1 <= de1}
       {ph0 : ga0 <= ga}{ph1 : ga1 <= ga} ->
       Square (th0 ^ ps0) (ph0 ^ th) -> Square (th1 ^ ps1) (ph1 ^ th) ->
       Pullback (no& ps0 ^ no& ps1) -> Pullback (no& ph0 ^ no& ph1)
     pb {th0 = th0}{th}{th1}{ph0}{ph1} s0 s1 p with ph0 \^/ ph1
     ... | ch0 ^ ch1 , (ch , v2 , v3) , p'
       with ch0 -&- th0 | ch1 -&- th1 | ch -&- th
     ... | ! v4 | ! v5 | ! w
       with coSq v4 w (id& ch ^ v2) (opSq s0)
          | coSq v5 w (id& ch ^ v3) (opSq s1)
     ... | w0 ^ w2 | w1 ^ w3 with w0 ~&~ w1
     ... | r~ , r~ with pullU (w2 ^ w3) p
     ... | [] , w4 , w5 , w6
       with noth! ch0 noth | noth! ch noth | noth! ch1 noth
     ... | r~ | r~ | r~ with v2 ~&~ no& ph0 | v3 ~&~ no& ph1
     ... | r~ , r~ | r~ , r~ = p'
   snd (selSplit ps (split u p th sg)) i with ps <u u
   ... | (th0 ^ ph0) , (th1 ^ ph1) , (v0 ^ v1 , p0) , (v2 ^ v3 , p1) , u'
     with cover1 i u' | cover1 (i -<- ps) u
   snd (selSplit ps (split u p th sg)) i
     | (th0 ^ ph0) , (th1 ^ ph1) , (v0 ^ v1 , p0) , (v2 ^ v3 , p1) , u'
     | inl (j , w0) | inl (k , w1)
       with th0 -&- th | i -&- ps | k -&- th | assoc03 (w0 ^ v1)
   ... | th' , w2 | ! w3 | ! w4 | w5 ^ w6 with j -&- th' | w3 ~&~ w6 
   ... | ! w7 | r~ , r~ with assoc02 (w7 ^ w2)
   ... | w8 ^ w9 with assoc03 (w8 ^ v0)
   ... | wA ^ wB with wA ~&~ w5
   ... | r~ , r~ with wB ~1&1~ w1
   ... | r~ with w4 ~&~ w9
   ... | r~ , r~ = r~
   snd (selSplit ps (split u p th sg)) i
     | (th0 ^ ph0) , (th1 ^ ph1) , (v0 ^ v1 , p0) , (v2 ^ v3 , p1) , u'
     | inr (j , w0) | inr (k , w1) with i -&- ps | assoc03 (w0 ^ v3)
   ... | ! w2 | w3 ^ w4 with w2 ~&~ w4 | assoc02 (w3 ^ v2)
   ... | r~ , r~ | w5 ^ w6 with w6 ~1&1~ w1
   ... | r~ rewrite w5 &<? sg = r~
   snd (selSplit ps (split u p th sg)) i
     | (th0 ^ ph0) , (th1 ^ ph1) , (v0 ^ v1 , p0) , (v2 ^ v3 , p1) , u'
     | inl (j , w0) | inr (k , w1) with i -&- ps | assoc03 (w0 ^ v1)
   ... | ! w2 | w3 ^ w4 with w2 ~&~ w4 | assoc02 (w3 ^ v0)
   ... | r~ , r~ | w5 ^ w6 with pullU (w6 ^ w1) p ; ... | () , _
   snd (selSplit ps (split u p th sg)) i
     | (th0 ^ ph0) , (th1 ^ ph1) , (v0 ^ v1 , p0) , (v2 ^ v3 , p1) , u'
     | inr (j , w0) | inl (k , w1) with i -&- ps | assoc03 (w0 ^ v3)
   ... | ! w2 | w3 ^ w4 with w2 ~&~ w4 | assoc02 (w3 ^ v2)
   ... | r~ , r~ | w5 ^ w6 with pullU (w1 ^ w6) p ; ... | () , _

   module _ where
    open Action
    open SBG action=u>
    open THINACTION action~ ; open THSBG action~
    private module X = SBGFUN Thinned action=u>
    private module Y = SBGFUN action=u> action=u>

    splSb : forall D {ga de}(t : Tm D ga)(sg : ga =u> de) ->
            < SbG D (t ^ idth) sg >
    splSb D {ga} t a@(split {active = []} u p th sg) with allLeft u
    ... | r~ , r~  = t ^ th
      , X.sbGMap (\ i ->
          (var ^ i -<- idth -<- th)   ~[  (var ^_) $~ ((_-<- th) $~ (i <id)) >
          (var ^ i -<- th)             < help i ]~
          hit action=u> i a            < hit action=u> $~ i <id ~$~ rf a ]~
          hit action=u> (i -<- idth) a [QED])
        (thSbG {D} (idSbG (t ^ idth)) th
         :[ SBG.SbG _ _ _ _ $~ ((t ^_) $~ id< th) >)
      where
        help : forall {b}(i : b <- ga) -> hit action=u> i a ~ var ^ i -<- th
        help i with cover1 i u
        ... | inr ((), _)
        ... | inl (j , v) with v ~&~ j &id ; ... | r~ , r~ = r~

    splSb un' null (split {active = _ -, _} {activeTh = ()} u p ph sg)
    splSb (D *' E) (d </ u' \> e) a@(split {active = _ -, _} u p ph sg)
      with selSplit (u/ u') a | selSplit (u\ u') a
    ... | a/ , q/ | a\ , q\ with splSb D d a/ | splSb E e a\
    ... | d' , ds | e' , es = (d' /,\ e') ,
      prSb covPr
        (Y.sbGMap (\ i ->
          hit action=u> (i -<- idth) a/ ~[ hit action=u> $~ i <id ~$~ rf a/ >
          hit action=u> i a/            ~[ q/ i >
          hit action=u> (i -<- u/ u') a
            < hit action=u> $~ ((i -<-_) $~ (u/ u' <id)) ~$~ rf a ]~
          hit action=u> (i -<- (u/ u' -<- idth)) a [QED]) ds)
        (Y.sbGMap (\ i ->
          hit action=u> (i -<- idth) a\ ~[ hit action=u> $~ i <id ~$~ rf a\ >
          hit action=u> i a\            ~[ q\ i >
          hit action=u> (i -<- u\ u') a
            < hit action=u> $~ ((i -<-_) $~ (u\ u' <id)) ~$~ rf a ]~
          hit action=u> (i -<- (u\ u' -<- idth)) a [QED]) es)
        (prPr {s = d'}{t = e'})
    splSb (b >' D) (ll d) a@(split {active = _ -, _} u p ph sg) =
      ! \\Sb (splSb _ _ _ .snd)
    splSb (b >' D) (kk d) a@(split {active = _ -, _} u p ph sg) =
      ! kkSb (splSb _ _ _ .snd)
    splSb (` _) var (split {active = _ -, _} ([] -^, _) p ph ([] -, t)) =
      ! vaSb idth r~
    splSb (` _) var (split {active = _ -, _} (_-,^_ {ph = ()} u b) p ph sg)
    splSb (` _) var (split {active = _ -, _} (u -, _) () ph sg)
    splSb (` s) (c $ t)   a@(split {active = _ -, _} u p ph sg) =
      ! cnSb c (splSb _ _ _ .snd)
    splSb (` s) (m % t)   a@(split {active = _ -, _} u p ph sg) =
      ! meSb m (splSb _ _ _ .snd)
