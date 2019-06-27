module SynU where

open import Basics
open import Bwd
open import Thin

infixr 8 _*'_
infixr 9 _>'_
infix 10 `_
data Syn (B S : Set) : Set where
  un'   : Syn B S
  _*'_  : (d e : Syn B S) -> Syn B S
  _>'_  : B -> Syn B S -> Syn B S
  `_    : S -> Syn B S

module _ {B S : Set} where

 infix 6 :S_ :D_
 data Sort : Set where
   :S_ : S -> Sort
   :D_ : Syn B S -> Sort

 Rlv : Syn B S -> (S -> Bwd B -> Set) -> (Bwd B -> Set)
 Rlv un'       Tm ga       = Null ga
 Rlv (D *' E)  Tm ga       = (Rlv D Tm ^*^ Rlv E Tm) ga 
 Rlv (b >' D)  Tm ga       = Scope (Rlv D Tm) b ga
 Rlv (` s)     Tm ga       = Tm s ga

 module TERM (Cn : S -> Set)(Ds : {s : S} -> Cn s -> Syn B S)(b2s : B -> S)
  where

  spine : Bwd B -> Syn B S
  spine [] = un'
  spine (ga -, b) = spine ga *' ` b2s b

  data TmR (M : S -> Bwd B -> Set)(s : S)(ga : Bwd B) : Set

  infix 4 _!_ _!^_
  _!_ _!^_ : (M : S -> Bwd B -> Set) -> Sort -> Bwd B -> Set
  (M !^ k)    = ((M ! k) :^_)
  (M ! :S s)  = TmR M s
  (M ! :D D)  = Rlv D (TmR M)

  infix 5 _-_ _%_
  data TmR M s ga where
    va  : {b : B}(z : Sole b ga)(q : b2s b == s)              -> (M ! :S s) ga
    _-_ : (c : Cn s)(td : (M ! :D Ds c) ga)                   -> (M ! :S s) ga
    _%_ : {xi : Bwd B}(m : M s xi)(rh : (M ! :D spine xi) ga) -> (M ! :S s) ga

  pattern # = va sole refl

  #0 : forall {M ga b} -> (M !^ :S b2s b) (ga -, b)
  #0 = # ^ noth -, _

  infix 4 _:/_
  _:/_ : (M : S -> Bwd B -> Set) -> Bwd B -> Bwd B -> Set
  (M :/ ga) de = Env (\ b -> (M !^ :S (b2s b)) de) ga

  module _ {M : S -> Bwd B -> Set} where

   module _ {ga de : Bwd B} (sg : (M :/ ga) de) where
    dom = ga ; cod = de
    module _ (b : B) where
     infixl 8 _-$^_ _-$,_
     _-$^_ : (M :/ ga) (de -, b)  ;  _-$,_ : (M :/ ga -, b) (de -, b)
     _-$^_ = env (_^^^ b) sg      ;  _-$,_ = _-$^_ -, #0

   infix 4 _/_ _/^_
   _/_  : forall k {ga de} -> (M ! k) ga  -> (M :/ ga) de -> (M !^ k) de
   _/^_ : forall k {ga de} -> (M !^ k) ga -> (M :/ ga) de -> (M !^ k) de
   (:S _ / #)          (_ -, t) = t
   (:S _ / c - td)           sg = (c -_) ^$ (:D Ds c / td) sg
   (:S _ / _%_ {xi} m rh)    sg = (m %_) ^$ (:D spine xi / rh) sg
   (:D un'    / null)        sg = null ^ noth
   (:D D *' E / d <^ c ^> e) sg = (:D D /^ d &^ c) sg ^,^ (:D E /^ c ^& e) sg
   (:D b >' D / ll d)        sg = sco ((:D D / d) (sg -$, b))
   (:D b >' D / kk d)        sg = kk ^$ (:D D / d) sg
   (:D ` s    / t)           sg = (:S s / t) sg
   (k /^ t ^ th)             sg = (k / t) (th <? sg)

   data Sb {ga de} : (k : Sort) ->
     (M !^ k) ga -> (M :/ ga) de -> (M !^ k) de -> Set
     where
     vaSb : forall {b}(i : ([] -, b) <= ga){sg t'} ->
            (i <? sg) == ([] -, t') ->
            Sb (:S _) (# ^ i) sg t'
     cnSb : forall {s}(c : Cn s){tr sg tr'} ->
            Sb (:D Ds c) tr sg tr' -> 
            Sb (:S _) ((c -_) ^$ tr) sg ((c -_) ^$ tr')
     meSb : forall {s xi}(m : M s xi){rh sg rh'} ->
            Sb (:D spine xi) rh sg rh' ->
            Sb (:S s) ((m %_) ^$ rh) sg ((m %_) ^$ rh')
     unSb : forall {sg} ->
            Sb (:D un') (null ^ noth) sg (null ^ noth)
     prSb : forall {D E sg d d' e e' de de'} ->         Pr d e de ->
            Sb (:D D) d sg d' -> Sb (:D E) e sg e' ->   Pr d' e' de' ->
            Sb (:D D *' E) de sg de'
     llSb : forall {b D sg ga0 de0 d d'}{th : ga0 <= ga}{ph : de0 <= de} ->
            Sb (:D D) (d ^ (th -, b)) (sg -$, b) (d' ^ (ph -, b)) ->
            Sb (:D b >' D) (ll d ^ th) sg (ll d' ^ ph)
     kkSb : forall {b D sg d d'} ->
            Sb (:D D) d sg d' ->
            Sb (:D b >' D) (kk ^$ d) sg (kk ^$ d')
     tmSb : forall {s t t' sg} ->
            Sb (:S s) t sg t' ->
            Sb (:D ` s) t sg t'

   funSb : forall {k ga de}{t : (M !^ k) ga}{sg}{t0 t1 : (M !^ k) de} ->
     Sb k t sg t0 -> Sb k t sg t1 -> t0 == t1
   funSb (vaSb i q0) (vaSb .i q1) with sym q0 =-= q1  ; ... | refl = refl
   funSb (cnSb c p0) (cnSb .c p1) with funSb p0 p1    ; ... | refl = refl
   funSb (meSb m p0) (meSb .m p1) with funSb p0 p1    ; ... | refl = refl
   funSb unSb unSb = refl
   funSb (prSb x0 d0 e0 y0) (prSb x1 d1 e1 y1) with prInj x0 x1
   ... | refl , refl with funSb d0 d1 | funSb e0 e1 ; ... | refl | refl =
     prFun y0 y1
   funSb (llSb p0) (llSb p1) with funSb p0 p1         ; ... | refl = refl
   funSb (kkSb p0) (kkSb p1) with funSb p0 p1         ; ... | refl = refl
   funSb (tmSb p0) (tmSb p1) with funSb p0 p1         ; ... | refl = refl

   module _ {ga0 ga de0 de}(th : ga0 <= ga)(sg : (M :/ ga) de)(ph : de0 <= de)
    where
    Relevant : Set
    Relevant = forall {b}(i : ([] -, b) <= ga0){t'} ->
      (i <? (th <? sg)) == ([] -, t') -> Sg _ \ ps -> Tri ps ph (thinning t')

   sbRelv : forall {k ga0 ga de0 de}
     {s : (M ! k) ga0}{th : ga0 <= ga}{sg}{t : (M ! k) de0}{ph : de0 <= de} ->
     Sb k (s ^ th) sg (t ^ ph) -> Relevant th sg ph
   sbRelv (vaSb j p) ([] -, b) q with ((([] -, b) <?_) $= sym p) =-= q
   ... | refl = _ , idTri _
   sbRelv (vaSb _ x) (() -^ _) q
   sbRelv (cnSb c p) i q = sbRelv p i q
   sbRelv (meSb m p) i q = sbRelv p i q
   sbRelv unSb () q
   sbRelv (prSb (mkPr lv c rv) d e (mkPr lu b ru)) i q with cover1 i c
   sbRelv {sg = sg} (prSb (mkPr lv c rv) d e (mkPr lu b ru)) i q | inl (j , v)
     with cossaTri v lv | sbRelv d j
   ... | _ , v0 , v1 | dh rewrite compSel v0 sg | compSel v1 sg =
     let _ , u = dh q ; _ , _ , v = assocTri' u lu in _ , v
   sbRelv {sg = sg} (prSb (mkPr lv c rv) d e (mkPr lu b ru)) i q | inr (j , v)
     with cossaTri v rv | sbRelv e j
   ... | _ , v0 , v1 | eh rewrite compSel v0 sg | compSel v1 sg =
     let _ , u = eh q ; _ , _ , v = assocTri' u ru in _ , v
   sbRelv {:D b >' D} {th = th}{sg} (llSb p) i {t} q with sbRelv p (i -^ b) (
       (i <? th <? (sg -$^ b))    =[ (i <?_) $= naturalSelection _ th sg >=
       (i <? ((th <? sg) -$^ b))  =[ naturalSelection _ i (th <? sg) >=
       ((i <? th <? sg) -$^ b)    =[ (_-$^ b) $= q >=
       ([] -, (t ^^^ b))          [QED])
   ... | _ , (v -^, .b) = _ , v
   sbRelv (kkSb p) i q = sbRelv p i q
   sbRelv (tmSb p) i q = sbRelv p i q

   sb : forall k {ga0 ga de}(t : (M ! k) ga0)(th : ga0 <= ga)
        (sg : (M :/ ga) de) -> Sb k (t ^ th) sg ((k /^ t ^ th) sg)
   sb (:S _) # i sg  with i <? sg | \ t -> vaSb i {sg} {t}
   ... | [] -, t | h = h _ refl
   sb (:S _) (c - td) th sg = cnSb c (sb (:D Ds c) td th sg)
   sb (:S _) (_%_ {xi} m rh) th sg = meSb m (sb (:D spine xi) rh th sg)
   sb (:D un') null th sg rewrite nothU th noth = unSb
   sb (:D D *' E) (d <^ c ^> e) th sg
     with lcov c -<- th | lcov c -v- th | rcov c -<- th | rcov c -v- th
   ... | ph | lv | ps | rv rewrite compSel lv sg | compSel rv sg =
     prSb (mkPr lv c rv) (sb (:D D) d ph sg) (sb (:D E) e ps sg) (prPr _ _)
   sb (:D b >' D) {de = de} (ll d) th sg with sb (:D D) d (th -, b) (sg -$, b)
   ... | h with sbRelv h (noth -, b) (_-,_ $= env0 =$= refl)
   ... | ph , v with th <? env (_^^^ b) sg | env (_^^^ b) (th <? sg)
                   | naturalSelection (_^^^ b) th sg
   ... | sg0 | _ | refl with (:D D / d) (sg0 -, #0)
   sb (:D b >' D) (ll d) th sg | h | _ , (v -, _) | _ | _ | refl | _ = llSb h
   sb (:D b >' D) (kk d) th sg = kkSb (sb (:D D) d th sg)
   sb (:D ` s) t th sg = tmSb (sb (:S s) t th sg)

   thsb : forall {ga de} -> ga <= de -> (M :/ ga) de
   thsb []        = []
   thsb (th -, b) = thsb th -$, b
   thsb (th -^ b) = thsb th -$^ b

   thsbTri : forall {ga de xi th ph ps} ->
     Tri {_}{ga}{de}{xi} th ph ps -> (th <? thsb ph) == thsb ps
   thsbTri [] = refl
   thsbTri (_-,_ {th = th} {ph} v b)
     rewrite naturalSelection (_^^^ b) th (thsb ph) | thsbTri v = refl
   thsbTri (_-^,_ {th = th} {ph} v b)
     rewrite naturalSelection (_^^^ b) th (thsb ph) | thsbTri v = refl
   thsbTri {th = th} (_-^_ {ph = ph} v b)
     rewrite naturalSelection (_^^^ b) th (thsb ph) | thsbTri v = refl

   soleLemma : forall {de b}(i : ([] -, b) <= de) -> thsb i == ([] -, (# ^ i))
   soleLemma (i -, b) rewrite nothU i noth = (_-, _) $= env0
   soleLemma (i -^ b) rewrite soleLemma i = refl

   thsbLemma : forall k {ga de xi}(t : (M ! k) ga) {th ph ps} ->
     Tri {_}{ga}{de}{xi} th ph ps -> Sb k (t ^ th) (thsb ph) (t ^ ps)
   thsbLemma (:S _) # {th}{ph}{ps} v
     with soleLemma ps | vaSb th {thsb ph}{# ^ ps}
   ... | q | h rewrite thsbTri v = h q
   thsbLemma (:S _) (c - td) v = cnSb c (thsbLemma _ td v)
   thsbLemma (:S _) (m % rh) v = meSb m (thsbLemma _ rh v)
   thsbLemma (:D un') null {th}{_}{ps} v
     rewrite nothU th noth | nothU ps noth = unSb
   thsbLemma (:D D *' E) (d <^ c ^> e) v =
     prSb (covPr c) (thsbLemma _ d (compTri (lcov c) v))
                    (thsbLemma _ e (compTri (rcov c) v)) (covPr c)
   thsbLemma (:D b >' D) (ll d) v = llSb (thsbLemma _ d (v -, b))
   thsbLemma (:D b >' D) (kk d) v = kkSb (thsbLemma _ d v)
   thsbLemma (:D ` s)    t v = tmSb (thsbLemma _ t v)

   _-$-_ : forall {ga de xi} -> (M :/ ga) de -> (M :/ de) xi -> (M :/ ga) xi
   sg01 -$- sg12 = env (\ t -> (:S _ /^ t) sg12) sg01
   
{-


    sbthLemma : forall {s ga de}{t : Tm s ga}{sg : ga => de}{t' : Tm s de} ->
      Sb t sg t' -> forall {xi}(th : de <= xi) ->
      Sb t (env (\ e -> e ^< th) sg) (t' ^< th)
    sbthDLemma : forall D {ga de}
      {t : Rlv D TmR ^^ ga}{sg : ga => de}{t' :  Rlv D TmR ^^ de} ->
      SbD D t sg t' -> forall {xi}(th : de <= xi) ->
      SbD D t (env (\ e -> e ^< th) sg) (t' ^< th)
    sbthLemma {sg = sg}{t'} (vaSb {i = i} q) th = vaSb (
      (i <? env (_^< th) sg)  =[ naturalSelection _ i sg >=
      env (_^< th) (i <? sg)  =[ rf (env (_^< th)) =$= q >=
      ([] -, (t' ^< th))      [QED])
    sbthLemma (cnSb c p) th = cnSb c (sbthDLemma _ p th)
    sbthDLemma .at' (atSb a) th rewrite nothU (noth -<- th) noth = atSb a
    sbthDLemma .(_ *' _) (prSb de d e de') th =
      prSb de (sbthDLemma _ d th) (sbthDLemma _ e th) (pairThin de' th)
    sbthDLemma (b !-' D) {sg = sg} (llSb p) th = llSb (sbthDLemma D p (th -, b)
      [ rf (SbD D _)
        =$= (rf _-,_
          =$= (env (_^< (th -, b)) (sg -$^ b)
                 =[ envComp _ _ _ (\ _ -> refl) sg >=
               env (_^< (th -^ b)) sg
                 =< envComp _ _ _ (\ _ -> refl) sg ]=
               (env (_^< th) sg -$^ b)
                 [QED])
          =$= (rf (va sole refl ^_) =$= (rf (_-, b) =$= nothU _ _)) )
        =$= refl >)
    sbthDLemma .(_ !-' _) (kkSb p) th = kkSb (sbthDLemma _ p th)
    sbthDLemma .([ _ ]') (tmSb p) th = tmSb (sbthLemma p th)

    cowkLemma : forall {ga0 ga1 ga2}(sg01 : ga0 => ga1)(sg12 : ga1 => ga2) b ->
      ((sg01 -$, b) -$- (sg12 -$, b)) == ((sg01 -$- sg12) -$, b)
    cowkLemma sg01 sg12 b = rf (_-, _)
      =$= ((sg01 -$^ b) -$- (sg12 -$, b))
            =[ envComp _ _ _ (\ _ -> refl) sg01 >=
          (sg01 -$- (sg12 -$^ b))
            =[ envExt _ _ (\ t -> 
               (t $^ (sg12 -$^ b))
                 =[ rf (t $^_)
                    =$= envExt _ _ (\ { (t ^ th) ->
                      rf (t ^_)
                        =$= (rf (_-^ b)
                              =$= triFun (triId _) (mkTri _ _)) }) sg12 >=
               (t $^ env (_^< (idth -^ b)) sg12)
                 =[ funSb (sb^ t _) (sbthLemma (sb^ t sg12) (idth -^ b)) >=
               ((t $^ sg12) ^< (idth -^ b))
                 =[ rf (thing (t $^ sg12) ^_)
                    =$= (rf (_-^ b) =$= triFun (mkTri _ _) (triId _)) >=
               ((t $^ sg12) ^^^ b)
                 [QED]) sg01 >=
          env (\ t -> (t $^ sg12) ^^^ b) sg01
            =< envComp _ _ _ (\ _ -> refl) sg01 ]=
          ((sg01 -$- sg12) -$^ b)
            [QED] 

    sbComp : forall {s ga0 ga1 ga2}
      {t0 : Tm s ga0}{t1 : Tm s ga1}{t2 : Tm s ga2} ->
      {sg01 : ga0 => ga1}{sg12 : ga1 => ga2} ->
      Sb t0 sg01 t1 -> Sb t1 sg12 t2 -> Sb t0 (sg01 -$- sg12) t2
    sbDComp : forall D {ga0 ga1 ga2}
      {t0 : Rlv D TmR ^^ ga0}{t1 : Rlv D TmR ^^ ga1}{t2 : Rlv D TmR ^^ ga2} ->
      {sg01 : ga0 => ga1}{sg12 : ga1 => ga2} ->
      SbD D t0 sg01 t1 -> SbD D t1 sg12 t2 -> SbD D t0 (sg01 -$- sg12) t2
    sbComp {t1 = t1}{t2}{sg01} {sg12} (vaSb {i = i} q) p12 = vaSb
      ((i <? (sg01 -$- sg12))
         =[ naturalSelection _ i sg01 >=
       env (_$^ sg12) (i <? sg01)
         =[ rf (env (_$^ sg12)) =$= q >=
       ([] -, (t1 $^ sg12))
         =[ rf ([] -,_) =$= funSb (sb _ _ sg12) p12 >=
       ([] -, t2)
         [QED])
    sbComp (cnSb c p01) (cnSb .c p12) = cnSb c (sbDComp _ p01 p12)
    sbDComp .at' (atSb a) (atSb .a) = atSb a
    sbDComp .(_ *' _) (prSb de0 d01 e01 de1) (prSb de1' d12 e12 de2)
      with pairInj de1 de1'
    ... | refl , refl = prSb de0 (sbDComp _ d01 d12) (sbDComp _ e01 e12) de2
    sbDComp (b !-' _) {sg01 = sg01}{sg12} (llSb p01) (llSb p12)
      with sbDComp _ p01 p12
    ... | h rewrite cowkLemma sg01 sg12 b = llSb h
    sbDComp .(_ !-' _) (kkSb p01) (kkSb p12) = kkSb (sbDComp _ p01 p12)
    sbDComp .([ _ ]') (tmSb p01) (tmSb p12) = tmSb (sbComp p01 p12)


-----------------------------------
-- B = One; S = Dir
data Dir : Set where chk syn : Dir
data Tag : Dir -> Set where
  em am cs ab : Tag chk
  ra el : Tag syn
BiD : (d : Dir) -> Tag d -> Syn One Dir
BiD .chk em = [ syn ]'
BiD .chk am = at'
BiD .chk cs = [ chk ]' *' [ chk ]'
BiD .chk ab = <> !-' [ chk ]'
BiD .syn ra = [ chk ]' *' [ chk ]'
BiD .syn el = [ syn ]' *' [ chk ]'

open TERM Tag BiD (\ _ -> syn)
-}
