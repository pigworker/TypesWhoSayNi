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

 Sort = Syn B S

 Rlv : Sort -> (S -> Bwd B -> Set) -> (Bwd B -> Set)
 Rlv un'       Tm ga       = Null ga
 Rlv (D *' E)  Tm ga       = (Rlv D Tm ^*^ Rlv E Tm) ga 
 Rlv (b >' D)  Tm ga       = Scope (Rlv D Tm) b ga
 Rlv (` s)     Tm ga       = Tm s ga

 module TERM (Cn : S -> Set)(Ds : {s : S} -> Cn s -> Sort)(b2s : B -> S)
  where

  spine : Bwd B -> Syn B S
  spine [] = un'
  spine (ga -, b) = spine ga *' ` b2s b

  data TmR (M : S * Bwd B -> Set)(s : S)(ga : Bwd B) : Set

  infix 4 _!_ _!^_
  _!_ _!^_ : (M : S * Bwd B -> Set) -> Sort -> Bwd B -> Set
  (M !^ k)    = ((M ! k) :^_)
  (M ! D)  = Rlv D (TmR M)

  infix 5 _-_ _%_
  data TmR M s ga where
    va  : {b : B}(z : Sole b ga)(q : b2s b == s)               -> (M ! ` s) ga
    _-_ : (c : Cn s)(td : (M ! Ds c) ga)                       -> (M ! ` s) ga
    _%_ : {xi : Bwd B}(m : M (s , xi))(rh : (M ! spine xi) ga) -> (M ! ` s) ga

  pattern # = va sole refl

  #0 : forall {M ga b} -> (M !^ ` b2s b) (ga -, b)
  #0 = # ^ noth -, _

  infix 4 _:/_
  _:/_ : (M : S * Bwd B -> Set) -> Bwd B -> Bwd B -> Set
  (M :/ ga) de = Env (\ b -> (M !^ ` b2s b) de) ga
  
  module _ {M : S * Bwd B -> Set} where

   module _ {ga de : Bwd B} (sg : (M :/ ga) de) where
    dom = ga ; cod = de
    module _ (b : B) where
     infixl 8 _-$^_ _-$,_
     _-$^_ : (M :/ ga) (de -, b)  ;  _-$,_ : (M :/ ga -, b) (de -, b)
     _-$^_ = env (_^^^ b) sg      ;  _-$,_ = _-$^_ -, #0

   infix 4 _/_ _/^_
   _/_  : forall k {ga de} -> (M :/ ga) de -> (M ! k) ga  -> (M !^ k) de
   _/^_ : forall k {ga de} -> (M :/ ga) de -> (M !^ k) ga -> (M !^ k) de
   (` _ / sg)        (c - td) = (c -_) ^$ (Ds c / sg) td
   (` _ / sg) (_%_ {xi} m rh) = (m %_) ^$ (spine xi / sg) rh
   (` _ / (_ -, t))         # = t
   (un'    / sg) null = null ^ noth
   (D *' E / sg) (d <^ c ^> e) = (D /^ sg) (d &^ c) ^,^ (E /^ sg) (c ^& e)
   (b >' D / sg) (ll d) = sco ((D / sg -$, b) d)
   (b >' D / sg) (kk d) = kk ^$ (D / sg) d
   (D /^ sg) (t ^ th) = (D / th <? sg) t

   data Sb {ga de} : (k : Sort) ->
     (M !^ k) ga -> (M :/ ga) de -> (M !^ k) de -> Set
     where
     vaSb : forall {b}(i : ([] -, b) <= ga){sg t'} ->
            (i <? sg) == ([] -, t') ->
            Sb (` _) (# ^ i) sg t'
     cnSb : forall {s}(c : Cn s){tr sg tr'} ->
            Sb (Ds c) tr sg tr' -> 
            Sb (` _) ((c -_) ^$ tr) sg ((c -_) ^$ tr')
     meSb : forall {s xi}(m : M (s , xi)){rh sg rh'} ->
            Sb (spine xi) rh sg rh' ->
            Sb (` s) ((m %_) ^$ rh) sg ((m %_) ^$ rh')
     unSb : forall {sg} ->
            Sb (un') (null ^ noth) sg (null ^ noth)
     prSb : forall {D E sg d d' e e' de de'} ->         Pr d e de ->
            Sb D d sg d' -> Sb E e sg e' ->   Pr d' e' de' ->
            Sb (D *' E) de sg de'
     llSb : forall {b D sg ga0 de0 d d'}{th : ga0 <= ga}{ph : de0 <= de} ->
            Sb D (d ^ (th -, b)) (sg -$, b) (d' ^ (ph -, b)) ->
            Sb (b >' D) (ll d ^ th) sg (ll d' ^ ph)
     kkSb : forall {b D sg d d'} ->
            Sb D d sg d' ->
            Sb (b >' D) (kk ^$ d) sg (kk ^$ d')

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
   sbRelv {b >' D} {th = th}{sg} (llSb p) i {t} q with sbRelv p (i -^ b) (
       (i <? th <? (sg -$^ b))    =[ (i <?_) $= naturalSelection _ th sg >=
       (i <? ((th <? sg) -$^ b))  =[ naturalSelection _ i (th <? sg) >=
       ((i <? th <? sg) -$^ b)    =[ (_-$^ b) $= q >=
       ([] -, (t ^^^ b))          [QED])
   ... | _ , (v -^, .b) = _ , v
   sbRelv (kkSb p) i q = sbRelv p i q

   sb : forall k {ga0 ga de}(t : (M ! k) ga0)(th : ga0 <= ga)
        (sg : (M :/ ga) de) -> Sb k (t ^ th) sg ((k /^ sg) (t ^ th))
   sb (` _) # i sg  with i <? sg | \ t -> vaSb i {sg} {t}
   ... | [] -, t | h = h _ refl
   sb (` _) (c - td) th sg = cnSb c (sb (Ds c) td th sg)
   sb (` _) (_%_ {xi} m rh) th sg = meSb m (sb (spine xi) rh th sg)
   sb (un') null th sg rewrite nothU th noth = unSb
   sb (D *' E) (d <^ c ^> e) th sg
     with lcov c -<- th | lcov c -v- th | rcov c -<- th | rcov c -v- th
   ... | ph | lv | ps | rv rewrite compSel lv sg | compSel rv sg =
     prSb (mkPr lv c rv) (sb D d ph sg) (sb E e ps sg) (prPr _ _)
   sb (b >' D) {de = de} (ll d) th sg with sb D d (th -, b) (sg -$, b)
   ... | h with sbRelv h (noth -, b) (_-,_ $= env0 =$= refl)
   ... | ph , v with th <? env (_^^^ b) sg | env (_^^^ b) (th <? sg)
                   | naturalSelection (_^^^ b) th sg
   ... | sg0 | _ | refl with (D / sg0 -, #0) d
   sb (b >' D) (ll d) th sg | h | _ , (v -, _) | _ | _ | refl | _ = llSb h
   sb (b >' D) (kk d) th sg = kkSb (sb D d th sg)

   sb^ : forall k {ga de}(t : (M !^ k) ga)(sg : (M :/ ga) de) ->
     Sb k t sg ((k /^ sg) t)
   sb^ k (t ^ th) = sb k t th

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
   thsbLemma (` _) # {th}{ph}{ps} v
     with soleLemma ps | vaSb th {thsb ph}{# ^ ps}
   ... | q | h rewrite thsbTri v = h q
   thsbLemma (` _) (c - td) v = cnSb c (thsbLemma _ td v)
   thsbLemma (` _) (m % rh) v = meSb m (thsbLemma _ rh v)
   thsbLemma (un') null {th}{_}{ps} v
     rewrite nothU th noth | nothU ps noth = unSb
   thsbLemma (D *' E) (d <^ c ^> e) v =
     prSb (covPr c) (thsbLemma _ d (compTri (lcov c) v))
                    (thsbLemma _ e (compTri (rcov c) v)) (covPr c)
   thsbLemma (b >' D) (ll d) v = llSb (thsbLemma _ d (v -, b))
   thsbLemma (b >' D) (kk d) v = kkSb (thsbLemma _ d v)

   _-$-_ : forall {ga de xi} -> (M :/ ga) de -> (M :/ de) xi -> (M :/ ga) xi
   sg -$- ta = env (` _ /^ ta) sg

   sbthLemma : forall {k ga de}{t : (M !^ k) ga}{sg}{t' : (M !^ k) de} ->
     Sb k t sg t' -> forall {xi}(th : de <= xi) ->
     Sb k t (env (\ e -> e ^< th) sg) (t' ^< th)
   sbthLemma {sg = sg}{t'} (vaSb i q) th = vaSb i (
     (i <? env (_^< th) sg)  =[ naturalSelection _ i sg >=
     env (_^< th) (i <? sg)  =[ env (_^< th) $= q >=
     ([] -, (t' ^< th))      [QED])
   sbthLemma (cnSb c p) th = cnSb c (sbthLemma p th)
   sbthLemma (meSb m p) th = meSb m (sbthLemma p th)
   sbthLemma unSb th rewrite nothU (noth -<- th) noth = unSb
   sbthLemma (prSb de d e de') th = prSb de
     (sbthLemma d th) (sbthLemma e th) (prThin de' th)
   sbthLemma {b >' D} {sg = sg} (llSb p) th = llSb (sbthLemma p (th -, b)
     [ Sb _ _ $=  (_-,_ $= envComps sg (\ _ -> refl)
                       =$= ((# ^_) $= ((_-, b) $= nothU _ _)))
             =$= refl >)
   sbthLemma (kkSb p) th = kkSb (sbthLemma p th)

   cowkLemma : forall {ga de xi}(sg : (M :/ ga) de)(ta : (M :/ de) xi) b ->
     ((sg -$, b) -$- (ta -$, b)) == ((sg -$- ta) -$, b)
   cowkLemma sg ta b = (_-, _) $= 
     ((sg -$^ b) -$- (ta -$, b))  =[ (envComps sg \ t ->
       (` _ /^ ta -$^ b) t
         =[ (\ z -> (` _ /^ z) t) $= envExt _ _ (\ t -> 
              (thing t ^_) $= ((_-^ b) $= triFun (triId _) (_ -v- _))) ta >=
       (` _ /^ env (_^< (idth -^ b)) ta) t
         =[ funSb (sb^ (` _) t _) (sbthLemma (sb^ _ t ta) (idth -^ b)) >=
       ((` _ /^ ta) t ^< (idth -^ b))
         =[ (thing ((` _ /^ ta) t) ^_)
            $= ((_-^ b) $= triFun (_ -v- _) (triId _)) >=
       ((` _ /^ ta) t ^^^ b)       [QED]) >=
     ((sg -$- ta) -$^ b)          [QED]

   sbComp : forall {k ga de xi sg ta}
     {t0 : (M !^ k) ga}{t1 : (M !^ k) de}{t2 : (M !^ k) xi} ->
     Sb k t0 sg t1 -> Sb k t1 ta t2 -> Sb k t0 (sg -$- ta) t2
   sbComp {sg = sg}{ta}{t1 = s}{t} (vaSb i q) r = vaSb i (
     (i <? (sg -$- ta))          =[ naturalSelection _ i sg >=
     env (` _ /^ ta) (i <? sg)  =[ env (` _ /^ ta) $= q >=
     ([] -, (` _ /^ ta) s)      =[ ([] -,_) $= funSb (sb^ _ _ ta) r >=
     ([] -, t)                   [QED])
   sbComp (cnSb c p) (cnSb .c r) = cnSb c (sbComp p r)
   sbComp (meSb m p) (meSb .m r) = meSb m (sbComp p r)
   sbComp unSb unSb = unSb
   sbComp (prSb a p q b) (prSb c r s d) with prInj b c ; ... | refl , refl =
     prSb a (sbComp p r) (sbComp q s) d
   sbComp {b >' D}{sg = sg}{ta} (llSb p) (llSb r) =
     llSb (sbComp p r [ Sb _ _ $= cowkLemma sg ta b =$= refl >)
   sbComp (kkSb p) (kkSb r) = kkSb (sbComp p r)

-----------------------------------
module BIDI (Atom : Set) where

 data Dir : Set where chk syn : Dir
  
 data Tag : Dir -> Set where
   em cs ab : Tag chk
   am : Atom -> Tag chk
   ra el : Tag syn
    
 BiD : {d : Dir} -> Tag d -> Syn One Dir
 --   sort  tag      arity
 BiD {.chk} em     = ` syn
 BiD {.chk} cs     = ` chk *' ` chk
 BiD {.chk} ab     = <> >' ` chk
 BiD {.chk} (am a) = un'
 BiD {.syn} ra     = ` chk *' ` chk
 BiD {.syn} el     = ` syn *' ` chk

 open TERM Tag BiD (\ _ -> syn)
