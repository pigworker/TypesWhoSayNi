module SynU where

open import Basics
open import Atom
open import Bwd
open import Thin

data Syn (B S : Set) : Set where
  at'   : Syn B S
  _*'_  : (d e : Syn B S) -> Syn B S
  _!-'_ : B -> Syn B S -> Syn B S
  [_]'  : S -> Syn B S

module _ {B S : Set} where

  Rlv : Syn B S -> (S -> Bwd B -> Set) -> (Bwd B -> Set)
  Rlv at'       Tm []       = Atom
  Rlv at'       Tm (_ -, _) = Zero
  Rlv (D *' E)  Tm ga       = (Rlv D Tm ^*^ Rlv E Tm) ga 
  Rlv (b !-' D) Tm ga       = Scope (Rlv D Tm) b ga
  Rlv [ s ]'    Tm ga       = Tm s ga

  module TERM
    (Tag : S -> Set)(Desc : (s : S) -> Tag s -> Syn B S)
    (b2s : B -> S)
    where
    data TmR (s : S)(ga : Bwd B) : Set where
      va  : forall {b} -> Sole b ga -> b2s b == s -> TmR s ga
      _-_ : forall (c : Tag s) -> Rlv (Desc s c) TmR ga -> TmR s ga

    Tm : S -> Bwd B -> Set
    Tm s ga = TmR s ^^ ga

    _=>_ : Bwd B -> Bwd B -> Set
    ga => de = Env (\ b -> Tm (b2s b) de) ga

    _-$^_ : forall {ga de} -> ga => de -> forall b -> ga => (de -, b)
    sg -$^ b = env (_^^^ b) sg
    _-$,_ : forall {ga de} -> ga => de -> forall b -> (ga -, b) => (de -, b)
    sg -$, b = (sg -$^ b) -, (va sole refl ^ (noth -, b))

    _$_ : forall {s ga de} -> TmR s ga -> ga => de -> Tm s de
    [_/_]$_ : forall D {ga de} -> Rlv D TmR ga -> ga => de -> Rlv D TmR ^^ de
    va sole refl $ (sg -, t) = t
    (c - tr) $ sg = (c -_) ^$ ([ Desc _ c / tr ]$ sg)
    [_/_]$_ at' {[]} a sg = a ^ noth
    [_/_]$_ at' {_ -, _} () sg
    [ D *' E / d <^ c ^> e ]$ sg = pair
      (([ D / d ]$ (lcov c <? sg)) , ([ E / e ]$ (rcov c <? sg)))
    [ b !-' D / ll d ]$ sg = sco ([ D / d ]$ (sg -$, b))
    [ b !-' D / kk d ]$ sg = kk ^$ ([ D / d ]$ sg)
    [ [ s ]' / t ]$ sg = t $ sg

    _$^_ : forall {s ga de} -> Tm s ga -> ga => de -> Tm s de
    (t ^ th) $^ sg = t $ (th <? sg)

    data SbD {ga de} :
      (D : Syn B S) -> Rlv D TmR ^^ ga -> ga => de -> Rlv D TmR ^^ de -> Set
    data Sb {ga de} : forall {s} -> Tm s ga -> ga => de -> Tm s de -> Set where
      vaSb : forall {b}{i : ([] -, b) <= ga}
             {sg : ga => de}{t' : Tm (b2s b) de} ->
             (i <? sg) == ([] -, t') ->
             Sb (va sole refl ^ i) sg t'
      cnSb : forall {s}(c : Tag s){tr : Rlv (Desc _ c) TmR ^^ ga}
             {sg : ga => de}{tr' : Rlv (Desc _ c) TmR ^^ de} ->
             SbD (Desc _ c) tr sg tr' -> 
             Sb ((c -_) ^$ tr) sg ((c -_) ^$ tr')
    data SbD {ga de} where
      atSb : forall a {sg} ->
             SbD at' (a ^ noth) sg (a ^ noth)
      prSb : forall {D E sg d d' e e' de de'} ->
             Pair d e de ->
             SbD D d sg d' ->
             SbD E e sg e' ->
             Pair d' e' de' ->
             SbD (D *' E) de sg de'
      llSb : forall {b D sg ga0 de0 d d'}{th : ga0 <= ga}{ph : de0 <= de} ->
             SbD D (d ^ (th -, b)) (sg -$, b) (d' ^ (ph -, b)) ->
             SbD (b !-' D) (ll d ^ th) sg (ll d' ^ ph)
      kkSb : forall {b D sg d d'} ->
             SbD D d sg d' ->
             SbD (b !-' D) (kk ^$ d) sg (kk ^$ d')
      tmSb : forall {s t t' sg} ->
             Sb t sg t' ->
             SbD [ s ]' t sg t'

    funSb : forall {s ga de}{t : Tm s ga}{sg : ga => de}{t0 t1 : Tm s de} ->
      Sb t sg t0 -> Sb t sg t1 -> t0 == t1
    funSbD : forall D {ga de}
      {t : Rlv D TmR ^^ ga}{sg : ga => de}{t0 t1 : Rlv D TmR ^^ de} ->
      SbD D t sg t0 -> SbD D t sg t1 -> t0 == t1
    funSb (vaSb q0) (vaSb q1) with _ =< q0 ]= _ =[ q1 >= _ [QED]
    ... | refl = refl
    funSb (cnSb c p0) (cnSb .c p1) with funSbD _ p0 p1
    ... | refl = refl
    funSbD .at' (atSb a) (atSb .a) = refl
    funSbD .(_ *' _) (prSb x0 d0 e0 x1) (prSb x2 d1 e1 x3)
      with pairInj x0 x2
    ... | refl , refl with funSbD _ d0 d1 | funSbD _ e0 e1
    ... | refl | refl = pairFun x1 x3
    funSbD .(_ !-' _) (llSb p0) (llSb p1) with funSbD _ p0 p1
    ... | refl = refl
    funSbD .(_ !-' _) (kkSb p0) (kkSb p1) with funSbD _ p0 p1
    ... | refl = refl
    funSbD .([ _ ]') (tmSb p0) (tmSb p1) with funSb p0 p1
    ... | refl = refl

    Relevant : forall {ga0 ga de0 de}
               (th : ga0 <= ga)(sg : ga => de)(ph : de0 <= de) -> Set
    Relevant {ga0}{ga}{de0}{de} th sg ph =
      forall {b}(i : ([] -, b) <= ga0){t'}(q : (i <? (th <? sg)) == ([] -, t'))
      -> Sg _ \ ps' -> Tri ps' ph (thinning t')

    sbRelv : forall {s ga0 ga de0 de}
             {t : TmR s ga0}{th : ga0 <= ga}{sg : ga => de}
             {t' : TmR s de0}{ph : de0 <= de} ->
             Sb (t ^ th) sg (t' ^ ph) ->
             Relevant th sg ph
    sbDRelv : forall D {ga0 ga de0 de}
             {d : Rlv D TmR ga0}{th : ga0 <= ga}{sg : ga => de}
             {d' : Rlv D TmR de0}{ph : de0 <= de} ->
             SbD D (d ^ th) sg (d' ^ ph) ->
             Relevant th sg ph
    sbRelv (vaSb q') ([] -, b) q
      with _ =< rf (([] -, b) <?_) =$= q' ]= _ =[ q >= _ [QED]
    ... | refl = _ , idTri _
    sbRelv (vaSb q') (() -^ _) q
    sbRelv (cnSb c tr) i q = sbDRelv (Desc _ c) tr i q
    sbDRelv .at' (atSb a) () q
    sbDRelv _ (prSb (mkPair _ _ lv c rv) dh eh (mkPair _ _ lu b ru)) i q
      with cover1 i c
    sbDRelv ._ {sg = sg} (prSb (mkPair _ _ lv c rv) dh eh (mkPair _ _ lu b ru)) i q
      | inl (j , v) with cossaTri v lv | sbDRelv _ dh j
    ... | _ , v0 , v1 | dh' rewrite compSel v0 sg | compSel v1 sg =
      let _ , u = dh' q ; _ , _ , v = assocTri' u lu in _ , v
    sbDRelv ._ {sg = sg} (prSb (mkPair _ _ lv c rv) dh eh (mkPair _ _ lu b ru)) i q
      | inr (j , v) with cossaTri v rv | sbDRelv _ eh j
    ... | _ , v0 , v1 | eh' rewrite compSel v0 sg | compSel v1 sg =
      let _ , u = eh' q ; _ , _ , v = assocTri' u ru in _ , v
    sbDRelv (b !-' _) {th = th} {sg = sg} (llSb d) i {t'} q
      with sbDRelv _ d (i -^ b) (
        (i <? (th <? (sg -$^ b)))
          =[ rf (i <?_) =$= naturalSelection _ th sg >=
        (i <? ((th <? sg) -$^ b))
          =[ naturalSelection _ i (th <? sg) >=
        ((i <? (th <? sg)) -$^ b)
          =[ rf (_-$^ b) =$= q >=
        ([] -, (t' ^^^ b))
          [QED])
    sbDRelv (b !-' _) {th = th} {sg} (llSb d) i {thing ^ thinning} q
      | _ , (v -^, .b) = _ , v
    sbDRelv .(_ !-' _) (kkSb x) i q = sbDRelv _ x i q
    sbDRelv .([ _ ]') (tmSb x) i q = sbRelv x i q

    sb : forall {s ga0 ga de}(t : TmR s ga0)(th : ga0 <= ga)(sg : ga => de) ->
         Sb (t ^ th) sg (t $ (th <? sg))
    sbD : forall D {ga0 ga de}(d : Rlv D TmR ga0)(th : ga0 <= ga)(sg : ga => de) ->
         SbD D (d ^ th) sg ([ D / d ]$ (th <? sg))
    sb (va sole refl) i sg with i <? sg | \ t' -> vaSb {i = i}{sg = sg}{t'}
    ... | [] -, t | h = h _ refl
    sb (c - tr) th sg = cnSb c (sbD (Desc _ c) tr th sg)
    sbD at' {[]} a th sg rewrite nothU th noth = atSb a
    sbD at' {_ -, _} () th sg
    sbD (D *' E) (d <^ c ^> e) th sg
      with lcov c -<- th | mkTri (lcov c) th | rcov c -<- th | mkTri (rcov c) th
    ... | lth | lv | rth | rv rewrite compSel lv sg | compSel rv sg =
      prSb (mkPair _ _ lv c rv) (sbD D d lth sg) (sbD E e rth sg) (pairPair _ _) 
    sbD (b !-' D) {de = de} (ll d) th sg  with sbD D d (th -, b) (sg -$, b)
    ... | dh with sbDRelv D dh (noth -, b) (rf _-,_ =$= env0 =$= refl)
    ... | ph , v with
      th <? env (_^^^ b) sg | env (_^^^ b) (th <? sg) | naturalSelection (_^^^ b) th sg
    sbD (b !-' D) {de = de} (ll d) th sg | dh | ph , v | sg0 | .sg0 | refl
      with [ D / d ]$ (sg0 -, (va sole refl ^ (noth -, b)))
    sbD (b !-' D) {de = de} (ll d) th sg | dh | .(_ -, b) , (v -, .b) | sg0 | .sg0
      | refl | _ ^ .(_ -, b) = llSb dh
    sbD (b !-' D) (kk d) th sg = kkSb (sbD D d th sg)
    sbD [ s ]' t th sg = tmSb (sb t th sg)

    sb^ : forall {s ga de}(t : Tm s ga)(sg : ga => de) ->
         Sb t sg (t $^ sg)
    sb^ (t ^ th) sg = sb t th sg


    thsb : forall {ga de} -> ga <= de -> ga => de
    thsb []        = []
    thsb (th -, b) = thsb th -$, b
    thsb (th -^ b) = thsb th -$^ b

    thsbTri : forall {ga de xi}
      {th : ga <= de}{ph : de <= xi}{ps : ga <= xi} -> Tri th ph ps ->
      (th <? thsb ph) == thsb ps
    thsbTri [] = refl
    thsbTri (_-,_ {th = th} {ph} v b)
      rewrite naturalSelection (_^^^ b) th (thsb ph) | thsbTri v = refl
    thsbTri (_-^,_ {th = th} {ph} v b)
      rewrite naturalSelection (_^^^ b) th (thsb ph) | thsbTri v = refl
    thsbTri {th = th} (_-^_ {ph = ph} v b)
      rewrite naturalSelection (_^^^ b) th (thsb ph) | thsbTri v = refl

    soleLemma : forall {de b}(i : ([] -, b) <= de) ->
      thsb i == ([] -, (va sole refl ^ i))
    soleLemma (i -, b) rewrite nothU i noth = rf (_-, _) =$= env0
    soleLemma (i -^ b) rewrite soleLemma i = refl

    thsbLemma : forall {s ga de xi}(t : TmR s ga)
      {th : ga <= de}{ph : de <= xi}{ps : ga <= xi} -> Tri th ph ps ->
      Sb (t ^ th) (thsb ph) (t ^ ps)
    thsbLemmaD : forall D {ga de xi}(t : Rlv D TmR ga)
      {th : ga <= de}{ph : de <= xi}{ps : ga <= xi} -> Tri th ph ps ->
      SbD D (t ^ th) (thsb ph) (t ^ ps)
    thsbLemma (va sole refl) {th = th}{ph}{ps} v
      with soleLemma ps | vaSb {i = th}{thsb ph}{va sole refl ^ ps}
    ... | q | h rewrite thsbTri v = h q
    thsbLemma (c - tr) v = cnSb c (thsbLemmaD _ tr v)
    thsbLemmaD at' {[]} a {th} {ps = ps} v
      rewrite nothU th noth | nothU ps noth = atSb a
    thsbLemmaD at' {ga -, x} () v
    thsbLemmaD (D *' E) (d <^ c ^> e) {th = th}{ph}{ps} v
      = prSb
      (mkPair d e (mkTri _ _) c (mkTri _ _))
      (thsbLemmaD D d (compTri (lcov c) v))
      (thsbLemmaD E e (compTri (rcov c) v))
      (mkPair d e (mkTri _ _) c (mkTri _ _))
    thsbLemmaD (b !-' D) (ll d) v = llSb (thsbLemmaD D d (v -, b))
    thsbLemmaD (b !-' D) (kk d) v = kkSb (thsbLemmaD D d v)
    thsbLemmaD [ s ]' t v = tmSb (thsbLemma t v)

    _-$-_ : forall {ga0 ga1 ga2} -> ga0 => ga1 -> ga1 => ga2 -> ga0 => ga2
    sg01 -$- sg12 = env (_$^ sg12) sg01

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
