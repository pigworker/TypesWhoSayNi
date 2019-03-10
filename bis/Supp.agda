module Supp where

open import Basics
open import Cats
open import Eq
open import Bwd
open import All
open import Thin
open import Pat
open import Term
open import ActCats

open Cat (OPE {One})

triAct : forall {M l d ga0 ga1 ga2}
  {th : ga0 <= ga1}{ph : ga1 <= ga2}{ps : ga0 <= ga2}
  (t : Term M ga0 l d)(x : Tri th ph ps) ->
  (t ^ ps) == ((t ^ th) ^ ph)
triAct {th = th}{ph}{ps} t x =
  (t ^ ps) =[ (t ^_) $= triDet x (mkTri th ph) >=
  (t ^ (th -< ph)) =< thinco t th ph ]=
  ((t ^ th) ^ ph) [QED]


triInvSuNo : forall {ga0 ga1 ga2}
  {th : ga0 <= (ga1 -, <>)}{ph : ga1 <= ga2}{ps : ga0 <= ga2} ->
  Tri th (ph su) (ps no) -> Sg (ga0 <= ga1) \ th' -> Tri th' ph ps
triInvSuNo (t nosuno) = _ , t

triInvSuSu : forall {ga0 ga1 ga2}
  {th : (ga0 -, <>) <= (ga1 -, <>)}{ph : ga1 <= ga2}{ps : ga0 <= ga2} ->
  Tri th (ph su) (ps su) -> Sg (ga0 <= ga1) \ th' -> Tri th' ph ps
triInvSuSu (t su) = _ , t

open Act THIN


data _<[_]z=_ {M ga de} : forall {n : Nat}(ez0 : All (\ _ -> Term M ga lib syn) n)(th : ga <= de)(ez1 : All (\ _ -> Term M de lib syn) n )-> Set
data _<[_]=_ {M ga de} : forall {l d}(t0 : Term M ga l d)(th : ga <= de)(t1 : Term M de l d) -> Set where

  atom : forall {th} a -> atom a <[ th ]= atom a
  cons : forall {th s0 s1 t0 t1} -> s0 <[ th ]= s1 -> t0 <[ th ]= t1 -> cons s0 t0 <[ th ]= cons s1 t1
  abst : forall {th t0 t1} -> t0 <[ th su ]= t1 -> abst t0 <[ th ]= abst t1
  thnk : forall {th n0 n1} -> n0 <[ th ]= n1 -> thnk n0 <[ th ]= thnk n1
  essl : forall {th d}{t0 : Term M ga ess d}{t1} -> t0 <[ th ]= t1 -> essl t0 <[ th ]= essl t1
  vari : forall {th}{i j} -> Tri i th j -> vari i <[ th ]= vari j
  elim : forall {th e0 e1 s0 s1} -> e0 <[ th ]= e1 -> s0 <[ th ]= s1 -> elim e0 s0 <[ th ]= elim e1 s1
  _::_ : forall {th t0 t1 T0 T1} -> t0 <[ th ]= t1 -> T0 <[ th ]= T1 -> (t0 :: T0) <[ th ]= (t1 :: T1)
  _?-_ : forall {th n} x {ez0 : All _ n}{ez1} -> ez0 <[ th ]z= ez1 -> (x ?- ez0) <[ th ]= (x ?- ez1)
  mets : forall {th} x -> mets x <[ th ]= mets x

data _<[_]z=_ {M ga de} where
  [] : forall {th} -> [] <[ th ]z= []
  _-,_ : forall {th n}{ez0 : All _ n}{ez1 e0 e1} -> ez0 <[ th ]z= ez1 -> e0 <[ th ]= e1 -> (ez0 -, e0) <[ th ]z= (ez1 -, e1)

thinR : forall {M ga de l d}(t : Term M ga l d)(th : ga <= de) -> t <[ th ]= (t ^ th)
thinzR : forall {M ga de n}(ez : All (\ _ -> Term M ga lib syn) n)(th : ga <= de) -> ez <[ th ]z= actz ez (refl , th)
thinR (atom a) th = atom a
thinR (cons s t) th = cons (thinR s th) (thinR t th)
thinR (abst t) th = abst (thinR t (th su))
thinR (vari i) th = vari (mkTri i th)
thinR (elim e s) th = elim (thinR e th) (thinR s th)
thinR {d = chk} (essl k) th = essl (thinR k th)
thinR {d = syn} (essl n) th = essl (thinR n th)
thinR (thnk n) th = thnk (thinR n th)
thinR (t :: T) th = thinR t th :: thinR T th
thinR (x ?- ez) th = x ?- thinzR ez th
thinR (mets x) th = mets x
thinzR [] th = []
thinzR (ez -, e) th = thinzR ez th -, thinR e th

nihtR : forall {M ga de l d}{th : ga <= de}{t0 : Term M ga l d}{t1 : Term M de l d} ->
  t0 <[ th ]= t1 -> t1 == (t0 ^ th)
znihtR : forall {M ga de n}{th : ga <= de}{ez0 : [ M ! n ]/ ga}{ez1 : [ M ! n ]/ de} ->
  ez0 <[ th ]z= ez1 -> ez1 == Act.actz THIN ez0 (refl , th)
nihtR (atom a) = refl
nihtR (cons s t) rewrite nihtR s | nihtR t = refl
nihtR (abst t) rewrite nihtR t = refl
nihtR (thnk n) rewrite nihtR n = refl
nihtR {d = syn} (essl n) rewrite nihtR n = refl
nihtR {d = chk} (essl k) rewrite nihtR k = refl
nihtR (vari x) = vari $= triDet x (mkTri _ _)
nihtR (elim e s) rewrite nihtR e | nihtR s = refl
nihtR (t :: T) rewrite nihtR t | nihtR T = refl
nihtR (x ?- ez) = (x ?-_) $= znihtR ez
nihtR (mets x) = refl
znihtR [] = refl
znihtR (ez -, e) rewrite znihtR ez | nihtR e = refl

thickR? : forall {M ga de l d}(th : ga <= de)(t' : Term M de l d) -> Dec (Sg _ \ t -> t <[ th ]= t')
thickzR? : forall {M ga de n}(th : ga <= de)(ez' : All (\ _ -> Term M de lib syn) n) -> Dec (Sg _ \ ez -> ez <[ th ]z= ez')
thickR? th (atom a) = #1 , atom a , atom a
thickR? th (cons s' t') with thickR? th s' | thickR? th t'
thickR? th (cons s' t') | #0 , sn | tb , ta = #0 , \ { (_ , cons sy _) -> sn (_ , sy) }
thickR? th (cons s' t') | #1 , sa | #0 , tn = #0 , \ { (_ , cons _ ty) -> tn (_ , ty) }
thickR? th (cons s' t') | #1 , s , sy | #1 , t , ty = #1 , cons s t , cons sy ty
thickR? th (abst t') with thickR? (th su) t'
thickR? th (abst t') | #0 , tn = #0 , \ { (_ , abst ty) -> tn (_ , ty) }
thickR? th (abst t') | #1 , t , ty = #1 , abst t , abst ty
thickR? th (vari i) with thick? th i
thickR? th (vari i) | #0 , z = #0 , \ { (_ , vari t) -> z (_ , triDet t (mkTri _ th)) }
thickR? th (vari .(j -< th)) | #1 , j , refl = #1 , vari j , vari (mkTri j th)
thickR? th (elim e' s') with thickR? th e' | thickR? th s'
thickR? th (elim e' s') | #0 , en | sb , sa = #0 , \ { (_ , elim ey _) -> en (_ , ey) }
thickR? th (elim e' s') | #1 , ea | #0 , sn = #0 , \ { (_ , elim _ sy) -> sn (_ , sy) }
thickR? th (elim e' s') | #1 , e , ey | #1 , s , sy = #1 , elim e s , elim ey sy
thickR? th (essl t') with thickR? th t'
thickR? th (essl t') | #0 , tn = #0 , \ { (_ , essl ty) -> tn (_ , ty) }
thickR? th (essl t') | #1 , t , ty = #1 , essl t , essl ty
thickR? th (thnk n') with thickR? th n'
thickR? th (thnk n') | #0 , nn = #0 , \ { (_ , thnk ny) -> nn (_ , ny) }
thickR? th (thnk n') | #1 , n , ny = #1 , thnk n , thnk ny
thickR? th (t' :: T') with thickR? th t' | thickR? th T'
thickR? th (t' :: T') | #0 , tn | Tb , Ta = #0 , \ { (_ , ty :: _) -> tn (_ , ty) }
thickR? th (t' :: T') | #1 , ta | #0 , Tn = #0 , \ { (_ , _ :: Ty) -> Tn (_ , Ty) }
thickR? th (t' :: T') | #1 , t , ty | #1 , T , Ty = #1 , t :: T , ty :: Ty
thickR? th (x ?- ez') with thickzR? th ez'
thickR? th (x ?- ez') | #0 , n = #0 , \ { (_ , _ ?- y) -> n (_ , y) } 
thickR? th (x ?- ez') | #1 , ez , ezy = #1 , x ?- ez , x ?- ezy
thickR? th (mets x) = #1 , mets x , mets x
thickzR? th [] = #1 , [] , []
thickzR? th (ez' -, e') with thickzR? th ez' | thickR? th e'
thickzR? th (ez' -, e') | #0 , n | b , a = #0 , \ { (_ , y -, _) -> n (_ , y) }
thickzR? th (ez' -, e') | #1 , az | #0 , n = #0 , \ { (_ , _ -, y) -> n (_ , y) }
thickzR? th (ez' -, e') | #1 , ez , ezy | #1 , e , ey = #1 , ez -, e , ezy -, ey

_+t_ : forall {M ga0 ga1 ga2 l d}
       {t0 : Term M ga0 l d}{t1 : Term M ga1 l d}{t2 : Term M ga2 l d}
       {th : ga0 <= ga1}{ph : ga1 <= ga2} ->
       t0 <[ th ]= t1 -> t1 <[ ph ]= t2 ->
       t0 <[ th -< ph ]= t2
_+tz_ : forall {M ga0 ga1 ga2 de}
       {ez0 : [ M ! de ]/ ga0}{ez1 : [ M ! de ]/ ga1}{ez2 : [ M ! de ]/ ga2}
       {th : ga0 <= ga1}{ph : ga1 <= ga2} ->
       ez0 <[ th ]z= ez1 -> ez1 <[ ph ]z= ez2 ->
       ez0 <[ th -< ph ]z= ez2
atom a +t atom .a = atom a
cons s t +t cons s' t' = cons (s +t s') (t +t t')
abst t +t abst t' = abst (t +t t')
thnk n +t thnk n' = thnk (n +t n')
essl t +t essl t' = essl (t +t t')
_+t_ {th = th} {ph} (vari {i = i0} {j0} i) (vari j)
  with triDet i (mkTri i0 th) | triDet j (mkTri j0 ph)  -- this is the shitty way of cooking it
... | refl | refl rewrite sym (cocoC i0 th ph) = vari (mkTri i0 (th -< ph))
elim e s +t elim e' s' = elim (e +t e') (s +t s')
(t :: T) +t (t' :: T') = (t +t t') :: (T +t T')
(x ?- ez) +t (.x ?- ez') = x ?- (ez +tz ez')
mets x +t mets .x = mets x
[] +tz [] = []
(ez -, e) +tz (ez' -, e') = (ez +tz ez') -, (e +t e')


{-
supp : forall {M l d ga}(t : Term M ga l d) ->
  Sg Nat \ de ->
  Sg (de <= ga) \ th ->
  Sg (Term M de l d) \ t' ->
  t' <[ th ]= t *
    ((de+ : Nat)(th+ : de+ <= ga)(t+ : Term M de+ l d) -> t+ <[ th+ ]= t ->
      Sg (de <= de+) \ ph -> Tri ph th+ th)
supp (atom a) = [] , oe , atom a , atom a , \ { _ _ _ (atom a) -> _ , oeTri _ }
supp (cons s t) with supp s | supp t
... | des , ths , s' , ss' , us | det , tht , t' , tt' , ut with coproduct ths tht
... | de , phs , pht , th , tr0 , tr1 , u = de , th , cons (s' ^ phs) (t' ^ pht) , cons {!!} {!!} , {!!}
supp (abst t) = {!!}
supp (vari i) = {!!}
supp (elim e s) = {!!}
supp (essl t) = {!!}
supp (thnk n) = {!!}
supp (t :: T) = {!!}
supp (x ?- ez) = {!!}
supp (mets x) = {!!}
-}

support : forall {M l d ga}(t : Term M ga l d) ->
  Sg Nat \ de ->
  Sg (de <= ga) \ th ->
  Sg (Term M de l d) \ t' ->
  t == (t' ^ th) *
    ((de+ : Nat)(th+ : de+ <= ga)(t+ : Term M de+ l d) -> t == (t+ ^ th+) ->
      Sg (de <= de+) \ ph -> Tri ph th+ th)
supportz : forall {M n ga}(ez : All (\ _ -> Term M ga lib syn) n) ->
  Sg Nat \ de ->
  Sg (de <= ga) \ th ->
  Sg (All (\ _ -> Term M de lib syn) n) \ ez' ->
  ez == actz ez' (refl , th) *
    ((de+ : Nat)(th+ : de+ <= ga)(ez+ : All (\ _ -> Term M de+ lib syn) n) ->
      ez == actz ez+ (refl , th+) ->
      Sg (de <= de+) \ ph -> Tri ph th+ th)
support (atom a)   = _ , oe , atom a , refl , \
  { de+ th+ (atom a) refl -> oe , oeTri _
  ; de+ th+ (cons _ _) ()
  ; de+ th+ (abst _) ()
  }
support (cons s t) with support s | support t
... | des , ths , s' , qs , us  | det , tht , t' , qt , ut with coproduct ths tht
... | de , phs , pht , th , t0 , t1 , u
  = de , th , cons (s' ^ phs) (t' ^ pht)
  , cons $= (_ =[ qs >= _ =[ triAct s' t0 >= _ [QED])
        =$= (_ =[ qt >= _ =[ triAct t' t1 >= _ [QED])
  ,  \ { de+ th+ (atom a) ()
       ; de+ th+ (cons s+ t+) refl -> 
         let _ , t2 = us de+ th+ s+ refl
             _ , t3 = ut de+ th+ t+ refl
             ps , t4 , t5 , t6 = u t2 t3
         in  ps , t5
       ; de+ th+ (abst t+) () }
support (abst t)   with support t
support (abst ._) | _ , (th no) , t' , refl , u = _ , th , abst (t' ^ (oi no))
  , abst $= triAct t' (oiTri th nosuno)
  , \ { de+ th+ (atom a) ()
      ; de+ th+ (cons _ _) ()
      ; de+ th+ (abst t+) q+ -> termNoConf q+ \ q ->
        _ , snd (triInvSuNo (snd (u _ (th+ su) t+ q))) }
support (abst ._) | _ , (th su) , t' , refl , u = _ , th , abst t'
  , refl
  , \ { de+ th+ (atom a) ()
      ; de+ th+ (cons _ _) ()
      ; de+ th+ (abst t+) q+ -> termNoConf q+ \ q ->
        _ , snd (triInvSuSu (snd (u _ (th+ su) t+ q))) }
support (vari i)   = _ , i , vari (ze su)
  , vari $= triDet (oiTri i) (mkTri oi i)
  , \ { de+ th+ (vari j) q+ -> termNoConf q+ \ { refl -> j , mkTri j th+ } 
      ; de+ th+ (elim _ _) () ; de+ th+ (mets x) () }
support (elim e s) with support e | support s
... | dee , the , e' , qe , ue  | des , ths , s' , qs , us with coproduct the ths
... | de , phe , phs , th , t0 , t1 , u
  = de , th , elim (e' ^ phe) (s' ^ phs)
  , elim $= (_ =[ qe >= _ =[ triAct e' t0 >= _ [QED])
        =$= (_ =[ qs >= _ =[ triAct s' t1 >= _ [QED])
  , \ { de+ th+ (vari i) ()
      ; de+ th+ (elim e+ s+) refl ->
        let _ , t2 = ue de+ th+ e+ refl
            _ , t3 = us de+ th+ s+ refl
            ps , t4 , t5 , t6 = u t2 t3
        in  ps , t5
      ; de+ th+ (mets x) () }
support {d = chk} (essl t)   with support t
... | de , th , t' , q , u = _ , th , essl t' , essl $= q ,
  \ { de+ th+ (essl t+) refl -> u de+ th+ t+ refl
    ; de+ th+ (thnk t+) ()
    ; de+ th+ (x ?- _) () }
support {d = syn} (essl t)   with support t
... | de , th , t' , q , u = _ , th , essl t' , essl $= q ,
  \ { de+ th+ (essl t+) refl -> u de+ th+ t+ refl
    ; de+ th+ (t+ :: _) () }
support (thnk n)   with support n
... | de , th , n' , q , u = _ , th , thnk n' , thnk $= q ,
  \ { de+ th+ (essl t+) ()
    ; de+ th+ (thnk n+) refl -> u de+ th+ n+ refl
    ; de+ th+ (x ?- _) () }
support (t :: T)   with support t | support T
... | det , tht , t' , qt , ut | deT , thT , T' , qT , uT with coproduct tht thT
... | de , pht , phT , th , t0 , t1 , u
    = de , th , (t' ^ pht) :: (T' ^ phT)
    , _::_ $= (_ =[ qt >= _ =[ triAct t' t0 >= _ [QED])
          =$= (_ =[ qT >= _ =[ triAct T' t1 >= _ [QED])
    , \ { de+ th+ (essl t+) ()
      ; de+ th+ (t+ :: T+) refl ->
        let _ , t2 = ut de+ th+ t+ refl
            _ , t3 = uT de+ th+ T+ refl
            ps , t4 , t5 , t6 = u t2 t3
        in  ps , t5
      }
support (x ?- ez)  with supportz ez
... | de , th , ez' , q , u = de , th , (x ?- ez') , (x ?-_) $= q
  , \ { de+ th+ (essl t+) ()
      ; de+ th+ (thnk t+) ()
      ; de+ th+ (y ?- ez+) q+ -> termNoConf q+ \ { refl refl refl ->
        u de+ th+ ez+ refl } }
support (mets x)   = _ , oe , mets x , refl ,
   \ { de+ th+ (vari i) () ; de+ th+ (elim _ _) ()
     ; de+ th+ (mets x) refl -> oe , oeTri _ }

supportz [] = _ , oe , [] , refl ,
  \ { de+ th+ [] refl -> oe , oeTri _ }
supportz (ez -, e) with supportz ez | support e
... | deez , thez , ez' , qez , uez | dee , the , e' , qe , ue with coproduct thez the
... | de , phez , phe , th , t0 , t1 , u
    = de , th , (actz ez' (refl , phez) -, (e' ^ phe))
    , _-,_ $= (_ =[ qez >= _ =[ 
          actz ez' (refl , thez) =[ actzAll ez' (refl , thez) >=
          all (_^ thez) ez' =[ allCo _ _ _ (\ t -> triAct t t0) ez' >=
          all (_^ th) (all (_^ phez) ez') =< all (_^ th) $= actzAll _ (refl , phez) ]=
          all (_^ th) (actz ez' (refl , phez)) =< actzAll _ (refl , th) ]=
          actz (actz ez' (refl , phez)) (refl , th)
            [QED]
             >= _ [QED])
          =$= (_ =[ qe >= _ =[ triAct e' t1 >= _ [QED])
    , \ { de+ th+ (ez+ -, e+) refl ->
          let _ , t2 = uez de+ th+ ez+ refl
              _ , t3 = ue de+ th+ e+ refl
              ps , t4 , t5 , t6 = u t2 t3
          in  ps , t5 }


thinMonoTerm : forall {M ga de l d}(t0 t1 : Term M ga l d)(th : ga <= de) ->
  (t0 ^ th) == (t1 ^ th) ->
  t0 == t1
thinMonoTermz : forall {M ga de n}(ez0 ez1 : All (\ _ -> Term M ga lib syn) n)
  (th : ga <= de) ->
  Act.actz THIN ez0 (refl , th) == Act.actz THIN ez1 (refl , th) ->
  ez0 == ez1
thinMonoTerm (atom a) (atom .a) th refl = refl
thinMonoTerm (atom a) (cons t1 t2) th ()
thinMonoTerm (atom a) (abst t1) th ()
thinMonoTerm (cons t0 t1) (atom a) th ()
thinMonoTerm (cons t0 t1) (cons t2 t3) th q = termNoConf q \ q0 q1 ->
  cons $= thinMonoTerm t0 t2 th q0 =$= thinMonoTerm t1 t3 th q1
thinMonoTerm (cons t0 t1) (abst t2) th ()
thinMonoTerm (abst t0) (atom a) th ()
thinMonoTerm (abst t0) (cons t1 t2) th ()
thinMonoTerm (abst t0) (abst t1) th q = termNoConf q \ q' ->
  abst $= thinMonoTerm t0 t1 (th su) q'
thinMonoTerm (vari i) (vari j) th q = termNoConf q \ q' ->
  vari $= qThinMono i j th q'
thinMonoTerm (vari i) (elim t1 t2) th ()
thinMonoTerm (vari i) (mets x) th ()
thinMonoTerm (elim t0 t1) (vari i) th ()
thinMonoTerm (elim t0 t1) (elim t2 t3) th q = termNoConf q \ q0 q1 ->
  elim $= thinMonoTerm t0 t2 th q0 =$= thinMonoTerm t1 t3 th q1
thinMonoTerm (elim t0 t1) (mets x) th ()
thinMonoTerm {d = chk} (essl t0) (essl t1) th q = termNoConf q \ q' ->
  essl $= thinMonoTerm t0 t1 th q'
thinMonoTerm {d = syn} (essl t0) (essl t1) th q = termNoConf q \ q' ->
  essl $= thinMonoTerm t0 t1 th q'
thinMonoTerm (essl t0) (thnk t1) th ()
thinMonoTerm (essl t0) (t1 :: t2) th ()
thinMonoTerm (essl t0) (x ?- _) th ()
thinMonoTerm (thnk t0) (essl t1) th ()
thinMonoTerm (thnk t0) (thnk t1) th q = termNoConf q \ q' ->
  thnk $= thinMonoTerm t0 t1 th q'
thinMonoTerm (thnk t0) (x ?- _) th ()
thinMonoTerm (t0 :: t1) (essl t2) th ()
thinMonoTerm (t0 :: t1) (t2 :: t3) th q = termNoConf q \ q0 q1 ->
  _::_ $= thinMonoTerm t0 t2 th q0 =$= thinMonoTerm t1 t3 th q1
thinMonoTerm (x ?- _) (essl t1) th ()
thinMonoTerm (x ?- _) (thnk t1) th ()
thinMonoTerm (x ?- ez) (y ?- fz) th q = termNoConf q \ { refl q0 q1 ->
  _?-_ $= q0 =$= thinMonoTermz ez fz th q1 }
thinMonoTerm (mets x) (vari i) th ()
thinMonoTerm (mets x) (elim t1 t2) th ()
thinMonoTerm (mets x) (mets .x) th refl = refl
thinMonoTermz [] [] th q = refl
thinMonoTermz (ez0 -, e0) (ez1 -, e1) th q
  = _-,_ $= thinMonoTermz ez0 ez1 th (pop $= q)
        =$= thinMonoTerm e0 e1 th (top $= q)


pullbackTerm : forall {M ga0 ga1 de l d}
  (t0 : Term M ga0 l d)(th0 : ga0 <= de)(t1 : Term M ga1 l d)(th1 : ga1 <= de) ->
  (t0 ^ th0) == (t1 ^ th1) ->
  let ga , ph0 , ph1 , _ = pullback th0 th1 in
  Sg _ \ t -> t0 == (t ^ ph0) * t1 == (t ^ ph1)
pullbackTerm t0 th0 t1 th1 q
  with support (t0 ^ th0) | pullback th0 th1 | pullbackU th0 th1
... | _ , th , t , q0 , u0 | ga , ph0 , ph1 , ph , r0 , r1 | up
  with u0 _ th0 t0 refl | u0 _ th1 t1 q
... | _ , r2 | _ , r3
  with up r2 r3
... | th' , r4 , r5
    = t ^ th'
    , thinMonoTerm t0 ((t ^ th') ^ ph0) th0 (
      (t0 ^ th0) =[ q0 >=
      (t ^ th) =[ (t ^_) $= (
         th =[ triDet r2 (mkTri _ th0) >=
         (_ -< th0) =[ (_-< th0) $= triDet r4 (mkTri th' ph0) >=
         ((th' -< ph0) -< th0) [QED]) >=
      (t ^ ((th' -< ph0) -< th0)) =< thinco _ _ _ ]=
      ((t ^ (th' -< ph0)) ^ th0) =< (_^ th0) $= thinco _ _ _ ]=
      (((t ^ th') ^ ph0) ^ th0) [QED] )
    , thinMonoTerm t1 ((t ^ th') ^ ph1) th1 (
        (t1 ^ th1) =< q ]=
        (t0 ^ th0) =[ q0 >=
        (t ^ th) =[ (t ^_) $=
          (th =[ triDet r3 (mkTri _ th1) >=
           (_ -< th1) =[ (_-< th1) $= triDet r5 (mkTri th' ph1) >=
           ((th' -< ph1) -< th1) [QED]) >=
        (t ^ ((th' -< ph1) -< th1)) =< thinco _ _ _ ]=
        ((t ^ (th' -< ph1)) ^ th1) =< (_^ th1) $= thinco _ _ _ ]=
        (((t ^ th') ^ ph1) ^ th1) [QED])

pullbackFact : forall {X}{ga ga' de de' : Bwd X}(th : ga <= ga')(ph : de <= de') ->
  pullback  (th ^+ oi {S = de'}) (oi {S = ga'} ^+ ph) ==
  ((ga -+ de) , (oi {S = ga} ^+ ph) , (th ^+ oi {S = de}) , (th ^+ ph) , (oiTri th +T triOi ph) , (triOi th +T oiTri ph))
pullbackFact th (ph no) rewrite pullbackFact th ph = refl
pullbackFact th (ph su) rewrite pullbackFact th ph = refl
pullbackFact th ze = pullbackOi th


thickEnv : forall {M ga ga' de}(p : Pat de)
  (t : Term M (ga -+ de) lib chk)(th : ga <= ga')(ts' : Env M (ga' ,P p)) ->
  (p %P ts') == (t ^ (th ^+ oi {S = de})) ->
  Sg _ \ ts -> ts' == ActWeak.acte THINWEAK ts th * t == (p %P ts)
thickEnv (atom a) (! .a) th (atom .a) refl = atom a , refl , refl
thickEnv (atom a) (_ & _) th (atom .a) ()
thickEnv (atom a) (\\ t) th (atom .a) ()
thickEnv (atom a) (thnk t) th (atom .a) ()
thickEnv (atom a) (x ?- _) th (atom .a) ()
  -- atom a , refl , {!!}
thickEnv (p - q) (s & t) th (cons ss' ts') z = termNoConf z \ z -> termNoConf z \ z0 z1 ->
  let ss , sq , sq' = thickEnv p s th ss' z0 in
  let ts , tq , tq' = thickEnv q t th ts' z1 in
  cons ss ts , cons $= sq =$= tq , _&_ $= sq' =$= tq'
thickEnv (p - q) (! a) th (cons ss' ts') ()
thickEnv (p - q) (\\ t) th (cons ss' ts') ()
thickEnv (p - q) (thnk t) th (cons ss' ts') ()
thickEnv (p - q) (x ?- _) th (cons ss' ts') ()
thickEnv (\\\ q) (! a) th (abst ts') ()
thickEnv (\\\ q) (_ & _) th (abst ts') ()
thickEnv (\\\ q) (\\ t) th (abst ts') z = termNoConf z \ z -> termNoConf z \ z ->
  let ts , tq , tq' = thickEnv q t th ts' z in
  abst ts , abst $= tq , \\_ $= tq'
thickEnv (\\\ q) (thnk t) th (abst ts') ()
thickEnv (\\\ q) (x ?- _) th (abst ts') ()
thickEnv {ga = ga} {ga'} {de'} (hole {de} ph) t th (hole s) z
  with pullback  (th ^+ oi {S = de'})(oi {S = ga'} ^+ ph)
    | pullbackFact th ph
    | pullbackTerm t (th ^+ oi {S = de'}) s (oi {S = ga'} ^+ ph) (sym z)
... | ._ | refl | u , refl , refl = hole u , refl , refl

