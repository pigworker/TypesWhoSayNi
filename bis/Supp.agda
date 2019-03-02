module Supp where

open import Basics
open import Eq
open import Bwd
open import All
open import Thin
open import Pat
open import Term
open import ActCats

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
