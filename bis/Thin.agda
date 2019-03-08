module Thin where

open import Basics
open import Eq
open import Cats
open import Bwd

module _ {X : Set} where

  data _<=_ : Bwd X -> Bwd X -> Set where
    _no : forall {xz yz z} -> xz <= yz ->  xz       <= (yz -, z)
    _su : forall {xz yz z} -> xz <= yz -> (xz -, z) <= (yz -, z)
    ze  : [] <= []

  _<-_ : X -> Bwd X -> Set
  x <- xz = ([] -, x) <= xz

  oe : {xz : Bwd X} -> [] <= xz
  oe {[]}      = ze
  oe {xz -, x} = oe no

  oeU : forall {xz}(th ph : [] <= xz) -> th == ph
  oeU (th no) (ph no) = _no $= oeU th ph
  oeU ze      ze      = refl

  
  _=^=_ : forall {xz yz zz : Bwd X} -> xz <= zz -> yz <= zz -> Set
  _=^=_ {xz = xz}{yz = yz} th ph = Sg (xz == yz) \ { refl -> th == ph }

  thinEq? : forall {xz yz zz : Bwd X}(th : xz <= zz)(ph : yz <= zz) ->
    Dec (th =^= ph)
  thinEq? (th no) (ph no) with thinEq? th ph
  thinEq? (th no) (ph no) | #0 , a = #0 , \ { (refl , refl) -> a (refl , refl) }
  thinEq? (th no) (.th no) | #1 , refl , refl = #1 , refl , refl
  thinEq? (th no) (ph su) = #0 , \ { (refl , ()) }
  thinEq? (th su) (ph no) = #0 , \ { (refl , ()) }
  thinEq? (th su) (ph su) with thinEq? th ph
  thinEq? (th su) (ph su) | #0 , a = #0 , \ { (refl , refl) -> a (refl , refl) }
  thinEq? (th su) (.th su) | #1 , refl , refl = #1 , refl , refl
  thinEq? ze ze = #1 , refl , refl

  _^+_ : forall {az bz cz dz}(th : az <= bz)(ph : cz <= dz) -> (az -+ cz) <= (bz -+ dz)
  th ^+ (ph no) = (th ^+ ph) no
  th ^+ (ph su) = (th ^+ ph) su
  th ^+ ze      = th

  thinl : forall {az bz}(th : az <= bz) cz -> az <= (bz -+ cz)
  thinl th cz = th ^+ oe {cz}

  thinr : forall cz {az bz}(th : az <= bz) -> az <= (cz -+ bz)
  thinr cz (th no) = thinr cz th no
  thinr cz (th su) = thinr cz th su
  thinr cz ze      = oe

  thinCatSplit : forall bz {az cz}(th : (az -+ bz) <= cz) ->
    Sg _ \ dz -> Sg _ \ ez -> Sg (az <= dz) \ th0 -> Sg (bz <= ez) \ th1 ->
    Sg (cz == (dz -+ ez)) \ { refl -> th == (th0 ^+ th1) }
  thinCatSplit [] th = _ , _ , th , ze , refl , refl
  thinCatSplit (bz -, b) (th no) with thinCatSplit (bz -, b) th
  ... | dz , ez , th0 , th1 , refl , refl = _ , _ , th0 , th1 no , refl , refl
  thinCatSplit (bz -, b) (th su) with thinCatSplit bz th
  ... | dz , ez , th0 , th1 , refl , refl = _ , _ , th0 , th1 su , refl , refl

  thinSplitCat : forall {az bz} cz (th : az <= (bz -+ cz)) ->
    Sg _ \ dz -> Sg _ \ ez -> Sg (dz <= bz) \ th0 -> Sg (ez <= cz) \ th1 ->
    th =^= (th0 ^+ th1)
  thinSplitCat [] th = _ , _ , th , ze , refl , refl
  thinSplitCat (cz -, c) (th no) with thinSplitCat cz th
  ... | _ , _ , th0 , th1 , refl , refl = _ , _ , th0 , th1 no , refl , refl
  thinSplitCat (cz -, c) (th su) with thinSplitCat cz th
  ... | _ , _ , th0 , th1 , refl , refl = _ , _ , th0 , th1 su , refl , refl

  module _ where
    open Cat
    open Monoidal
    module BWD = Cat (MonoidBwd X)
    
    OPE : Cat (Bwd X) _<=_
    idC OPE {[]}      = ze
    idC OPE {xz -, x} = idC OPE su
    coC OPE th      (ph no) = coC OPE th ph no
    coC OPE (th no) (ph su) = coC OPE th ph no
    coC OPE (th su) (ph su) = coC OPE th ph su
    coC OPE ze      ze      = ze
    idcoC OPE (th no) = _no $= idcoC OPE th
    idcoC OPE (th su) = _su $= idcoC OPE th
    idcoC OPE ze      = refl
    coidC OPE (th no) = _no $= coidC OPE th
    coidC OPE (th su) = _su $= coidC OPE th
    coidC OPE ze      = refl
    cocoC OPE  th      ph     (ps no) = _no $= cocoC OPE th ph ps
    cocoC OPE  th     (ph no) (ps su) = _no $= cocoC OPE th ph ps
    cocoC OPE (th no) (ph su) (ps su) = _no $= cocoC OPE th ph ps
    cocoC OPE (th su) (ph su) (ps su) = _su $= cocoC OPE th ph ps
    cocoC OPE ze      ze      ze      = refl

    oi   = idC OPE
    _-<_ = coC OPE

    thinQ : forall {xz yz : Bwd X} -> xz == yz -> xz <= yz
    thinQ refl = oi

    OPEMON : Monoidal (MonoidBwd X) OPE
    _><_ OPEMON = _^+_
    moid OPEMON xz [] = refl
    moid OPEMON xz (yz -, x) = _su $= moid OPEMON xz yz
    moco OPEMON th0 ph0 th1 (ph1 no) = _no $= moco OPEMON th0 ph0 th1 ph1
    moco OPEMON th0 (ph0 no) th1 (ph1 su) = _no $= moco OPEMON th0 ph0 th1 ph1
    moco OPEMON th0 (ph0 su) th1 (ph1 su) = _su $= moco OPEMON th0 ph0 th1 ph1
    moco OPEMON th0 ze th1 ze = refl
    {-
    lunitor OPEMON {S} {.(T -, _)} (_no {yz = T} f)
      with [] -+ S | [] -+ T | BWD.idcoC S | BWD.idcoC T | ze ^+ f | lunitor OPEMON f
    ... | S' | T' | refl | refl | .f | refl = refl
    lunitor OPEMON (_su {S} {T} f)
      with [] -+ S | [] -+ T | BWD.idcoC S | BWD.idcoC T | ze ^+ f | lunitor OPEMON f
    ... | S' | T' | refl | refl | .f | refl = refl
    lunitor OPEMON ze = refl
    runitor OPEMON f = refl
    associator OPEMON {S0} {S1} {S2} {T0} {T1} f0 f1 (_no {yz = T2} f2)
      with (S0 -+ S1) -+ S2 | BWD.cocoC S0 S1 S2
         | (T0 -+ T1) -+ T2 | BWD.cocoC T0 T1 T2
         | (f0 ^+ f1) ^+ f2 | associator OPEMON f0 f1 f2
    ... | ._ | refl | ._ | refl | ._ | refl = refl
    associator OPEMON {S0} {S1} {T0 = T0} {T1} f0 f1 (_su {S2} {T2} f2)
      with (S0 -+ S1) -+ S2 | BWD.cocoC S0 S1 S2
         | (T0 -+ T1) -+ T2 | BWD.cocoC T0 T1 T2
         | (f0 ^+ f1) ^+ f2 | associator OPEMON f0 f1 f2
    ... | ._ | refl | ._ | refl | ._ | refl = refl
    associator OPEMON f0 f1 ze = refl
    -}

  data Tri : forall {iz jz kz}(th : iz <= jz)(ph : jz <= kz)(ps : iz <= kz) -> Set where
    _no : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
      Tri th ph ps -> Tri {kz = _ -, k} th     (ph no) (ps no)
    _nosuno : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
      Tri th ph ps -> Tri {kz = _ -, k} (th no) (ph su) (ps no)
    _su : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
      Tri th ph ps -> Tri {kz = _ -, k} (th su) (ph su) (ps su)
    ze : Tri ze ze ze

  mkTri : forall {iz jz kz}(th : iz <= jz)(ph : jz <= kz) -> Tri th ph (th -< ph)
  mkTri th (ph no) = mkTri th ph no
  mkTri (th no) (ph su) = mkTri th ph nosuno
  mkTri (th su) (ph su) = mkTri th ph su
  mkTri ze ze = ze

  oeTri : forall {iz jz}(th : iz <= jz) -> Tri oe th oe
  oeTri (th no) = oeTri th no
  oeTri (th su) = oeTri th nosuno
  oeTri ze = ze

  oiTri : forall {iz jz}(th : iz <= jz) -> Tri oi th th
  oiTri (th no) = oiTri th no
  oiTri (th su) = oiTri th su
  oiTri ze = ze

  triOi : forall {iz jz}(th : iz <= jz) -> Tri th oi th
  triOi (th no) = triOi th nosuno
  triOi (th su) = triOi th su
  triOi ze      = ze

  triDet : forall {iz jz kz}{th : iz <= jz}{ph : jz <= kz}{ps0 ps1} ->
    Tri th ph ps0 -> Tri th ph ps1 -> ps0 == ps1
  triDet (t0 no) (t1 no) rewrite triDet t0 t1 = refl
  triDet (t0 nosuno) (t1 nosuno) rewrite triDet t0 t1 = refl
  triDet (t0 su) (t1 su) rewrite triDet t0 t1 = refl
  triDet ze ze = refl

  triMono : forall {iz jz kz}{th0 th1 : iz <= jz}{ph : jz <= kz}{ps} ->
    Tri th0 ph ps -> Tri th1 ph ps -> th0 == th1
  triMono (t0 no) (t1 no) rewrite triMono t0 t1 = refl
  triMono (t0 nosuno) (t1 nosuno) rewrite triMono t0 t1 = refl
  triMono (t0 su) (t1 su) rewrite triMono t0 t1 = refl
  triMono ze ze = refl

  thinMono : forall {hz iz jz kz}(th0 : hz <= jz)(th1 : iz <= jz)(ph : jz <= kz) ->
    (th0 -< ph) =^= (th1 -< ph) -> th0 =^= th1
  thinMono th0 th1 ph (refl , q) with mkTri th0 ph | mkTri th1 ph
  ... | t0 | t1 rewrite q = refl , triMono t0 t1

  qThinMono : forall {iz jz kz}(th0 th1 : iz <= jz)(ph : jz <= kz) ->
    (th0 -< ph) == (th1 -< ph) -> th0 == th1
  qThinMono th0 th1 ph q with thinMono th0 th1 ph (refl , q)
  ... | refl , q' = q'

  thinrLemma : forall {az bz cz dz ez}(th : az <= bz)(ph : cz <= dz)(ps : bz <= ez) ->
    (thinr cz th -< (ph ^+ ps)) == thinr dz (th -< ps)
  thinrLemma th ph (ps no) = _no $= thinrLemma th ph ps
  thinrLemma (th no) ph (ps su) = _no $= thinrLemma th ph ps
  thinrLemma (th su) ph (ps su) = _su $= thinrLemma th ph ps
  thinrLemma ze ph ze = oeU _ _

  thinrAmmel : forall {az bz cz dz}
    (th : az <= bz)(ph : bz <= cz) -> (th -< thinr dz ph) == thinr dz (th -< ph)
  thinrAmmel th (ph no) = _no $= thinrAmmel th ph
  thinrAmmel (th no) (ph su) = _no $= thinrAmmel th ph
  thinrAmmel (th su) (ph su) = _su $= thinrAmmel th ph
  thinrAmmel ze ze = oeU _ _

  _~su : forall {iz jz kz l}{th : iz <= kz}{ph : jz <= kz} ->
    th =^= ph -> _=^=_ {_ -, l} (th su) (ph su)
  (refl , q) ~su = refl , (_su $= q)

  _~no : forall {iz jz kz l}{th : iz <= kz}{ph : jz <= kz} ->
    th =^= ph -> _=^=_ {_}{_}{_ -, l} (th no) (ph no)
  (refl , q) ~no = refl , (_no $= q)

  thinrGrouse : forall {iz jz kz}(th : [] <= iz)(ph : jz <= kz) ->
    (th ^+ ph) =^= thinr iz ph
  thinrGrouse th (ph no) = thinrGrouse th ph ~no
  thinrGrouse {iz}{jz}{kz} th (ph su) = thinrGrouse th ph ~su
  thinrGrouse th ze = refl , oeU _ _

  _+T_ : forall
    {iz jz kz}{th0 : iz <= jz}{th1 : jz <= kz}{th2 : iz <= kz}(t : Tri th0 th1 th2)
    {xz yz zz}{ph0 : xz <= yz}{ph1 : yz <= zz}{ph2 : xz <= zz}(t' : Tri ph0 ph1 ph2)
    ->
    Tri (th0 ^+ ph0) (th1 ^+ ph1) (th2 ^+ ph2)
  t +T (t' no)     = (t +T t') no
  t +T (t' nosuno) = (t +T t') nosuno
  t +T (t' su)     = (t +T t') su
  t +T ze          = t

  fromCat : forall {z} xz yz (i : z <- (xz -+ yz)) ->
      (Sg (z <- xz) \ j -> Tri j (thinl oi yz) i)
    + (Sg (z <- yz) \ j -> Tri j (thinr xz oi) i)
  fromCat xz yz i with thinSplitCat yz i
  fromCat xz yz .(th0 ^+ th1) | .([] -, _) , [] , th0 , th1 , refl , refl
    with triOi th0 +T oeTri th1
  ... | t rewrite oeU th1 oe = #0 , th0 , t
  fromCat xz yz .(th0 ^+ th1) | .[] , [] -, y , th0 , th1 , refl , refl
    with oeU th0 oe | oeTri th0 +T triOi th1
  fromCat xz yz .(oe ^+ th1) | .[] , [] -, y , .oe , th1 , refl , refl | refl | t
    with [] -+ yz
       | BWD.idcoC yz
       | ze ^+ th1
       | oe {xz = xz} ^+ oi {S = yz}
       | thinrGrouse (oe {xz = xz}) (oi {S = yz})
       | oe {xz = xz} ^+ th1
  fromCat xz yz .(oe ^+ th1) | .[] , [] -, y , .oe , th1 , refl , refl
    | refl | t | .yz | refl | ph0 | .(thinr xz (Cat.idC OPE))
    | refl , refl | ph2
    = #1 , ph0 , t
  fromCat xz yz i | de , ez -, _ -, _ , th0 , th1 , () , r

{-
  moco : forall {az bz cz dz ez fz}
           (th0 : az <= bz)(ph0 : bz <= cz)
           (th1 : dz <= ez)(ph1 : ez <= fz) ->
         ((th0 ^+ th1) -< (ph0 ^+ ph1)) == ((th0 -< ph0) ^+ (th1 -< ph1))
  moco th0 ph0 th1 (ph1 no) = _no $= moco th0 ph0 th1 ph1
  moco th0 ph0 (th1 no) (ph1 su) = _no $= moco th0 ph0 th1 ph1
  moco th0 ph0 (th1 su) (ph1 su) = _su $= moco th0 ph0 th1 ph1
  moco th0 ph0 ze ze = refl

  thinlLeft : forall {az bz cz}
    (th : az <= bz)(ph : bz <= cz) dz ->
    (th -< thinl ph dz) == thinl (th -< ph) dz
  thinlLeft th ph dz = 
    (th -< thinl ph dz)
      =[ moco th ph ze (oe {xz = dz}) >=
    ((th -< ph) ^+ (ze -< oe {xz = dz}))
      =[ ((th -< ph) ^+_) $= oeU _ _ >=
    thinl (th -< ph) dz
      [QED]
-}


  Thick : forall {iz jz kz}(th : iz <= kz)(ph : jz <= kz) -> Set
  Thick th ph = Sg _ \ ps -> ph == (ps -< th)
  thick? : forall {iz jz kz}(th : iz <= kz)(ph : jz <= kz) -> Dec (Thick th ph)
  thick? (th no) (ph no) with thick? th ph
  thick? (th no) (ph no) | #0 , bad = #0 , \ { (_ , refl) -> bad (_ , refl) }
  thick? (th no) (.(ps -< th) no) | #1 , (ps , refl) = #1 , (ps , refl)
  thick? (th no) (ph su) = #0 , \ { (_ , ()) }
  thick? (th su) (ph no) with thick? th ph
  thick? (th su) (ph no) | #0 , bad = #0 ,
    \ { ((ps no) , refl) -> bad (ps , refl) ; ((ps su) , ()) }
  thick? (th su) (.(ps -< th) no) | #1 , (ps , refl) = #1 , ((ps no) , refl)
  thick? (th su) (ph su) with thick? th ph
  thick? (th su) (ph su) | #0 , bad = #0 ,
    \ { ((ps no) , ()) ; ((ps su) , refl) -> bad (ps , refl) }
  thick? (th su) (.(ps -< th) su) | #1 , (ps , refl) = #1 , ((ps su) , refl)
  thick? ze ze = #1 , (ze , refl)

  pullback : forall {iz jz kz}(th : iz <= kz)(ph : jz <= kz) ->
    Sg _ \ hz ->
    Sg (hz <= iz) \ th' -> Sg (hz <= jz) \ ph' -> Sg (hz <= kz) \ ps' ->
    Tri th' th ps' * Tri ph' ph ps'
    
  pullback (th no) (ph no) with pullback th ph
  ... | _ , _ , _ , _ , t0 , t1 = _ , _ , _ , _ , (t0 no) , (t1 no)
  pullback (th no) (ph su) with pullback th ph
  ... | _ , _ , _ , _ , t0 , t1 = _ , _ , _ , _ , (t0 no) , (t1 nosuno)
  pullback (th su) (ph no) with pullback th ph
  ... | _ , _ , _ , _ , t0 , t1 = _ , _ , _ , _ , (t0 nosuno) , (t1 no)
  pullback (th su) (ph su) with pullback th ph
  ... | _ , _ , _ , _ , t0 , t1 = _ , _ , _ , _ , (t0 su) , (t1 su)
  pullback ze ze = _ , _ , _ , _ , ze , ze

  pullbackU : forall {iz jz kz}(th : iz <= kz)(ph : jz <= kz) ->
              let hz , th' , ph' , ps' , t0 , t1 = pullback th ph in
              forall {gz} {th_ : gz <= iz}{ph_ : gz <= jz}{ps_ : gz <= kz} ->
              Tri th_ th ps_ -> Tri ph_ ph ps_ ->
              Sg (gz <= hz) \ ps -> Tri ps th' th_ * Tri ps ph' ph_
  pullbackU (th no) (ph no) (t2 no) (t3 no) =
    let _ , t4 , t5 = pullbackU th ph t2 t3 in _ , t4 , t5
  pullbackU (th no) (ph su) (t2 no) (t3 nosuno) =
    let _ , t4 , t5 = pullbackU th ph t2 t3 in _ , t4 , t5 no
  pullbackU (th su) (ph no) (t2 nosuno) (t3 no) =
    let _ , t4 , t5 = pullbackU th ph t2 t3 in _ , t4 no , t5
  pullbackU (th su) (ph no) (t2 su) ()
  pullbackU (th su) (ph su) (t2 nosuno) (t3 nosuno) =
    let _ , t4 , t5 = pullbackU th ph t2 t3 in  _ , t4 nosuno , t5 nosuno
  pullbackU (th su) (ph su) (t2 su) (t3 su) =
    let _ , t4 , t5 = pullbackU th ph t2 t3 in  _ , t4 su , t5 su
  pullbackU ze ze ze ze = ze , ze , ze

  pullbackEq : forall {iz jz}(th : iz <= jz) ->
    pullback th th == (iz , oi , oi , th , oiTri th , oiTri th)
  pullbackEq (th no) rewrite pullbackEq th = refl
  pullbackEq (th su) rewrite pullbackEq th = refl
  pullbackEq ze = refl

  pullbackOi : forall {iz jz}(th : iz <= jz) ->
    pullback th oi == (iz , oi , th , th , oiTri th , triOi th)
  pullbackOi (th no) rewrite pullbackOi th = refl
  pullbackOi (th su) rewrite pullbackOi th = refl
  pullbackOi ze = refl

  pullbackOe : forall {iz jz}(th : iz <= jz) ->
    pullback th oe == ([] , oe , oe , oe , oeTri th , oeTri oe)
  pullbackOe (th no) rewrite pullbackOe th = refl
  pullbackOe (th su) rewrite pullbackOe th = refl
  pullbackOe ze = refl

  coproduct : forall {iz jz kz}(th : iz <= kz)(ph : jz <= kz) ->
    Sg _ \ hz ->
    Sg (iz <= hz) \ th' -> Sg (jz <= hz) \ ph' -> Sg (hz <= kz) \ ps' ->
    Tri th' ps' th * Tri ph' ps' ph * forall {gz}
    {th_ : iz <= gz}{ph_ : jz <= gz}{ps_ : gz <= kz} ->
    Tri th_ ps_ th -> Tri ph_ ps_ ph ->
    Sg (hz <= gz) \ ps -> Tri th' ps th_ * Tri ps ps_ ps' * Tri ph' ps ph_
  coproduct (th no) (ph no) with coproduct th ph
  ... | _ , _ , _ , _ , t0 , t1 , u = _ , _ , _ , _ , t0 no , t1 no ,
    \ { (t2 no) (t3 no)         ->
        let _ , t4 , t5 , t6 = u t2 t3 in _ , t4 , t5 no , t6
      ; (t2 nosuno) (t3 nosuno) ->
        let _ , t4 , t5 , t6 = u t2 t3 in _ , t4 no , t5 nosuno , t6 no }
  coproduct (th no) (ph su) with coproduct th ph
  ... | _ , _ , _ , _ , t0 , t1 , u = _ , _ , _ , _ , t0 nosuno , t1 su , 
    \ { (t2 no) () ; (t2 nosuno) (t3 su) ->
        let _ , t4 , t5 , t6 = u t2 t3 in _ , t4 nosuno , t5 su , t6 su }
  coproduct (th su) (ph no) with coproduct th ph
  ... | _ , _ , _ , _ , t0 , t1 , u = _ , _ , _ , _ , t0 su , t1 nosuno , 
    \ { (t2 su) (t3 nosuno) -> let _ , t4 , t5 , t6 = u t2 t3 in _ , t4 su , t5 su , t6 nosuno }
  coproduct (th su) (ph su) with coproduct th ph
  ... | _ , _ , _ , _ , t0 , t1 , u = _ , _ , _ , _ , t0 su , t1 su , 
    \ { (t2 su) (t3 su) -> let _ , t4 , t5 , t6 = u t2 t3 in _ , t4 su , t5 su , t6 su }
  coproduct ze ze = _ , _ , _ , _ , ze , ze , \ { ze ze -> _ , ze , ze , ze }

  tscviapb : forall {iz jz} kz (th : iz <= (jz -+ kz)) ->
    let ijz , th0 , th1 , th2 , t0 , t1 = pullback th (thinl (oi {S = jz}) kz)
        ikz , ph0 , ph1 , ph2 , t2 , t3 = pullback th (thinr jz (oi {S = kz}))
    in  th =^= (th1 ^+ ph1)
  tscviapb {iz} {jz} [] th rewrite pullbackOi th | pullbackOe th = refl , refl
  tscviapb {iz} {jz} (kz -, x) (th no) = tscviapb kz th ~no
  tscviapb {.(_ -, x)} {jz} (kz -, x) (th su) = tscviapb kz th ~su
{-
  with pullback th (thinl (oi {S = jz}) kz)
                    | pullback th (thinr jz (oi {S = kz}))
  ... | ijz , th0 , th1 , th2 , t0 , t1 | ikz , ph0 , ph1 , ph2 , t2 , t3
    = {!!}
-}

join^ : forall {X}{xzz xzz' : Bwd (Bwd X)} -> BwdR _<=_ xzz xzz' ->
  join xzz <= join xzz'
join^ [] = ze
join^ (thz -, th) = join^ thz ^+ th

bind^ : forall {X Y}(k : X -> Bwd Y){yz yzz xz} ->
  BwdR (\ x yz -> yz <= k x) xz yzz ->
  yz == join yzz ->
  yz <= (xz >>= k)
bind^ k [] refl = ze
bind^ k (thz -, th) refl = bind^ k thz refl ^+ th

data InBind {X Y}(xz : Bwd X)(k : X -> Bwd Y)
    yz : yz <= (xz >>= k) -> Set where
  isInBind : forall yzz (thz : BwdR (\ x yz -> yz <= k x) xz yzz) ->
    (q : yz == join yzz) ->
    InBind xz k yz (bind^ k thz q)

bwdRThin : forall {X Y}{R : X -> Y -> Set}{xz' yz yz'} ->
  BwdR R xz' yz' -> yz <= yz' ->
  Sg _ \ xz -> xz <= xz' * BwdR R xz yz
bwdRThin (rz -, r) (ph no) with bwdRThin rz ph
... | _ , th , sz = _ , th no , sz
bwdRThin (rz -, r) (ph su) with bwdRThin rz ph
... | _ , th , sz = _ , th su , sz -, r
bwdRThin [] ze = _ , ze , []

inBind : forall {X Y}(xz : Bwd X)(k : X -> Bwd Y){yz}(th : yz <= (xz >>= k)) ->
  InBind xz k yz th
inBind [] k ze = isInBind _ [] refl
inBind (xz -, x) k th with thinSplitCat (k x) th
inBind (xz -, x) k .(th0 ^+ th1) | _ , _ , th0 , th1 , refl , refl with inBind xz k th0
inBind (xz -, x) k .(bind^ k thz refl ^+ th1) | _ , _ , .(bind^ k thz refl) , th1 , refl , refl
  | isInBind yzz thz refl = isInBind _ (thz -, th1) refl

bwdThin : forall {X Y}(f : X -> Y)(xz' : Bwd X){yz}(th : yz <= bwd f xz') ->
  Sg _ \ xz -> (xz <= xz') * (yz == bwd f xz)
bwdThin f [] ze = [] , ze , refl
bwdThin f (xz' -, x) (th no) with bwdThin f xz' th
... | xz , ph , q = xz , ph no , q
bwdThin f (xz' -, x) (th su) with bwdThin f xz' th
... | xz , ph , q = xz -, x , ph su , (_-, _) $= q

Longer : forall {X} -> Bwd X -> Bwd X -> Set
Longer [] yz = Zero
Longer (xz -, _) [] = One
Longer (xz -, _) (yz -, _) = Longer xz yz

evenLonger : forall {X} xz yz {z : X} -> Longer xz (yz -, z) -> Longer xz yz
evenLonger [] yz ()
evenLonger (xz -, x) [] l = <>
evenLonger (xz -, _) (yz -, _) l = evenLonger xz yz l

busted : forall {X}{xz yz : Bwd X}(th : xz <= yz){bad : Longer xz yz} -> Zero
busted {xz = xz}{yz = yz -, _} (th no) {bad} = busted th {evenLonger xz yz bad}
busted (th su) {bad} = busted th {bad}
busted ze {()}

narrowing : forall {X Y}{xz xz' : Bwd X}(th : xz <= xz')(k : X -> Bwd Y) ->
  (xz >>= k) <= (xz' >>= k)
narrowing {xz' = _ -, x} (th no) k = narrowing th k ^+ oe {xz = k x}
narrowing {xz' = _ -, x} (th su) k = narrowing th k ^+ oi {S = k x}
narrowing ze k = ze



{-
provenance : forall {X Y}(xz : Bwd X)(k : X -> Bwd Y){y}(i : y <- (xz >>= k)) ->
  Sg X \ x -> (x <- xz) *
  Sg (y <- k x) \ j -> Sg (k x <= (xz >>= k)) \ th -> Tri j th i
provenance [] k ()
provenance (xz -, x) k i with fromCat (xz >>= k) (k x) i
provenance (xz -, x) k i | #0 , i' = {!!}
provenance (xz -, x) k i | #1 , i' = _ , oe su , i' , thinr (xz >>= k) oi , {!!}
-}

{-
provenance [] k ()
provenance (xz -, x) k i with fromCat (xz >>= k) (k x) i
provenance (xz -, x) k i | #0 , i' with provenance xz k i'
... | x' , l , j = x' , l no , j
provenance (xz -, x) k i | #1 , j = _ , oe su , j
-}

{-
  data Thin' (xz : Bwd X) : Bwd X -> Set
  _<='_ = Thin Thin'
  data Thin' xz where
    <_> : forall {yz} -> xz <= yz -> Thin' xz yz
    id' : Thin' xz xz
    co' : forall {yz zz} -> xz <=' yz -> yz <=' zz -> Thin' xz zz
-}
{-
  module THINSTUFF where
    open Cat OPE

    eval : forall {xz yz} -> xz <=' yz -> xz <= yz
    eval (th no)       = eval th no
    eval (th su)       = eval th su
    eval < < th > >    = th
    eval < id' >       = oi
    eval < co' th ph > = eval th -< eval ph

    _su^ : forall {xz yz z} -> xz <=' yz -> (xz -, z) <=' (yz -, z)
    < id' > su^ = < id' >
    th      su^ = th su

    suLemma : forall {xz yz z}(th : xz <=' yz) ->
      eval th su == eval {_ -, z} (th su^)
    suLemma < id' >     = refl
    suLemma < co' _ _ > = refl
    suLemma < < _ > >   = refl
    suLemma (_ no)      = refl
    suLemma (_ su)      = refl

    _-<^_ : forall {xz yz zz} -> xz <=' yz -> yz <=' zz -> xz <=' zz
    th      -<^  (ph no) = (th -<^ ph) no
    (th no) -<^  (ph su) = (th -<^ ph) no
    (th su) -<^  (ph su) = (th -<^ ph) su^
    th      -<^  < id' > = th
    th -<^ < co' ph ps > = (th -<^ ph) -<^ ps
    < id' > -<^       ph = ph
    th      -<^       ph = < co' th ph >

    lemma : forall {xz yz zz}(th : xz <=' yz)(ph : yz <=' zz) ->
      eval th -< eval ph == eval (th -<^ ph)
    -- sometimes we get some action
    lemma th          (ph no) = _no $= lemma th ph
    lemma (th no)     (ph su) = _no $= lemma th ph
    lemma (th su)     (ph su) = 
      ((eval th -< eval ph) su)   =[ _su $= lemma th ph >=
      (eval (th -<^ ph) su)      =[ suLemma (th -<^ ph) >=
      eval ((th -<^ ph) su^)                         [QED]
    lemma < id' >     (ph su) = idcoC _
    lemma < id' >  < < ph > > = idcoC _
    lemma th          < id' > = coidC _
    lemma th    < co' ph ps > = 
      (eval th -< (eval ph -< eval ps))           =[ cocoC _ _ (eval ps) >=
      ((eval th -< eval ph) -< eval ps)  =[ (_-< eval ps) $= lemma th ph >=
      (eval (th -<^ ph) -< eval ps)              =[ lemma (th -<^ ph) ps >=
      eval ((th -<^ ph) -<^ ps)                                       [QED]
    -- sometimes we don't
    lemma < < _ > >      (ph su) = refl
    lemma < co' _ _ >    (ph su) = refl
    lemma (_ no)      < < ph > > = refl
    lemma (_ su)      < < ph > > = refl
    lemma < < _ > >   < < ph > > = refl
    lemma < co' _ _ > < < ph > > = refl

    norm : forall {xz yz} -> xz <=' yz -> xz <=' yz
    norm (th no)        = norm th no
    norm (th su)        = norm th su^
    norm < co' th ph >  = norm th -<^ norm ph
    norm th             = th

    nova : forall {xz yz}(th : xz <=' yz) -> eval th == eval (norm th)
    nova (th no) = _no $= nova th
    nova (th su) = (eval th su)            =[ _su $= nova th >=
                   (eval (norm th) su)  =[ suLemma (norm th) >=
                   eval (norm th su^)                     [QED]
    nova < < th > >    = refl
    nova < id' >       = refl
    nova < co' th ph > =
      (eval th -< eval ph)               =[ rf _-<_ =$= nova th =$= nova ph >=
      (eval (norm th) -< eval (norm ph))       =[ lemma (norm th) (norm ph) >=
      eval (norm th -<^ norm ph)                                         [QED]

  THIN' : forall {xz yz} -> Reflector (xz <=' yz) (xz <= yz)
  THIN' = record { eval = eval ; norm = norm ; nova = nova }
    where open THINSTUFF
-}

