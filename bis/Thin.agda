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

  thinEq? : forall {xz yz}(th ph : xz <= yz) -> Dec (th == ph)
  thinEq? (th no) (ph no) with thinEq? th ph
  thinEq? (th no) (ph no)  | #0 , q = #0 , \ { refl -> q refl }
  thinEq? (th no) (.th no) | #1 , refl = #1 , refl
  thinEq? (th no) (ph su) = #0 , \ ()
  thinEq? (th su) (ph no) = #0 , \ ()
  thinEq? (th su) (ph su) with thinEq? th ph
  thinEq? (th su) (ph su)  | #0 , q = #0 , \ { refl -> q refl }
  thinEq? (th su) (.th su) | #1 , refl = #1 , refl
  thinEq? ze      ze      = #1 , refl

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

  module _ where
    open Cat
    
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

  thinrLemma : forall {az bz cz dz ez}(th : az <= bz)(ph : cz <= dz)(ps : bz <= ez) ->
    (thinr cz th -< (ph ^+ ps)) == thinr dz (th -< ps)
  thinrLemma th ph (ps no) = _no $= thinrLemma th ph ps
  thinrLemma (th no) ph (ps su) = _no $= thinrLemma th ph ps
  thinrLemma (th su) ph (ps su) = _su $= thinrLemma th ph ps
  thinrLemma ze ph ze = oeU _ _

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
    Tri th' th ps' * Tri ph' ph ps' * forall {gz}
    {th_ : gz <= iz}{ph_ : gz <= jz}{ps_ : gz <= kz} ->
    Tri th_ th ps_ -> Tri ph_ ph ps_ ->
    Sg (gz <= hz) \ ps -> Tri ps th' th_ * Tri ps ph' ph_
    
  pullback (th no) (ph no) with pullback th ph
  ... | _ , _ , _ , _ , t0 , t1 , u = _ , _ , _ , _ , (t0 no) , (t1 no) ,
    \ { (t2 no) (t3 no) -> let _ , t4 , t5 = u t2 t3 in _ , t4 , t5 }
  pullback (th no) (ph su) with pullback th ph
  ... | _ , _ , _ , _ , t0 , t1 , u = _ , _ , _ , _ , (t0 no) , (t1 nosuno) ,
   \ { (t2 no) (t3 nosuno) -> let _ , t4 , t5 = u t2 t3 in _ , t4 , (t5 no) }
  pullback (th su) (ph no) with pullback th ph
  ... | _ , _ , _ , _ , t0 , t1 , u = _ , _ , _ , _ , (t0 nosuno) , (t1 no) , 
   \ { (t2 nosuno) (t3 no) -> let _ , t4 , t5 = u t2 t3 in _ , (t4 no) , t5
     ; (t2 su) () }
  pullback (th su) (ph su) with pullback th ph
  ... | _ , _ , _ , _ , t0 , t1 , u = _ , _ , _ , _ , (t0 su) , (t1 su) , 
   \ { (t2 nosuno) (t3 nosuno) -> let _ , t4 , t5 = u t2 t3 in _ , (t4 nosuno) , (t5 nosuno)
     ; (t2 su)     (t3 su)     -> let _ , t4 , t5 = u t2 t3 in _ , (t4 su) , (t5 su) }
  pullback ze ze = _ , _ , _ , _ , ze , ze , 
   \ { ze ze -> ze , ze , ze }

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
