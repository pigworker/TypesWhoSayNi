module Thin where

open import Basics
open import Eq
open import Cats
open import Bwd

module _ {X : Set} where

  data Thin (R : Bwd X -> Bwd X -> Set) : Bwd X -> Bwd X -> Set where
    _no : forall {xz yz z} -> Thin R xz yz -> Thin R  xz       (yz -, z)
    _su : forall {xz yz z} -> Thin R xz yz -> Thin R (xz -, z) (yz -, z)
    <_> : forall {xz yz} -> R xz yz -> Thin R xz yz

  data Nils : Bwd X -> Bwd X -> Set where
    ze : Nils [] []

  _<=_ = Thin Nils

  module _ where
    open Cat
    
    OPE : Cat (Bwd X) _<=_
    idC OPE {[]}      = < ze >
    idC OPE {xz -, x} = idC OPE su
    coC OPE th      (ph no) = coC OPE th ph no
    coC OPE (th no) (ph su) = coC OPE th ph no
    coC OPE (th su) (ph su) = coC OPE th ph su
    coC OPE < () >  (ph su)
    coC OPE < ze >  < ze >  = < ze >
    idcoC OPE (th no) = _no $= idcoC OPE th
    idcoC OPE (th su) = _su $= idcoC OPE th
    idcoC OPE < ze >  = refl
    coidC OPE (th no) = _no $= coidC OPE th
    coidC OPE (th su) = _su $= coidC OPE th
    coidC OPE < ze >  = refl
    cocoC OPE  th      ph     (ps no) = _no $= cocoC OPE th ph ps
    cocoC OPE  th     (ph no) (ps su) = _no $= cocoC OPE th ph ps
    cocoC OPE (th no) (ph su) (ps su) = _no $= cocoC OPE th ph ps
    cocoC OPE (th su) (ph su) (ps su) = _su $= cocoC OPE th ph ps
    cocoC OPE < () >  (ph su) (ps su)
    cocoC OPE  th     < () >  (ps su)
    cocoC OPE < ze >  < ze >  < ze >  = refl

    oi   = idC OPE
    _-<_ = coC OPE

  data Thin' (xz : Bwd X) : Bwd X -> Set
  _<='_ = Thin Thin'
  data Thin' xz where
    <_> : forall {yz} -> xz <= yz -> Thin' xz yz
    id' : Thin' xz xz
    co' : forall {yz zz} -> xz <=' yz -> yz <=' zz -> Thin' xz zz

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
