module Thin where

open import Basics
open import Bwd
open import SmolCat

module _ {X : Set} where

  infixl 30 _-^_
  infix 15 _<=_
  data _<=_ : Bwd X -> Bwd X -> Set where
    _-^_ : forall {xz yz} -> xz <= yz -> forall y ->
           xz <= yz -, y
    _-,_ : forall {xz yz} -> xz <= yz -> forall x ->
           xz -, x <= yz -, x
    []   : [] <= []

  io : forall {xz} -> xz <= xz
  io {[]} = []
  io {_ -, x} = io -, x

  no : forall {xz} -> [] <= xz
  no {[]} = []
  no {_ -, x} = no -^ x

  infix 15 [_&_]~_
  infixl 30 _-^,_
  data [_&_]~_ : forall {xz yz zz} -> xz <= yz -> yz <= zz -> xz <= zz -> Set where
    _-^_  : forall {xz yz zz}{th : xz <= yz}{ph : yz <= zz}{ps : xz <= zz}
         -> [ th & ph ]~ ps -> forall z
         -> [ th & ph -^ z ]~ ps -^ z
    _-^,_ : forall {xz yz zz}{th : xz <= yz}{ph : yz <= zz}{ps : xz <= zz}
         -> [ th & ph ]~ ps -> forall y
         -> [ th -^ y & ph -, y ]~ ps -^ y
    _-,_  : forall {xz yz zz}{th : xz <= yz}{ph : yz <= zz}{ps : xz <= zz}
         -> [ th & ph ]~ ps -> forall x
         -> [ th -, x & ph -, x ]~ ps -, x
    []    : [ [] & [] ]~ []

module _ (X : Set) where
  open SmolCat.SmolCat

  THIN : SmolCat
  Obj THIN = Bwd X
  _=>_ THIN = _<=_
  iden THIN = io
  [_-_]~_ THIN = [_&_]~_
  compU THIN th         (ph -^ y) .fst = let _ , ps = compU THIN th ph .fst in _ , ps -^ y
  compU THIN (th -^ .x) (ph -, x) .fst = let _ , ps = compU THIN th ph .fst in _ , ps -^, x
  compU THIN (th -, .x) (ph -, x) .fst = let _ , ps = compU THIN th ph .fst in _ , ps -, x
  compU THIN [] [] .fst = _ , []
  compU THIN _ _ .snd (_ , v -^ z) (_ , w -^ .z)
    with r~ <- compU THIN _ _ .snd (_ , v) (_ , w) = r~
  compU THIN _ _ .snd (_ , v -^, y) (_ , w -^, .y)
    with r~ <- compU THIN _ _ .snd (_ , v) (_ , w) = r~
  compU THIN _ _ .snd (_ , (v -, x)) (_ , (w -, .x))
    with r~ <- compU THIN _ _ .snd (_ , v) (_ , w) = r~
  compU THIN _ _ .snd (_ , []) (_ , []) = r~
  absl THIN (f -^ y) = absl THIN f -^ y
  absl THIN (f -, x) = absl THIN f -, x
  absl THIN [] = []
  absr THIN (f -^ y) = absr THIN f -^, y
  absr THIN (f -, x) = absr THIN f -, x
  absr THIN [] = []
  asso03 THIN (_ , v , w -^ z)
    with _ , a , b <- asso03 THIN (_ , v , w) = _ , a -^ z , b -^ z
  asso03 THIN (_ , v -^ .y , w -^, y)
    with _ , a , b <- asso03 THIN (_ , v , w) = _ , a -^ y , b -^, y
  asso03 THIN (_ , v -^, .x , w -, x)
    with _ , a , b <- asso03 THIN (_ , v , w) = _ , a -^, x , b -^, x
  asso03 THIN (_ , v -, .x , w -, x)
    with _ , a , b <- asso03 THIN (_ , v , w) = _ , a -, x , b -, x
  asso03 THIN (_ , [] , []) = _ , [] , []

module _ {X : Set} where
  open SmolCat.SmolCat (THIN X)

  infixl 30 _&_
  _&_ : forall {xz yz zz}(th : xz <= yz)(ph : yz <= zz) -> xz <= zz
  th & ph = fst (comp th ph)
  
  triQ : forall {xz yz zz}{th : xz <= yz}{ph : yz <= zz}{ps : xz <= zz}
      -> [ th & ph ]~ ps
      -> (th & ph) ~ ps
  triQ v with r~ <- compQ (_ , v) (comp _ _) = r~

  noBig : forall {xz x} -> xz -, x <= xz -> Zero
  noBig (th -^ y) = noBig ((io -^ y -, _) & th)
  noBig (th -, x) = noBig th

  ioU : forall {xz}(th ph : xz <= xz) -> th ~ ph
  ioU (th -^ y) ph with () <- noBig th
  ioU (th -, x) (ph -^ .x) with () <- noBig ph
  ioU (th -, x) (ph -, .x) with r~ <- ioU th ph = r~
  ioU [] [] = r~

  noU : forall {xz : Bwd X}(th ph : [] <= xz) -> th ~ ph
  noU (th -^ y) (ph -^ .y) with r~ <- noU th ph = r~
  noU [] [] = r~

  asyL : forall {xz yz : Bwd X}{th : xz <= yz}{ph : yz <= xz}
     -> [ th & ph ]~ io
     -> (xz ~ yz) >< \ { r~ -> (th ~ io) * (ph ~ io) }
  asyL (v -, x) with r~ , r~ , r~ <- asyL v = r~ , r~ , r~
  asyL [] = r~ , r~ , r~

  asy : forall {xz yz : Bwd X}(th : xz <= yz)(ph : yz <= xz)
     -> (xz ~ yz) >< \ { r~ -> (th ~ io) * (ph ~ io) }
  asy th ph
    with (ps , v) <- comp th ph
       | r~ <- ioU ps io
       | r~ , r~ , r~ <- asyL v
       = r~ , r~ , r~

  no& : forall {xz yz : Bwd X}(th : xz <= yz) -> [ no & th ]~ no
  no& (th -^ y) = no& th -^ y
  no& (th -, x) = no& th -^, x
  no& [] = []

  infix 15 _/u\_
  infixr 20 _-,^_
  data _/u\_ : forall {xz yz zz : Bwd X} -> xz <= zz -> yz <= zz -> Set where
    _-^,_ : forall {xz yz zz}{th : xz <= zz}{ph : yz <= zz}
         -> th /u\ ph -> forall y
         -> th -^ y /u\ ph -, y
    _-,^_ : forall {xz yz zz}{th : xz <= zz}{ph : yz <= zz}
         -> th /u\ ph -> forall x
         -> th -, x /u\ ph -^ x
    _-,_  : forall {xz yz zz}{th : xz <= zz}{ph : yz <= zz}
         -> th /u\ ph -> forall z
         -> th -, z /u\ ph -, z
    []    : [] /u\ []

  covQ : forall {xz yz zz}{th : xz <= zz}{ph : yz <= zz}
      -> (a b : th /u\ ph) -> a ~ b
  covQ (a -^, y) (b -^, .y) rewrite covQ a b = r~
  covQ (a -,^ x) (b -,^ .x) rewrite covQ a b = r~
  covQ (a -, z)  (b -, .z) rewrite covQ a b = r~
  covQ [] [] = r~

  lll : forall {xz} -> io{X}{xz} /u\ no
  lll {  []  } = []
  lll {_ -, x} = lll -,^ x

  rrr : forall {xz} -> no /u\ io{X}{xz}
  rrr {  []  } = []
  rrr {_ -, x} = rrr -^, x

  isRRR : forall {xz yz}{th : [] <= yz}{ph : xz <= yz} -> th /u\ ph
       -> xz ~ yz
  isRRR (u -^, y) with r~ <- isRRR u = r~
  isRRR [] = r~

  isRRRdammit : forall {xz yz}{th : [] <= yz}{ph : xz <= yz}(u : th /u\ ph)
       -> (xz ~ yz) >< \ { r~ -> (th ~ no) >< \ { r~ -> (ph ~ io) >< \ { r~ ->
          u ~ rrr } } }
  isRRRdammit (u -^, y) with r~ , r~ , r~ , r~ <- isRRRdammit u = r~ , r~ , r~ , r~
  isRRRdammit [] = r~ , r~ , r~ , r~


  module _ {xz yz zz : Bwd X}{th : xz <= zz}{ph : yz <= zz}(u : th /u\ ph) where
    luth = th
    ruth = ph

  infix 15 _/|_|\_
  record Cop {uz : Bwd X}(l r : < _<= uz >) : Set where
    constructor _/|_|\_
    share = uz
    subcl = snd l
    subcr = snd r
    field
      {union} : Bwd X
      {injcl} : fst l <= union
      {slack} : union <= share
      {injcr} : fst r <= union
      tricl   : [ injcl & slack ]~ subcl
      cover   : injcl /u\ injcr
      tricr   : [ injcr & slack ]~ subcr
    unionOb : < _<= uz >
    unionOb = union , slack
  open Cop public

  cop : forall {uz}(l r : < _<= uz >) -> Cop l r
  cop (! th -^ y) (! ph -^ .y) =
    let v /| u |\ w = cop (! th) (! ph) in v -^ y  /| u       |\ w -^ y
  cop (! th -^ y) (! ph -, .y) =
    let v /| u |\ w = cop (! th) (! ph) in v -^, y /| u -^, y |\ w -, y
  cop (! th -, x) (! ph -^ .x) =
    let v /| u |\ w = cop (! th) (! ph) in v -, x  /| u -,^ x |\ w -^, x
  cop (! th -, x) (! ph -, .x) =
    let v /| u |\ w = cop (! th) (! ph) in v -, x  /| u -, x  |\ w -, x
  cop (! []) (! []) = [] /| [] |\ []

{-
  copU : forall {xz yz}{c@(zz , th , ph) : < xz <=_ *: yz <=_ >}
    -> {(uz0 , th0 , ps0 , ph0) : < xz <=_ *: _<= zz *: yz <=_ >}
    -> [ th0 & ps0 ]~ th -> [ ph0 & ps0 ]~ ph
    -> (C : Cop c)
    -> < [ injcl C &_]~ th0 *: [_& ps0 ]~ slack C *: [ injcr C &_]~ ph0 >
  copU _ _ (v -^, _ /| () |\ w -^, _)
  copU (s -^ z) (t -^ .z) (v -^ .z /| u |\ w -^ .z) =
    let _ , a , b , c = copU s t (v /| u |\ w) in _ , a , b -^ z , c
  copU (s -^, y) (t -^, .y) (v -^ .y /| u |\ w -^ .y) =
    let _ , a , b , c = copU s t (v /| u |\ w) in _ , a -^ y , (b -^, y) , c -^ y
  copU (s -^, y) (t -, .y) (v -^, .y /| u -^, .y |\ (w -, .y)) =
    let _ , a , b , c = copU s t (v /| u |\ w) in _ , a -^, y , b -, y , c -, y
  copU (s -, x) (t -^, .x) (v -, .x /| u -,^ .x |\ w -^, .x) =
    let _ , a , b , c = copU s t (v /| u |\ w) in _ , a -, x , b -, x , c -^, x
  copU (s -, x) (t -, .x) (v -, .x /| u -, .x |\ w -, .x) =
    let _ , a , b , c = copU s t (v /| u |\ w) in _ , a -, x , b -, x , c -, x
  copU [] [] ([] /| [] |\ []) = _ , [] , [] , []

  CopQ : forall {xz yz}{c : < xz <=_ *: yz <=_ >}
         (a b : Cop c) -> a ~ b
  CopQ Cl@(vl /| ul |\ wl) Cr@(vr /| ur |\ wr)
    with ch , a , b , c <- copU vr wr Cl
       | om , d , e , f <- copU vl wl Cr
       | r~ , r~ , r~ <- asy ch om
       | r~ , r~ , r~ <-
         compQ (_ , a) (_ , absr _) , compQ (_ , b) (_ , absl _) , compQ (_ , c) (_ , absr _)
       | r~ , r~ , r~ <- compQ (_ , vl) (_ , vr) , covQ ul ur , compQ (_ , wl) (_ , wr)
    = r~

  -- associativity of disjunction in a heavy disguise
  copGluR : forall {ga}
    {(_ , th0) (_ , th1) (_ , th2) : < _<= ga >}
    (a : Cop (ga , th0 , th1))(b : Cop (ga , th1 , th2))
    -> slack a /u\ th2
    -> th0 /u\ slack b
  copGluR a@(av /| au |\ aw) b@(bv /| bu |\ bw) u
    with c@(cv /| cu |\ cw) <- cop (_ , subcl a , slack b)
       | (_ , dv , dw) , (_ , ev , ew) <- asso02 (_ , bv , cw) , asso02 (_ , bw , cw)
       | _ , _ , f , _ <- copU cv dw a
       | _ , _ , g , _ <- copU f ew (absr _ /| u |\ absr _)
       | r~ , r~ , r~ <- asyL g
       | r~ , r~ <- compQ (_ , cv) (_ , absr _) , compQ (_ , cw) (_ , absr _)
    = cu
    
  covSwap : forall {xz yz zz}{th : yz <= zz}{ph : xz <= zz}
         -> th /u\ ph -> ph /u\ th
  covSwap (u -^, y) = covSwap u -,^ y
  covSwap (u -,^ x) = covSwap u -^, x
  covSwap (u -, z) = covSwap u -, z
  covSwap [] = []

  copSwap : forall {xz yz zz}{th : yz <= zz}{ph : xz <= zz}
        -> Cop (_ , th , ph) -> Cop (_ , ph , th)
  copSwap (v /| u |\ w) = w /| covSwap u |\ v

  copDis : forall {ga}
    {(_ , th0) (_ , th1) (_ , th) : < _<= ga >}
    (a : Cop (ga , th0 , th))(b : Cop (ga , th1 , th))(c : Cop (ga , th0 , th1))
    -> slack c /u\ th
    -> slack a /u\ slack b
  copDis a@(av /| au |\ aw) b@(bv /| bu |\ bw) c@(cv /| cu |\ cw) u
    with dv /| du |\ dw <- cop (_ , slack a , slack b)
       | (_ , _ , ae) , (_ , _ , be) , (_ , _ , ce)
         <- asso02 (_ , av , dv) , asso02 (_ , bv , dw) , asso02 (_ , bw , dw)
       | _ , _ , e , _ <- copU ae be c
       | _ , _ , f , _ <- copU e ce (absr _ /| u |\ absr _)
       | r~ , r~ , r~ <- asyL f
       | r~ , r~ <- compQ (_ , dv) (_ , absr _) , compQ (_ , dw) (_ , absr _)
       = du

  infix 15 _\^/_

  data _\^/_ : forall {iz jz kz uz : Bwd X}
             {th0 : iz <= jz}{th1 : jz <= uz}
             {ph0 : iz <= kz}{ph1 : kz <= uz}
             {ps}
          -> [ th0 & th1 ]~ ps -> [ ph0 & ph1 ]~ ps -> Set
    where
    _-^_ : forall {iz jz kz uz}
             {th0 : iz <= jz}{th1 : jz <= uz}
             {ph0 : iz <= kz}{ph1 : kz <= uz}
             {ps}
             {v : [ th0 & th1 ]~ ps}{w : [ ph0 & ph1 ]~ ps}
          -> v \^/ w -> forall x
          -> v -^ x \^/ w -^ x
    _-,^_ : forall {iz jz kz uz}
             {th0 : iz <= jz}{th1 : jz <= uz}
             {ph0 : iz <= kz}{ph1 : kz <= uz}
             {ps}
             {v : [ th0 & th1 ]~ ps}{w : [ ph0 & ph1 ]~ ps}
          -> v \^/ w -> forall x
          -> v -^, x \^/ w -^ x
    _-^,_ : forall {iz jz kz uz}
             {th0 : iz <= jz}{th1 : jz <= uz}
             {ph0 : iz <= kz}{ph1 : kz <= uz}
             {ps}
             {v : [ th0 & th1 ]~ ps}{w : [ ph0 & ph1 ]~ ps}
          -> v \^/ w -> forall x
          -> v -^ x \^/ w -^, x
    _-,_ : forall {iz jz kz uz}
             {th0 : iz <= jz}{th1 : jz <= uz}
             {ph0 : iz <= kz}{ph1 : kz <= uz}
             {ps}
             {v : [ th0 & th1 ]~ ps}{w : [ ph0 & ph1 ]~ ps}
          -> v \^/ w -> forall x
          -> v -, x \^/ w -, x
    [] : [] \^/ []

  record Pub {uz : Bwd X}(th : < _<= uz >)(ph : < _<= uz >) : Set where
    constructor pb
    field
      {intersection} : Bwd X
      {diagonal}     : intersection <= uz
      {leftSelect}   : intersection <= fst th
      {rightSelect}  : intersection <= fst ph
      {leftTri}      : [ leftSelect & snd th ]~ diagonal
      {rightTri}     : [ rightSelect & snd ph ]~ diagonal
      pullback       : leftTri \^/ rightTri

  open Pub public

  pub : forall {uz : Bwd X}(th : < _<= uz >)(ph : < _<= uz >) -> Pub th ph
  pub (_ , th -^ y) (_ , ph -^ .y) = let pb a = pub (_ , th) (_ , ph) in pb (a -^ y)
  pub (_ , th -^ y) (_ , (ph -, .y)) = let pb a = pub (_ , th) (_ , ph) in pb (a -^, y)
  pub (_ , (th -, x)) (_ , ph -^ .x) = let pb a = pub (_ , th) (_ , ph) in pb (a -,^ x)
  pub (_ , (th -, x)) (_ , (ph -, .x)) = let pb a = pub (_ , th) (_ , ph) in pb (a -, x)
  pub (_ , []) (_ , []) = pb []

  record Neg {uz : Bwd X}(th : < _<= uz >) : Set where
    constructor _u!^_
    field
      {complement} : Bwd X
      {negation} : complement <= uz
      exhaustive : snd th /u\ negation
      exclusive  : no& (snd th) \^/ no& negation

  open Neg public

  neg : forall {uz : Bwd X}(th : < _<= uz >) -> Neg th
  neg (_ , th -^ y) = let u u!^ a = neg (_ , th) in (u -^, y) u!^ (a -^, y)
  neg (_ , th -, x) = let u u!^ a = neg (_ , th) in (u -,^ x) u!^ (a -,^ x)
  neg (_ , []) = [] u!^ []

  infix 15 _:^_
  infixl 25 _^_
  record _:^_ (P : Bwd X -> Set)(ga : Bwd X) : Set where
    constructor _^_
    field
      {support} : Bwd X
      thing     : P support
      thinning  : support <= ga
  open _:^_ public

  _^&_ : forall {P ga} -> P :^ ga -> [ ga <=_ -:> P :^_ ]
  (p ^ th) ^& ph = p ^ th & ph

-}
