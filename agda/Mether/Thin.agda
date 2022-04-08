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
  Arr THIN = _<=_
  iden THIN = io
  [_-_]~_ THIN = [_&_]~_
  comp THIN th         (ph -^ y) = let _ , ps = comp THIN th ph in _ , ps -^ y
  comp THIN (th -^ .x) (ph -, x) = let _ , ps = comp THIN th ph in _ , ps -^, x
  comp THIN (th -, .x) (ph -, x) = let _ , ps = comp THIN th ph in _ , ps -, x
  comp THIN [] [] = _ , []
  compU THIN (_ , v -^ z) (_ , w -^ .z)
    with r~ <- compU THIN (_ , v) (_ , w) = r~
  compU THIN (_ , v -^, y) (_ , w -^, .y)
    with r~ <- compU THIN (_ , v) (_ , w) = r~
  compU THIN (_ , (v -, x)) (_ , (w -, .x))
    with r~ <- compU THIN (_ , v) (_ , w) = r~
  compU THIN (_ , []) (_ , []) = r~
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
  triQ v with r~ <- compU (_ , v) (comp _ _) = r~

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

  module _ {xz yz zz : Bwd X}{th : xz <= zz}{ph : yz <= zz}(u : th /u\ ph) where
    luth = th
    ruth = ph

  Cop : forall {xz yz : Bwd X} -> < xz <=_ *: yz <=_ > -> Set
  Cop {xz}{yz} (zz , th , ph) =
    < xz <=_ *: _<= zz *: yz <=_ > >< \ (_ , th' , ps , ph') ->
    [ th' & ps ]~ th * th' /u\ ph' * [ ph' & ps ]~ ph

  copa : forall {xz yz : Bwd X}{z@(zz , _) : < xz <=_ *: yz <=_ >}
    (C@((uz , _) , _) : Cop z) -> uz <= zz
  copa ((_ , _ , ps , _) , _) = ps
              
  cop : forall {xz yz} -> [> Cop {xz}{yz} ]
  cop (_ , th -^ y , ph -^ .y) =
    let _ , v , u , w = cop (_ , th , ph) in _ , v -^ y  , u       , w -^ y
  cop (_ , th -^ y , ph -, .y) =
    let _ , v , u , w = cop (_ , th , ph) in _ , v -^, y , u -^, y , w -, y
  cop (_ , th -, x , ph -^ .x) =
    let _ , v , u , w = cop (_ , th , ph) in _ , v -, x  , u -,^ x , w -^, x
  cop (_ , th -, x , ph -, .x) =
    let _ , v , u , w = cop (_ , th , ph) in _ , v -, x  , u -, x  , w -, x
  cop (_ ,    []   ,    []   ) =             _ ,   []    ,   []    ,   []

  copQ : forall {xz yz zz}{th : xz <= zz}{ph : yz <= zz}
      -> (a b : th /u\ ph) -> a ~ b
  copQ (a -^, y) (b -^, .y) rewrite copQ a b = r~
  copQ (a -,^ x) (b -,^ .x) rewrite copQ a b = r~
  copQ (a -, z) (b -, .z) rewrite copQ a b = r~
  copQ [] [] = r~

  copU : forall {xz yz}{c@(zz , th , ph) : < xz <=_ *: yz <=_ >}
      -> (((uz , th' , ps , ph') , v , u , w) : Cop c)
      -> ((uz0 , th0 , ps0 , ph0) : < xz <=_ *: _<= zz *: yz <=_ >)
      -> [ th0 & ps0 ]~ th -> [ ph0 & ps0 ]~ ph
      -> < [ th' &_]~ th0 *: [_& ps0 ]~ ps *: [ ph' &_]~ ph0 >
  copU (_ , v -^ .z , u , w -^ .z) _ (v' -^ z) (w' -^ .z)
    with _ , v0 , t0 , w0 <- copU (_ , v , u , w) _ v' w'
    = _ , v0 , t0 -^ z , w0
  copU (_ , v -^, y , () , w -^, .y) _ (v' -^ .y) (w' -^ .y)
  copU (_ , v -^ _ , u , w -^ _) _ (v' -^, _) (w' -^, _)
    with _ , v0 , t0 , w0 <- copU (_ , v , u , w) _ v' w'
    = _ , v0 -^ _ , t0 -^, _ , w0 -^ _
  copU (_ , v -^, .y , () , w -^, .y) _ (v' -^, y) (w' -^, .y)
  copU (_ , v -^, .y , u -^, .y , (w -, .y)) _ (v' -^, y) (w' -, .y)
    with _ , v0 , t0 , w0 <- copU (_ , v , u , w) _ v' w'
    = _ , v0 -^, y , t0 -, y , w0 -, y
  copU (_ , (v -, .x) , u -,^ .x , w -^, .x) _ (v' -, x) (w' -^, .x)
    with _ , v0 , t0 , w0 <- copU (_ , v , u , w) _ v' w'
    = _ , v0 -, x , t0 -, x , w0 -^, x
  copU (_ , (v -, .x) , (u -, .x) , (w -, .x)) _ (v' -, x) (w' -, .x)
    with _ , v0 , t0 , w0 <- copU (_ , v , u , w) _ v' w'
    = _ , v0 -, x , t0 -, x , w0 -, x
  copU (_ , [] , [] , []) _ [] [] = _ , [] , [] , []

  CopQ : forall {xz yz}{c : < xz <=_ *: yz <=_ >}
         (a b : Cop c) -> a ~ b
  CopQ l@((_ , thl , psl , phl) , vl , ul , wl)
       r@((_ , thr , psr , phr) , vr , ur , wr)
    with chl , a , b , c <- copU l _ vr wr
       | chr , d , e , f <- copU r _ vl wl
       | r~ , r~ , r~ <- asy chl chr
       | r~ <- compU (_ , a) (_ , absr _)
       | r~ <- compU (_ , b) (_ , absl _)
       | r~ <- compU (_ , c) (_ , absr _)
       | r~ <- compU (_ , vl) (_ , vr)
       | r~ <- copQ ul ur
       | r~ <- compU (_ , wl) (_ , wr)
    = r~

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

  copL : forall {xz yz}(th : xz <= yz) ->
    cop (_ , th , no) ~ ((_ , io , th , no) , absl th , lll , no& th)
  copL (th -^ y) rewrite copL th = r~
  copL (th -, x) rewrite copL th = r~
  copL [] = r~

  copR : forall {xz yz}(th : xz <= yz) ->
    cop (_ , no , th) ~ ((_ , no , th , io) , no& th , rrr , absl th)
  copR (th -^ y) rewrite copR th = r~
  copR (th -, x) rewrite copR th = r~
  copR [] = r~

  copSwap : forall {xz yz zz}{th : yz <= zz}{ph : xz <= zz}
         -> th /u\ ph -> ph /u\ th
  copSwap (u -^, y) = copSwap u -,^ y
  copSwap (u -,^ x) = copSwap u -^, x
  copSwap (u -, z) = copSwap u -, z
  copSwap [] = []

  copRot : forall {xz yz wz}
      -> {z@(zz , th , ph) : < xz <=_ *: yz <=_ >}
      -> (C@((_ , _ , ch , _) , _) : Cop z)
      -> {ps : wz <= zz}
      -> ch /u\ ps
      -> let (_ , _ , psr , _) , vr , ur , wr = cop (_ , ph , ps)
      in th /u\ psr
  copRot {z = _ , th , ph} C@((_ , _ , ch , _) , v , u , w) x
    with cr@((_ , _ , psr , _) , vr , ur , wr) <- cop (_ , ph , ruth x)
       | (_ , _ , om , _) , tl , y , tr <- cop (_ , th , psr)
       | (_ , _ , b) , (_ , _ , h ) <- asso02 (_ , vr , tr) , asso02 (_ , wr , tr)
       | _ , _ , e , _ <- copU C _ tl b
       | _ , _ , j , _ <- copU (_ , absr _ , x , absr _) _ e h
       | r~ , r~ , r~ <- asyL j
       | r~ <- compU (_ , tr) (_ , absr _)
       | r~ <- compU (_ , tl) (_ , absr _)
    = y

  copDis : forall {xz yz wz}
        -> {z@(zz , th , ph) : < xz <=_ *: yz <=_ >}
        -> (((_ , _ , ch , _) , _) : Cop z)
        -> {ps : wz <= zz}
        -> ch /u\ ps
        -> let (_ , _ , psl , _) , vl , ul , wl = cop (_ , th , ps)
        in let (_ , _ , psr , _) , vr , ur , wr = cop (_ , ph , ps)
        in psl /u\ psr
  copDis {z = _ , th , ph} C@((_ , _ , ch , _) , v , u , w) x
    with cl@((_ , _ , psl , _) , vl , ul , wl) <- cop (_ , th , ruth x)
       | cr@((_ , _ , psr , _) , vr , ur , wr) <- cop (_ , ph , ruth x)
       | (_ , _ , nu , _) , v' , u' , w' <- cop (_ , psl , psr)
       | (_ , a , b) , (_ , c , d) <- asso02 (_ , vl , v') , asso02 (_ , vr , w')
       | _ , e , f , g <- copU C _ b d
       | _ , h , i <- asso02 (_ , wr , w')
       | om , j , k , l <- copU (_ , absr _ , x , absr _) _ f i
       | r~ , r~ , r~ <- asy om nu
       | r~ , r~ <- compU (_ , v') (_ , absr _) , compU (_ , w') (_ , absr _)
    = u'

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
