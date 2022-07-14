module SmolCat where

open import Basics

record SmolCat : Set1 where
  field
    Obj : Set
    _=>_ : Obj -> Obj -> Set
    iden : {X : Obj} -> X => X
    [_-_]~_ : forall {R S T} ->
      R => S -> S => T -> R => T -> Set
    compU : forall {R S T}
      (f : R => S)(g : S => T) ->
      Uniquely < [ f - g ]~_ >
    absl : forall {S T}(f : S => T) ->
      [ iden - f ]~ f
    absr : forall {S T}(f : S => T) ->
      [ f - iden ]~ f
    asso03 : forall {X0 X1 X2 X3}
      {f01 : X0 => X1}{f23 : X2 => X3}{f02 : X0 => X2}{f13 : X1 => X3}
      -> < [ f01 -_]~ f02  *: [_- f23 ]~ f13  >
      -> < [ f01 - f13 ]~_ *: [ f02 - f23 ]~_ >
  comp : forall {R S T}(f : R => S)(g : S => T) -> _
  comp f g = fst (compU f g)
  compQ : forall {R S T}{f : R => S}{g : S => T} -> _
  compQ {f = f}{g = g} = snd (compU f g)
  infix 25 [_-_]~_
  asso02 : forall {X0 X1 X2 X3}
      {f01 : X0 => X1}{f03 : X0 => X3}{f12 : X1 => X2}{f23 : X2 => X3}
      -> < [ f01 -_]~ f03 *: [ f12 - f23 ]~_ >
      -> < [ f01 - f12 ]~_ *: [_- f23 ]~ f03 >
  asso02 {f01 = f01} {f12 = f12} (_ , v , w)
    with _ , a <- comp f01 f12
       | _ , b , c <- asso03 (_ , a , w)
       | r~ <- compQ (_ , b) (_ , v)
    = _ , a , c
  asso13 : forall {X0 X1 X2 X3}
      {f01 : X0 => X1}{f03 : X0 => X3}{f12 : X1 => X2}{f23 : X2 => X3}
      -> < [ f01 - f12 ]~_ *: [_- f23 ]~ f03 >
      -> < [ f01 -_]~ f03 *: [ f12 - f23 ]~_ >
  asso13 {f12 = f12} {f23} (_ , v , w)
    with _ , a <- comp f12 f23
       | _ , b , c <- asso03 (_ , v , a)
       | r~ <- compQ (_ , c) (_ , w)
       = _ , b , a

module _ (X : Set) where

  open SmolCat
  
  DISCRETE : SmolCat
  Obj DISCRETE = X
  _=>_ DISCRETE = _~_
  iden DISCRETE = r~
  [_-_]~_ DISCRETE _ _ _ = One
  fst (compU DISCRETE r~ r~) = r~ , _
  snd (compU DISCRETE r~ r~) (r~ , _) (r~ , _) = r~
  absl DISCRETE = _
  absr DISCRETE = _
  asso03 DISCRETE {f01 = r~} {f13 = r~} (r~ , _) = r~ , _

module _ (C : SmolCat) where

  open SmolCat C

  OP : SmolCat
  SmolCat.Obj OP = Obj
  SmolCat._=>_ OP S T = T => S
  SmolCat.iden OP = iden
  SmolCat.[_-_]~_ OP f g h = [ g - f ]~ h
  SmolCat.compU OP f g = compU g f
  SmolCat.absl OP = absr
  SmolCat.absr OP = absl
  SmolCat.asso03 OP (! v , w) = let ! x , y = asso03 (! w , v) in ! y , x

module _ (C : SmolCat) where

  open SmolCat C

  data ConeObj : Set where
    orig : ConeObj
    base : Obj -> ConeObj

  data _-Cone>_ : ConeObj -> ConeObj -> Set where
    orig : forall X -> orig -Cone> X
    base : forall {S T : Obj} -> S => T -> base S -Cone> base T

  data [_-Cone-_]~_ : forall {R S T}
    -> R -Cone> S -> S -Cone> T -> R -Cone> T -> Set
    where
    orig : forall X -> [ orig orig -Cone- orig X ]~ orig X
    face : forall {S T}(f : S => T) -> [ orig (base S) -Cone- base f ]~ orig (base T)
    base : forall {R S T}{f : R => S}{g : S => T}{h : R => T} ->
      [ f - g ]~ h -> [ base f -Cone- base g ]~ base h

  CONE : SmolCat
  SmolCat.Obj CONE = ConeObj
  SmolCat._=>_ CONE = _-Cone>_
  SmolCat.iden CONE {orig} = orig orig
  SmolCat.iden CONE {base X} = base iden
  SmolCat.[_-_]~_ CONE = [_-Cone-_]~_
  fst (SmolCat.compU CONE (orig .orig) (orig X)) = ! orig X
  snd (SmolCat.compU CONE (orig .orig) (orig X)) (! orig .X) (! orig .X) = r~
  fst (SmolCat.compU CONE (orig ._) (base f)) = ! face f
  snd (SmolCat.compU CONE (orig ._) (base f)) (! face .f) (! face .f) = r~
  fst (SmolCat.compU CONE (base f) (base g)) = let ! v = comp f g in ! base v
  snd (SmolCat.compU CONE (base f) (base g)) (! base v) (! base w)
    with r~ <- compQ (! v) (! w) = r~
  SmolCat.absl CONE (orig X) = orig X
  SmolCat.absl CONE (base f) = base (absl _)
  SmolCat.absr CONE (orig orig) = orig orig
  SmolCat.absr CONE (orig (base X)) = face iden
  SmolCat.absr CONE (base f) = base (absr f)
  SmolCat.asso03 CONE (! orig .orig , orig X) = ! orig _ , orig _
  SmolCat.asso03 CONE (! orig .(base _) , face f) = ! orig _ , face _
  SmolCat.asso03 CONE (! face f , base v) = ! face _ , face _
  SmolCat.asso03 CONE (! base v , base w) = 
    let ! x , y = asso03 (! v , w) in ! base x , base y

module _ (Src Trg : SmolCat) where

  module C = SmolCat Src
  module D = SmolCat Trg

  record _-Smol>_ : Set1 where
    field
      RObj : C.Obj -> D.Obj -> Set
      FObj : forall X -> Uniquely < RObj X >
      RArr : forall {CS CT DS DT} ->
             CS C.=> CT -> RObj CS DS -> RObj CT DT -> DS D.=> DT -> Set
      FArr : forall {CS CT DS DT}(f : CS C.=> CT)(s : RObj CS DS)(t : RObj CT DT)
          -> Uniquely < RArr f s t >
      RIdn : forall {CX DX}(x : RObj CX DX) ->
             RArr C.iden x x D.iden
      RCom : forall {CR CS CT DR DS DT}
             {r : RObj CR DR}{s : RObj CS DS}{t : RObj CT DT}
             {cf : CR C.=> CS}{df : DR D.=> DS}
             {cg : CS C.=> CT}{dg : DS D.=> DT}
             {ch : CR C.=> CT}{dh : DR D.=> DT}
          -> C.[ cf - cg ]~ ch
          -> RArr cf r s df -> RArr cg s t dg
          -> D.[ df - dg ]~ dh
          -> RArr ch r t dh

{-
module _ (C : SmolCat) where

  open SmolCat C

  module _ (X : Obj) where

    _/_ : SmolCat
    SmolCat.Obj _/_ = < _=> X >
    SmolCat._=>_ _/_ (! f) (! g) = < [_- g ]~ f >
    SmolCat.iden _/_ {_ , f} = ! absl f
    SmolCat.[_-_]~_ _/_ (f , _) (g , _) (h , _) = [ f - g ]~ h
    SmolCat.comp _/_ (f , v) (g , w)
      with h , x <- comp f g
         | ! y , z <- asso03 (! x , w)
         | r~ <- compQ (! y) (! v)
         = (h , z) , x
    SmolCat.compQ _/_ ((! a) , b) ((! c) , d)
      with r~ <- compQ (! b) (! d)
         | r~ <- compQ (! a) (! c)
         = r~
    SmolCat.absl _/_ _ = absl _
    SmolCat.absr _/_ _ = absr _
    SmolCat.asso03 _/_ {f01 = ! a01}{f23 = ! a23}{f02 = ! a02}{f13 = ! a13}
      ((! a12) , vw)
      with ! x , y <- asso03 (! vw)
         | ! b , c <- asso03 (! x , a13)
         | r~ <- compQ (! b) (! a01)
      = (! c) , x , y

  record Coproducty : Set where
    field
      injections : forall A B -> < A =>_ *: B =>_ >
    COP : Obj -> Obj -> Obj
    COP A B = fst (injections A B)
    injl : forall {A B} -> A => COP A B
    injl {A}{B} = fst (snd (injections A B))
    injr : forall {A B} -> B => COP A B
    injr {A}{B} = snd (snd (injections A B))
    field
      copCase : forall {A B}
        ((! l , r) : < A =>_ *: B =>_ >) ->
        Uniquely < [ injl -_]~ l *: [ injr -_]~ r > 
-}
