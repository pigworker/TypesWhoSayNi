module Thin where

open import Basics
open import Bwd

module _ {X : Set} where

  data _<=_ : Bwd X -> Bwd X -> Set where
    _-^_ : forall {ga de} -> ga <= de -> forall x -> ga      <= de -, x
    _-,_ : forall {ga de} -> ga <= de -> forall x -> ga -, x <= de -, x
    [] : [] <= []

  infix 15 _<=_ [_-<_]~_ _<1_
  infixl 20 _-^_ _-^,_ _-,^_ _-<io _-<_

  _<1_ : X -> Bwd X -> Set
  x <1 ga = [] -, x <= ga

  no : forall {de} -> [] <= de
  no {[]} = []
  no {de -, x} = no -^ x

  noQ : forall {de}(th ph : [] <= de) -> th ~ ph
  noQ (th -^ x) (ph -^ .x) with r~ <- noQ th ph = r~
  noQ [] [] = r~

  io : forall {de} -> de <= de
  io {[]} = []
  io {de -, x} = io -, x

  data [_-<_]~_ : forall {ga de xi} -> ga <= de -> de <= xi -> ga <= xi -> Set where
    _-^_ : forall {ga de xi}{th : ga <= de}{ph : de <= xi}{ps : ga <= xi} -> [ th -< ph ]~ ps
        -> forall x -> [ th -< ph -^ x ]~ ps -^ x
    _-^,_ : forall {ga de xi}{th : ga <= de}{ph : de <= xi}{ps : ga <= xi} -> [ th -< ph ]~ ps
        -> forall x -> [ th -^ x -< ph -, x ]~ ps -^ x
    _-,_ : forall {ga de xi}{th : ga <= de}{ph : de <= xi}{ps : ga <= xi} -> [ th -< ph ]~ ps
        -> forall x -> [ th -, x -< ph -, x ]~ ps -, x
    [] : [ [] -< [] ]~ []

  tri : forall {ga de xi}(th : ga <= de)(ph : de <= xi) -> <1 <: [ th -< ph ]~_ :> 1>
  tri th (ph -^ x) .fst with (_ , v) , _ <- tri th ph = _ , v -^ x
  tri th (ph -^ x) .snd (_ , w -^ .x) with (_ , v) , q <- tri th ph with r~ <- q (_ , w) = r~
  tri (th -^ .x) (ph -, x) .fst with (_ , v) , _ <- tri th ph = _ , v -^, x
  tri (th -^ .x) (ph -, x) .snd (_ , w -^, .x) with (_ , v) , q <- tri th ph with r~ <- q (_ , w) = r~
  tri (th -, .x) (ph -, x) .fst with (_ , v) , _ <- tri th ph = _ , v -, x
  tri (th -, .x) (ph -, x) .snd (_ , w -, .x)  with (_ , v) , q <- tri th ph with r~ <- q (_ , w) = r~
  tri [] [] .fst = _ , []
  tri [] [] .snd (_ , []) = r~

  _-<_ : forall {ga de xi}(th : ga <= de)(ph : de <= xi) -> ga <= xi
  th -< ph = tri th ph .fst .fst

  antisym : forall {ga de}(th : ga <= de)(ph : de <= ga)
         -> (ga ~ de) >< \ { r~ -> (th ~ io) * (ph ~ io) }
  antisym (th -^ x) ph with antisym th (io -^ x -< ph)
  antisym (th -^ _) (ph -^ x) | r~ , r~ , ()
  antisym (th -^ _) (ph -, _) | r~ , r~ , ()
  antisym (th -, x) (ph -^ .x) with r~ , () , w <- antisym (th -^ x) ph
  antisym (th -, x) (ph -, .x) with r~ , r~ , r~ <- antisym th ph = r~ , r~ , r~
  antisym [] [] = r~ , r~ , r~

  ioQ : forall {de}(th ph : de <= de) -> th ~ ph
  ioQ (th -, x) (ph -, .x) with r~ <- ioQ th ph = r~
  ioQ (th -^ x) ph with () , _ <- antisym th (io -^ x)
  ioQ (th -, x) (ph -^ .x) with () , _ <- antisym ph (io -^ x)
  ioQ [] [] = r~

  no-< : forall {ga de}(th : ga <= de) -> [ no -< th ]~ no
  no-< (th -^ x) = no-< th -^ x
  no-< (th -, x) = no-< th -^, x
  no-< [] = []

  io-< : forall {ga de}(th : ga <= de) -> [ io -< th ]~ th
  io-< (th -^ x) = io-< th -^ x
  io-< (th -, x) = io-< th -, x
  io-< [] = []

  _-<io : forall {ga de}(th : ga <= de) -> [ th -< io ]~ th
  th -^ x -<io = th -<io -^, x
  th -, x -<io = th -<io -, x
  [] -<io = []

  asso03 : forall {ga0 ga1 ga2 ga3}
        -> {th01 : ga0 <= ga1}{th02 : ga0 <= ga2}{th13 : ga1 <= ga3}{th23 : ga2 <= ga3}
        -> <: [ th01 -<_]~ th02 :* [_-< th23 ]~ th13 :>
        -> <: [ th01 -< th13 ]~_ :* [ th02 -< th23 ]~_ :>
  asso03 (_ , v , w -^ x) with _ , s , t <- asso03 (_ , v , w) = _ , s -^ x , t -^ x
  asso03 (_ , v -^ .x , w -^, x) with _ , s , t <- asso03 (_ , v , w) = _ , s -^ x , t -^, x
  asso03 (_ , v -^, .x , w -, x) with _ , s , t <- asso03 (_ , v , w) = _ , s -^, x , t -^, x
  asso03 (_ , v -, .x , w -, x) with _ , s , t <- asso03 (_ , v , w) = _ , s -, x , t -, x
  asso03 (_ , [] , []) = _ , [] , []

  asso02 : forall {ga0 ga1 ga2 ga3}
        -> {th01 : ga0 <= ga1}{th03 : ga0 <= ga3}{th12 : ga1 <= ga2}{th23 : ga2 <= ga3}
        -> <: [ th01 -<_]~ th03 :* [ th12 -< th23 ]~_ :>
        -> <: [ th01 -< th12 ]~_ :* [_-< th23 ]~ th03 :>
  asso02 {th01 = th01} {th12 = th12} (_ , v , w)
    with (_ , s) , _ <- tri th01 th12
    with (_ , v' , t) <- asso03 (_ , s , w)
    with r~ <- unique (tri _ _) {_ , v} {_ , v'}
       = _ , s , t

  asso13 : forall {ga0 ga1 ga2 ga3}
        -> {th01 : ga0 <= ga1}{th03 : ga0 <= ga3}{th12 : ga1 <= ga2}{th23 : ga2 <= ga3}
        -> <: [ th01 -< th12 ]~_ :* [_-< th23 ]~ th03 :>
        -> <: [ th01 -<_]~ th03 :* [ th12 -< th23 ]~_ :>
  asso13 {th12 = th12} {th23} (_ , v , w)
    with (_ , t) , _ <- tri th12 th23
    with (_ , s , w') <- asso03 (_ , v , t)
    with r~ <- unique (tri _ _) {_ , w} {_ , w'}
       = _ , s , t

  infix 15 _/u\_

  data _/u\_ : forall {de ga xi}(th : de <= ga)(ph : xi <= ga) -> Set where
    _-^,_ : forall {de ga xi}{th : de <= ga}{ph : xi <= ga} -> th /u\ ph
         -> forall x -> th -^ x /u\ ph -, x
    _-,^_ : forall {de ga xi}{th : de <= ga}{ph : xi <= ga} -> th /u\ ph
         -> forall x -> th -, x /u\ ph -^ x
    _-,_ : forall {de ga xi}{th : de <= ga}{ph : xi <= ga} -> th /u\ ph
         -> forall x -> th -, x /u\ ph -, x
    []   : [] /u\ []

  egtbs : forall {de ga xi}{th : de <= ga}{ph : xi <= ga}
       -> th /u\ ph
       -> ((_ , i) : <: _<1 ga :>)
       -> <: [_-< th ]~ i :> + <: [_-< ph ]~ i :>
  egtbs (u -^, x) (_ , i -^ .x) with egtbs u (_ , i)
  ... | ff , _ , j = ff , _ , j -^ x
  ... | tt , _ , j = tt , _ , j -^, x
  egtbs (u -^, x) (_ , (i -, .x)) with r~ <- noQ i no = tt , _ , no-< _ -, _
  egtbs (u -,^ x) (_ , i -^ .x) with egtbs u (_ , i)
  ... | ff , _ , j = ff , _ , j -^, x
  ... | tt , _ , j = tt , _ , j -^ x
  egtbs (u -,^ x) (_ , i -, .x) with r~ <- noQ i no = ff , _ , no-< _ -, _
  egtbs (u -, x) (_ , i -^ .x) with egtbs u (_ , i)
  ... | ff , _ , j = ff , _ , j -^, x
  ... | tt , _ , j = tt , _ , j -^, x
  egtbs (u -, x) (_ , (i -, .x)) with r~ <- noQ i no = ff , _ , no-< _ -, _
  egtbs [] (_ , ())

  sbtge : forall {de ga xi}{th : de <= ga}{ph : xi <= ga}
       -> (((_ , i) : <: _<1 ga :>)
            -> <: [_-< th ]~ i :> + <: [_-< ph ]~ i :>)
       -> th /u\ ph
  sbtge {th = th -^ x} {ph -^ .x} d with d (_ , no -, x)
  ... | ff , ()
  ... | tt , ()
  sbtge {th = th -^ x} {ph -, .x} d = sbtge e -^, x where
    e : ((_ , i) : <: _<1 _ :>) -> <: [_-< th ]~ i :> + <: [_-< ph ]~ i :>
    e (_ , i) with d (_ , i -^ x)
    ... | ff , _ , v -^ .x = ff , _ , v
    ... | tt , _ , v -^, .x = tt , _ , v
  sbtge {th = th -, x} {ph -^ .x} d = sbtge e -,^ x where
    e : ((_ , i) : <: _<1 _ :>) -> <: [_-< th ]~ i :> + <: [_-< ph ]~ i :>
    e (_ , i) with d (_ , i -^ x)
    ... | ff , _ , v -^, .x = ff , _ , v
    ... | tt , _ , v -^ .x = tt , _ , v
  sbtge {th = th -, x} {ph -, .x} d = sbtge e -, x where
    e : ((_ , i) : <: _<1 _ :>) -> <: [_-< th ]~ i :> + <: [_-< ph ]~ i :>
    e (_ , i) with d (_ , i -^ x)
    ... | ff , _ , v -^, .x = ff , _ , v
    ... | tt , _ , v -^, .x = tt , _ , v
  sbtge {th = []} {[]} d = []

  infix 15 _</\>_
  record Cosp {de om xi}(th : de <= om)(ph : xi <= om) : Set where
    constructor _</\>_
    field
      {union} : Bwd X
      {luth} : de <= union
      {uuth} : union <= om
      {ruth} : xi <= union
      ltri : [ luth -< uuth ]~ th
      rtri : [ ruth -< uuth ]~ ph
  open Cosp public

  Cop : forall {de om xi}(th : de <= om)(ph : xi <= om) -> Set
  Cop th ph = Cosp th ph >< \ c -> c .luth /u\ c .ruth

  cop : forall {de om xi}(th : de <= om)(ph : xi <= om) -> <1 Cop th ph 1>
  cop (th -^ x) (ph -^ .x) .fst with (v </\> w , u) , q <- cop th ph = v -^ x </\> w -^ x , u
  cop (th -^ x) (ph -^ .x) .snd (v' -^ .x </\> w' -^ .x , u')
    with (v </\> w , u) , q <- cop th ph with r~ <- q (v' </\> w' , u') = r~
  cop (th -^ x) (ph -^ .x) .snd (v -^, .x </\> w -^, .x , ())
  cop (th -^ x) (ph -, .x) .fst with (v </\> w , u) , q <- cop th ph = v -^, x </\> w -, x , u -^, x
  cop (th -^ x) (ph -, .x) .snd (v' -^, .x </\> w' -, .x , u' -^, .x)
    with (v </\> w , u) , q <- cop th ph with r~ <- q (v' </\> w' , u') = r~
  cop (th -, x) (ph -^ .x) .fst  with (v </\> w , u) , q <- cop th ph = v -, x </\> w -^, x , u -,^ x
  cop (th -, x) (ph -^ .x) .snd (v' -, .x </\> w' -^, .x , u' -,^ .x)
    with (v </\> w , u) , q <- cop th ph with r~ <- q (v' </\> w' , u') = r~
  cop (th -, x) (ph -, .x) .fst with (v </\> w , u) , q <- cop th ph = v -, x </\> w -, x , u -, x
  cop (th -, x) (ph -, .x) .snd (v' -, .x </\> w' -, .x , (u' -, .x))
    with (v </\> w , u) , q <- cop th ph with r~ <- q (v' </\> w' , u') = r~
  cop [] [] .fst = [] </\> [] , []
  cop [] [] .snd ([] </\> [] , []) = r~

  copU : forall {de om xi}{th : de <= om}{ph : xi <= om}
      -> (c' : Cosp th ph) -> (cu : Cop th ph)
      -> <: [ cu .fst . luth -<_]~ c' .luth
         :* [_-< c' .uuth ]~ cu .fst .uuth
         :* [ cu .fst . ruth -<_]~ c' .ruth
         :>
  copU (v' -^ x </\> w' -^ .x) (v -^ .x </\> w -^ .x , u)
    with _ , a , b , c <- copU (v' </\> w') (v </\> w , u) = _ , a , b -^ x , c
  copU _ (v -^, _ </\> w -^, _ , ())
  copU (v' -^, x </\> w' -^, .x) (v -^ .x </\> w -^ .x , u)
    with _ , a , b , c <- copU (v' </\> w') (v </\> w , u) = _ , a -^ x , b -^, x , c -^ x
  copU (v' -^, x </\> w' -, .x) (v -^, .x </\> (w -, .x) , u -^, .x)
    with _ , a , b , c <- copU (v' </\> w') (v </\> w , u) = _ , a -^, x , b -, x , c -, x
  copU (v' -, x </\> w' -^, .x) (v -, .x </\> w -^, .x , u -,^ .x)
    with _ , a , b , c <- copU (v' </\> w') (v </\> w , u) = _ , a -, x , b -, x , c -^, x
  copU ((v' -, x) </\> (w' -, .x)) (v -, .x </\> w -, .x , u -, .x)
    with _ , a , b , c <- copU (v' </\> w') (v </\> w , u) = _ , a -, x , b -, x , c -, x
  copU ([] </\> []) ([] </\> [] , []) = _ , [] , [] , []

  Sq : forall {al be ga de}(th : be <= de)(ph : ga <= de)(ph* : al <= be)(th* : al <= ga) -> Set
  Sq th ph ph* th* = <: [ ph* -< th ]~_ :* [ th* -< ph ]~_ :>

  data Pub : forall {al be ga de}{th : be <= de}{ph : ga <= de}{ph* : al <= be}{th* : al <= ga}
          -> Sq th ph ph* th* -> Set
    where
    _-^_ : forall {al be ga de}{th : be <= de}{ph : ga <= de}{ph* : al <= be}{th* : al <= ga}
        -> {(_ , v , w) : Sq th ph ph* th*} -> Pub (_ , v , w)
        -> forall x -> Pub (_ , v -^ x , w -^ x)
    _-,^_ : forall {al be ga de}{th : be <= de}{ph : ga <= de}{ph* : al <= be}{th* : al <= ga}
        -> {(_ , v , w) : Sq th ph ph* th*} -> Pub (_ , v , w)
        -> forall x -> Pub (_ , v -^, x , w -^ x)
    _-^,_ : forall {al be ga de}{th : be <= de}{ph : ga <= de}{ph* : al <= be}{th* : al <= ga}
        -> {(_ , v , w) : Sq th ph ph* th*} -> Pub (_ , v , w)
        -> forall x -> Pub (_ , v -^ x , w -^, x)
    _-,_ : forall {al be ga de}{th : be <= de}{ph : ga <= de}{ph* : al <= be}{th* : al <= ga}
        -> {(_ , v , w) : Sq th ph ph* th*} -> Pub (_ , v , w)
        -> forall x -> Pub (_ , v -, x , w -, x)
    [] : Pub (_ , [] , [])

  pub : forall {be ga de}(th : be <= de)(ph : ga <= de)
     -> <1(_ >< \ al -> al <= be >< \ ph* -> al <= ga >< \ th* -> Sq th ph ph* th* >< Pub)1>
  pub (th -^ x) (ph -^ .x) .fst
    with (_ , _ , _ , _ , p) , _ <- pub th ph
       = _ , _ , _ , _ , p -^ x
  pub (th -^ x) (ph -^ .x) .snd (_ , _ , _ , _ , p' -^ .x)
    with (_ , _ , _ , _ , p) , q <- pub th ph
    with r~ <- q (_ , _ , _ , _ , p')
       = r~
  pub (th -^ x) (ph -, .x) .fst
    with (_ , _ , _ , _ , p) , _ <- pub th ph
       = _ , _ , _ , _ , p -^, x
  pub (th -^ x) (ph -, .x) .snd (_ , _ , _ , _ , p' -^, .x)
    with (_ , _ , _ , _ , p) , q <- pub th ph
    with r~ <- q (_ , _ , _ , _ , p')
       = r~
  pub (th -, x) (ph -^ .x) .fst
    with (_ , _ , _ , _ , p) , _ <- pub th ph
       = _ , _ , _ , _ , p -,^ x
  pub (th -, x) (ph -^ .x) .snd (_ , _ , _ , _ , p' -,^ .x)
    with (_ , _ , _ , _ , p) , q <- pub th ph
    with r~ <- q (_ , _ , _ , _ , p')
       = r~
  pub (th -, x) (ph -, .x) .fst
    with (_ , _ , _ , _ , p) , _ <- pub th ph
       = _ , _ , _ , _ , p -, x
  pub (th -, x) (ph -, .x) .snd (_ , _ , _ , _ , p' -, .x)
    with (_ , _ , _ , _ , p) , q <- pub th ph
    with r~ <- q (_ , _ , _ , _ , p')
       = r~
  pub [] [] .fst = _ , _ , _ , _ , []
  pub [] [] .snd (_ , _ , _ , _ , []) = r~

  pubU : forall {be ga}{(_ , f , g) : <: be <=_ :* ga <=_ :>}
         {(_ , g0 , f0) (_ , g1 , f1) : <: _<= be :* _<= ga :>}
         {s0 : Sq f g g0 f0} -> Pub s0
      -> (s1 : Sq f g g1 f1)
      -> <: [_-< g0 ]~ g1 :* [_-< s0 .fst ]~ s1 .fst :* [_-< f0 ]~ f1 :>
  pubU (p -^ x) (_ , v -^ .x , w -^ .x)
    with _ , a , b , c <- pubU p (_ , v , w) = _ , a , b -^ x , c
  pubU (p -,^ x) (_ , v -^, .x , w -^ .x)
    with _ , a , b , c <- pubU p (_ , v , w) = _ , a -^ x , b -^ x , c
  pubU (p -^, x) (_ , v -^ .x , w -^, .x)
    with _ , a , b , c <- pubU p (_ , v , w) = _ , a , b -^ x , c -^ x
  pubU (p -, x) (_ , v -^, .x , w -^, .x)
    with _ , a , b , c <- pubU p (_ , v , w) = _ , a -^, x , b -^, x , c -^, x
  pubU (p -, x) (_ , v -, .x , w -, .x)
    with _ , a , b , c <- pubU p (_ , v , w) = _ , a -, x , b -, x , c -, x
  pubU [] (_ , [] , []) = _ , [] , [] , []

  comp : forall {ga xi}(th : ga <= xi)
      -> Bwd X >< \ de -> de <= xi >< \ ph
      -> th /u\ ph
       * Pub (_ , no-< th , no-< ph)
  comp (th -^ x) with _ , _ , u , p <- comp th = _ , _ , u -^, x , p -^, x
  comp (th -, x) with _ , _ , u , p <- comp th = _ , _ , u -,^ x , p -,^ x
  comp [] = _ , _ , [] , []

  _<?_ : forall {ga de}(th : ga <= de){P : X -> Set} -> All P de -> All P ga
  (th -^ x) <? (pz , _) = th <? pz
  (th -, x) <? (pz , p) = (th <? pz) , p
  [] <? <> = <>

  _?<_ : forall {ga de}{P : X -> Set} -> Any P ga -> ga <= de -> Any P de
  px ?< (th -^ x) = ff , (px ?< th)
  (ff , px) ?< (th -, x) = ff , (px ?< th)
  (tt , px) ?< (th -, x) = tt , px

  module _ (eq? : EqDec X) where

    elem? : (x : X)(xz : Bwd X) -> Maybe (x <1 xz)
    elem? x [] = ff , <>
    elem? x (xz -, y) with eq? x y | elem? x xz
    ... | ff , _ | ff , <> = ff , _
    ... | ff , _ | tt , j = tt , j -^ _
    ... | tt , r~ | _ = tt , no -, _

    joint? : (xz yz : Bwd X) -> Maybe <: _<1 xz :* _<1 yz :>
    joint? [] yz = ff , <>
    joint? (xz -, x) yz with elem? x yz | joint? xz yz
    ... | ff , <> | ff , <> = ff , <>
    ... | ff , <> | tt , _ , i , j = tt , _ , i -^ x , j
    ... | tt , j | _ = tt , _ , no -, x , j

  thinEq? : {xi : Bwd X} -> EqDec <: _<= xi :>
  thinEq? (_ , th -^ x) (_ , ph -^ .x) with thinEq? (_ , th) (_ , ph)
  ... | ff , z = ff , \ { r~ -> z r~ }
  ... | tt , r~ = tt , r~
  thinEq? (_ , th -^ x) (_ , ph -, .x) = ff , \ ()
  thinEq? (_ , th -, x) (_ , ph -^ .x) = ff , \ ()
  thinEq? (_ , th -, x) (_ , ph -, .x) with thinEq? (_ , th) (_ , ph)
  ... | ff , z = ff , \ { r~ -> z r~ }
  ... | tt , r~ = tt , r~
  thinEq? (_ , []) (_ , []) = tt , r~
