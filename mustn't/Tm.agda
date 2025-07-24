module Tm where

open import Basics
open import Bwd
open import Thin
open import Seq

module _ (X : Set) where

  data Sort : Set where
    `    : X -> Sort
    `1   : Sort
    _`*_ : Sort -> Sort -> Sort
    _`>_ : X -> Sort -> Sort

Cx : forall {X} -> Bwd X -> Sort X
Cx []        = `1
Cx (ga -, x) = Cx ga `* ` x

module TM {X : Set}(C : Sort X -> X -> Set) where

  infix 15 _|-_ _|=_
  
  data _|-_ : Bwd X -> Sort X -> Set where
    #       : forall {x} -> [] -, x |- ` x
    _$_     : forall {ga s x} -> C s x -> ga |- s -> ga |- ` x
    <>      : [] |- `1
    _<\_/>_ : forall {s t de ga xi}{th : de <= ga}{ph : xi <= ga}
           -> de |- s -> th /u\ ph -> xi |- t -> ga |- s `* t
    /\      : forall {ga x s} -> ga -, x |- s -> ga |- x `> s
    |<      : forall {ga x s} -> ga      |- s -> ga |- x `> s

  infix 20 _$_

  _|=_ : Bwd X -> Bwd X -> Set
  de |= ga = de |- Cx ga

  wks : forall {ga de} -> ga |= de -> forall x -> ga -, x |= de -, x
  wks sg x = sg <\ io/u\no -^, x /> #
  
  is : forall {ga} -> ga |= ga
  is {[]} = <>
  is {ga -, x} = wks is x

  data _%%_ : forall {be de}
           -> <: be <=_ :* de |=_ :>
           -> <: _|= be :* _<= de :>
           -> Set where
           
    naw : forall {be de xi ze x}
          {lt@(al , th , sg) : <: be <=_ :* de |=_ :>}
          {br@(ep , ta , ph) : <: _|= be :* _<= de :>}
       -> lt %% br
       -> {ps : de <= ze}{ch : xi <= ze}
          (u : ps /u\ ch)(t : xi |- ` x)
          ((om , _) : <: [ ph -< ps ]~_ :>)
       -> (_ , th -^ x , sg <\ u /> t) %% (_ , ta , om)

    aye : forall {be de xi ze x}
          {lt@(al , th , sg) : <: be <=_ :* de |=_ :>}
          {br@(ep , ta , ph) : <: _|= be :* _<= de :>}
       -> lt %% br
       -> {ps : de <= ze}{ch : xi <= ze}
          (u : ps /u\ ch)(t : xi |- ` x)
          ((om , _) : <: [ ph -< ps ]~_ :>)
          ((c , u') : Cop om ch)
       -> (_ , th -, x , sg <\ u /> t) %% (_ , ta <\ u' /> t , c .uuth)

    [] : (_ , [] , <>) %% (_ , <> , [])

  this : forall {ga de}(th : ga <= de)
      -> (_ , th , is) %% (_ , is , th)
  this (th -^ x) = naw (this _) (io/u\no -^, x) # (_ , th -<io -^ x)
  this (th -, x) =
    aye (this _) (io/u\no -^, x) # (_ , th -<io -^ x)
      (io-< th -^, x </\> no-< th -, x , (io/u\no -^, x))
  this [] = []

  selectSub : forall {be de}
           -> (lt : <: be <=_ :* de |=_ :>)
           -> <: lt %%_ :>
  selectSub (_ , th -^ x , sg <\ u /> t)
    with (_ , ta , ph) , s <- selectSub (_ , th , sg)
       = _ , naw s u t (fst (tri _ _))
  selectSub (_ , th -, x , sg <\ u /> t)
    with (_ , ta , ph) , s <- selectSub (_ , th , sg)
       = _ , aye s u t (fst (tri _ _)) (fst (cop _ _))
  selectSub (_ , [] , <>) = _ , []

  roof : forall {be0 be1 de al}
         {th0 : be0 <= al}{th1 : be1 <= al}{sg : de |= al}
         {br0@(ep0 , ta0 , ph0) : <: _|= be0 :* _<= de :>}
      -> (_ , th0 , sg) %% br0
      -> th0 /u\ th1
     -> {br1@(ep1 , ta1 , ph1) : <: _|= be1 :* _<= de :>}
      -> (_ , th1 , sg) %% br1
      -> ph0 /u\ ph1
  roof (naw s0 u0 t (_ , v0)) (u -^, x) (aye s1 _ _ (_ , w0) c) =
    sbtge \ i -> thump (_ ,N- _ ,N- kon _)
      ([] -, ((atom 0 \/ atom 1) \/ atom 2)) [] ([] -, (atom 1 \/ atom 2)) ([] -, 0)
      i
      (<> , ((<> , <> , v0 </\> w0 , roof s0 u s1) , <> , ((_ -<io) </\> (_ -<io)) , u0) , _ , _ -<io)
      <>
      (_ , _ , _ , c)
    >> \ { (ff , tt , z) -> tt , z
         ; (tt , tt , z) -> ff , z
         }
  roof (aye s0 u0 _ (_ , v0) c) (u -,^ x) (naw s1 _ _ (_ , w0)) =
    sbtge \ i -> thump (_ ,N- _ ,N- kon _)
      ([] -, ((atom 0 \/ atom 1) \/ atom 2)) [] ([] -, (atom 0 \/ atom 2)) ([] -, 1)
      i
      (<> , ((<> , <> , v0 </\> w0 , roof s0 u s1) , <> , (_ -<io </\> _ -<io , u0)) , _ , _ -<io)
      <>
      (<> , <> , <> , c)
    >> \ { (ff , tt , z) -> ff , z
         ; (tt , tt , z) -> tt , z
         }
  roof (aye s0 u0 _ (_ , v0) c0) (u -, x) (aye s1 _ _ (_ , w0) c1) =
    sbtge \ i -> thump (_ ,N- _ ,N- kon _)
      ([] -, ((atom 0 \/ atom 1) \/ atom 2)) [] ([] -, (atom 0 \/ atom 2) -, (atom 1 \/ atom 2)) []
      i
      (<> , ((<> , <> , v0 </\> w0 , roof s0 u s1) , <> , (_ -<io </\> _ -<io , u0)) , _ , _ -<io)
      <>
      ((<> , <> , <> , c0) , (<> , <> , c1))
    >> \ { (ff , ff , tt , z) -> ff , z
         ; (ff , tt , z) -> tt , z
         }
  roof [] [] [] = []

  infix 5 [_\\_]~_
  data [_\\_]~_ : forall {ga de s} -> ga |= de -> de |- s -> ga |- s -> Set where

    # : forall {ga x}{t : ga |- ` x} -> [ <> <\ no/u\io /> t \\ # ]~ t

    _$_ : forall {ga de s x}{sg : ga |= de}{t : de |- s}{u : ga |- s}
       -> (c : C s x) -> [ sg \\ t ]~ u
       -> [ sg \\ c $ t ]~ c $ u

    <> : [ <> \\ <> ]~ <>

    pair : forall {be0 be1 de al s0 s1}
         {t0 : be0 |- s0}{t1 : be1 |- s1}
         {th0 : be0 <= al}{th1 : be1 <= al}{sg : de |= al}
         {u : th0 /u\ th1}
         {br0@(ep0 , ta0 , ph0) : <: _|= be0 :* _<= de :>}
         {u0 : ep0 |- s0}
      -> (_ , th0 , sg) %% br0
      -> [ ta0 \\ t0 ]~ u0
      -> {br1@(ep1 , ta1 , ph1) : <: _|= be1 :* _<= de :>}
         {u1 : ep1 |- s1}
      -> (_ , th1 , sg) %% br1
      -> [ ta1 \\ t1 ]~ u1
      -> (u' : ph0 /u\ ph1)
      -> [ sg \\ t0 <\ u /> t1 ]~ u0 <\ u' /> u1
  
    /\ : forall {ga de x s}{sg : ga |= de}{b : de -, x |- s}{b' : ga -, x |- s}
      -> [ wks sg x \\ b ]~ b'
      -> [ sg \\ /\ b ]~ /\ b'

    |< : forall {ga de x s}{sg : ga |= de}{b : de |- s}{b' : ga |- s}
      -> [ sg \\ b ]~ b'
      -> [ sg \\ |< b ]~ |< {x = x} b'

  isNop : forall {ga s}(t : ga |- s) -> [ is \\ t ]~ t
  isNop # = #
  isNop (c $ t) = c $ isNop t
  isNop <> = <>
  isNop (t0 <\ u /> t1) = pair (this _) (isNop t0) (this _) (isNop t1) _
  isNop (/\ t) = /\ (isNop t)
  isNop (|< t) = |< (isNop t)

  is? : forall {ga de}(sg : ga |= de) -> Maybe ((ga ~ de) >< \ { r~ -> sg ~ is })
  is? {ga} {[]} <> = tt , r~ , r~
  is? {ga} {de -, x} (sg <\ u -^, .x /> #) with is? sg | allULeft u
  ... | ff , <> | _ = ff , <>
  ... | tt , r~ , r~ | r~ , (r~ , r~) , r~ = tt , r~ , r~
  is? {ga} {de -, x} (sg <\ u /> t) = ff , <>

  subst subst' : forall {ga de s}(sg : ga |= de)(t : de |- s)
              -> <: [ sg \\ t ]~_ :>
  subst sg t with is? sg
  ... | ff , <> = subst' sg t
  ... | tt , r~ , r~ = _ , isNop t
  subst' (<> <\ u /> t) # with r~ , (r~ , r~) , r~ <- allURite u = _ , #
  subst' sg (c $ t) with _ , t' <- subst' sg t = _ , c $ t'
  subst' <> <> = _ , <>
  subst' sg (t0 <\ u /> t1) = 
    let _ , d0 = selectSub (_ , _ , sg) in
    let _ , d1 = selectSub (_ , _ , sg) in
    let _ , t0' = subst _ t0 in
    let _ , t1' = subst _ t1 in
    _ , (pair d0 t0' d1 t1' (roof d0 u d1))
  subst' sg (/\ t) with _ , t' <- subst' (wks sg _) t = _ , /\ t'
  subst' sg (|< t) with _ , t' <- subst' sg t = _ , |< t'
