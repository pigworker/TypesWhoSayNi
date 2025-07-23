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

  infix 10 _|-_
  
  data _|-_ : Bwd X -> Sort X -> Set where
    #       : forall {x} -> [] -, x |- ` x
    _$_     : forall {ga s x} -> C s x -> ga |- s -> ga |- ` x
    <>      : [] |- `1
    _<\_/>_ : forall {s t de ga xi}{th : de <= ga}{ph : xi <= ga}
           -> de |- s -> th /u\ ph -> xi |- t -> ga |- s `* t
    /\      : forall {ga x s} -> ga -, x |- s -> ga |- x `> s
    |<      : forall {ga x s} -> ga      |- s -> ga |- x `> s

  _-|_ : Bwd X -> Bwd X -> Set
  ga -| de = de |- Cx ga

  data _%%_ : forall {be de}
           -> <: be <=_ :* _-| de :>
           -> <: be -|_ :* _<= de :>
           -> Set where
           
    naw : forall {be de xi ze x}
          {lt@(al , th , sg) : <: be <=_ :* _-| de :>}
          {br@(ep , ta , ph) : <: be -|_ :* _<= de :>}
       -> lt %% br
       -> {ps : de <= ze}{ch : xi <= ze}
          (u : ps /u\ ch)(t : xi |- ` x)
          ((om , _) : <: [ ph -< ps ]~_ :>)
       -> (_ , th -^ x , sg <\ u /> t) %% (_ , ta , om)

    aye : forall {be de xi ze x}
          {lt@(al , th , sg) : <: be <=_ :* _-| de :>}
          {br@(ep , ta , ph) : <: be -|_ :* _<= de :>}
       -> lt %% br
       -> {ps : de <= ze}{ch : xi <= ze}
          (u : ps /u\ ch)(t : xi |- ` x)
          ((om , _) : <: [ ph -< ps ]~_ :>)
          ((c , u') : Cop om ch)
       -> (_ , th -, x , sg <\ u /> t) %% (_ , ta <\ u' /> t , c .uuth)

    [] : (_ , [] , <>) %% (_ , <> , [])

  selectSub : forall {be de}
           -> (lt : <: be <=_ :* _-| de :>)
           -> <: lt %%_ :>
  selectSub (_ , th -^ x , sg <\ u /> t)
    with (_ , ta , ph) , s <- selectSub (_ , th , sg)
       = _ , naw s u t (fst (tri _ _))
  selectSub (_ , th -, x , sg <\ u /> t)
    with (_ , ta , ph) , s <- selectSub (_ , th , sg)
       = _ , aye s u t (fst (tri _ _)) (fst (cop _ _))
  selectSub (_ , [] , <>) = _ , []

  roof : forall {be0 be1 de al}
         {th0 : be0 <= al}{th1 : be1 <= al}{sg : al -| de}
         {br0@(ep0 , ta0 , ph0) : <: be0 -|_ :* _<= de :>}
      -> (_ , th0 , sg) %% br0
      -> th0 /u\ th1
     -> {br1@(ep1 , ta1 , ph1) : <: be1 -|_ :* _<= de :>}
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

