module SmolCat where

open import Basics

record SmolCat : Set1 where
  field
    Obj : Set
    Arr : Obj -> Obj -> Set
    iden : {X : Obj} -> Arr X X
    [_-_]~_ : forall {R S T} ->
      Arr R S -> Arr S T -> Arr R T -> Set
    comp : forall {R S T}
      (f : Arr R S)(g : Arr S T) ->
      < [ f - g ]~_ >
    compU : forall {R S T}
      {f : Arr R S}{g : Arr S T}
      (a b : < [ f - g ]~_ >) -> a ~ b
    absl : forall {S T}(f : Arr S T) ->
      [ iden - f ]~ f
    absr : forall {S T}(f : Arr S T) ->
      [ f - iden ]~ f
    asso03 : forall {X0 X1 X2 X3}
      {f01 : Arr X0 X1}{f23 : Arr X2 X3}{f02 : Arr X0 X2}{f13 : Arr X1 X3}
      -> < [ f01 -_]~ f02  *: [_- f23 ]~ f13  >
      -> < [ f01 - f13 ]~_ *: [ f02 - f23 ]~_ >
  infix 25 [_-_]~_
  asso02 : forall {X0 X1 X2 X3}
      {f01 : Arr X0 X1}{f03 : Arr X0 X3}{f12 : Arr X1 X2}{f23 : Arr X2 X3}
      -> < [ f01 -_]~ f03 *: [ f12 - f23 ]~_ >
      -> < [ f01 - f12 ]~_ *: [_- f23 ]~ f03 >
  asso02 {f01 = f01} {f12 = f12} (_ , v , w)
    with _ , a <- comp f01 f12
       | _ , b , c <- asso03 (_ , a , w)
       | r~ <- compU (_ , b) (_ , v)
    = _ , a , c
  asso13 : forall {X0 X1 X2 X3}
      {f01 : Arr X0 X1}{f03 : Arr X0 X3}{f12 : Arr X1 X2}{f23 : Arr X2 X3}
      -> < [ f01 - f12 ]~_ *: [_- f23 ]~ f03 >
      -> < [ f01 -_]~ f03 *: [ f12 - f23 ]~_ >
  asso13 {f12 = f12} {f23} (_ , v , w)
    with _ , a <- comp f12 f23
       | _ , b , c <- asso03 (_ , v , a)
       | r~ <- compU (_ , c) (_ , w)
       = _ , b , a
