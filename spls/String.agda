module String where

open import Basics

--open import Agda.Builtin.Bool
--open import Agda.Builtin.List
--open import Agda.Builtin.Char

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringEquality : String → String → Two
  
