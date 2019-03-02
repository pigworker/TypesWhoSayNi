module STLC where

open import Basics
open import Eq
open import Bwd
open import All
open import Atom
open import Pat
open import Term
open import Thin
open import Deriv

open TypeTheory

pattern BASE  = atom 1
pattern ARROW = atom 2

STLC : TypeTheory

formation STLC = [] -,
  record { typeSuj = BASE ; typePrems = [] }
  -,
  record
  { typeSuj = ARROW - hole oi - hole oi - NIL
  ; typePrems =
     [] -, type (_ , cdr (car hole) , oi)
        -, type (_ , cdr (cdr (car hole)) , oi)
  }
  
checking STLC = [] -,
  record
  { chkInp = ARROW - hole oi - hole oi - NIL
  ; chkSuj = \\\ ???
  ; chkPrems = [] -, (?? car (cdr (car hole))
                      !- ((car (cdr (cdr (car hole))) ?- [])
                         :> (_ , abst hole , oi)))
  }
  
elimination STLC = [] -,
  record
  { trgType = ARROW - hole oi - hole oi - NIL 
  ; elimSuj = ???
  ; elimPrems = [] -, (?? car (cdr (car hole))
                       :> (_ , hole , oi))
  ; resType = ?? car (cdr (cdr (car hole))) }
  
universe STLC = []

reducts STLC  = [] -,
  (car (car (abst hole)) ?-
    ([] -, (?? cdr hole ::
            ?? car (cdr (cdr (cdr (car hole)))))))
            
unambiguous STLC = _
