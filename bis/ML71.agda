module ML71 where

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

pattern U = atom 1
pattern PI = atom 2
pattern SG = atom 3
pattern CAR = atom 4
pattern CDR = atom 5

ML71 : TypeTheory

formation ML71 =
  [] -,
  record
    { typeSuj   = U
    ; typePrems = []
    }
  -,
  record
    { typeSuj   = PI - hole oi - \\\ hole oi - NIL
    ; typePrems = []
        -, type (_ , cdr (car hole) , oi)
        -, ((cdr (cdr hole) ?- []) !-
             type (_ , cdr (cdr (car (abst hole))) , oi))
    }
  -,
  record
    { typeSuj   = SG - hole oi - \\\ hole oi - NIL
    ; typePrems = []
        -, type (_ , cdr (car hole) , oi)
        -, ((cdr (cdr hole) ?- []) !-
             type (_ , cdr (cdr (car (abst hole))) , oi))
    }

checking ML71 = 
  [] -,
  record
    { chkInp   = U
    ; chkSuj   = hole oi
    ; chkPrems = [] -, type (_ , hole , oi)
    }
  -,
  record
    { chkInp   = PI - hole oi - \\\ hole oi - NIL
    ; chkSuj   = abst (hole oi)
    ; chkPrems = [] -, ((car (cdr (car hole)) ?- []) !-
                         ((car (cdr (cdr (car (abst hole)))) ?- ([] -, # (oe su)))
                           :> (_ , abst hole , oi))) }
  -,
  record
    { chkInp   = SG - hole oi - \\\ hole oi - NIL
    ; chkSuj   = cons (hole oi) (hole oi)
    ; chkPrems = []
        -, ((car (cdr (car hole)) ?- [])
             :> (_ , car hole , oi))
        -, ((car (cdr (cdr (car (abst hole)))) ?-
               ([] -, ((cdr (cdr hole) ?- []) :: (car (cdr (car hole)) ?- []))))
             :> (_ , cdr hole , oi))
    }
    
elimination ML71 = [] -,
  record
    { trgType   = PI - hole oi - \\\ hole oi - NIL
    ; elimSuj   = hole oi
    ; elimPrems = [] -, ((car (cdr (car hole)) ?- []) :> (_ , hole , oi))
    ; resType   = car (cdr (cdr (car (abst hole)))) ?- ([] -, (
                    (cdr (cdr hole) ?- []) :: (car (cdr (car hole)) ?- []))) }
  -,
  record
    { trgType   = SG - hole oi - \\\ hole oi - NIL
    ; elimSuj   = CAR
    ; elimPrems = []
    ; resType   = car (cdr (car hole)) ?- [] }
  -,
  record
    { trgType   = SG - hole oi - \\\ hole oi - NIL
    ; elimSuj   = CDR
    ; elimPrems = []
    ; resType   = car (cdr (cdr (car (abst hole)))) ?-
                    ([] -, essl (mets (oe su)) $ essl CAR) }


universe ML71 = [] -, record { uniInp = U ; uniPrems = [] }

reducts ML71 = 
  [] -,
  (car (car (abst hole)) ?-
                   ([] -, ((cdr hole ?- []) :: (car (cdr (cdr (car hole))) ?- []))))
  -,
  (car (car (car hole)) ?- [])
  -,
  (car (car (cdr hole)) ?- [])

unambiguous ML71 = _
