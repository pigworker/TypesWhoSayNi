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
open import Stab
open import Par

open TypeTheory

pattern U   = atom 1
pattern PI  = atom 2
pattern SG  = atom 3
pattern CAR = atom 4
pattern CDR = atom 5

ML71 : TypeTheory
ML71 = record
  { formation = [] -,
    --
    --------------------
    --     type U
    record
      { typeSuj   = U
      ; typePrems = []
      }
    -,
    --  type S   x : S |- type T
    --------------------------------
    --     type (PI S \x T)
    record
      { typeSuj   = PI - ??? - \\\ ??? - NIL
      ; typePrems = []
          -, type (_ , cdr (car hole) , oi)
          -, ((cdr (cdr hole) ?- []) !-
               type (_ , cdr (cdr (car (abst hole))) , oi))
      }
    -,
    --  type S   x : S |- type T
    --------------------------------
    --     type (SG S \x T)
    record
      { typeSuj   = SG - ??? - \\\ ??? - NIL
      ; typePrems = []
          -, type (_ , cdr (car hole) , oi)
          -, ((cdr (cdr hole) ?- []) !-
               type (_ , cdr (cdr (car (abst hole))) , oi))
      }
  ; checking =   [] -,
    --     type T
    -------------------
    --     U :> T
    record
      { chkInp   = U
      ; chkSuj   = ???
      ; chkPrems = [] -, type (_ , hole , oi)
      }
    -,
    --     x : S |- T :> t
    ------------------------------
    --     (PI S \x T) :> \x t
    record
      { chkInp   = PI - ??? - \\\ ??? - NIL
      ; chkSuj   = \\\ ???
      ; chkPrems = [] -, (?? car (cdr (car hole)) !-
                          (?? car (cdr (cdr (car (abst hole))))
                             :> (_ , abst hole , oi))) }
    -,
    --     S :> s   T/(s:S) :> t
    --------------------------------------
    --     (SG S \x T) :> (s . t)
    record
      { chkInp   = SG - ??? - \\\ ??? - NIL
      ; chkSuj   = ??? - ???
      ; chkPrems = []
          -, (?? car (cdr (car hole))
               :> (_ , car hole , oi))
          -, ((car (cdr (cdr (car (abst hole)))) ?-
                 ([] -, (?? cdr (cdr hole) :: ?? car (cdr (car hole)))))
               :> (_ , cdr hole , oi))
      }
  ; elimination = [] -,
    --    e <: (PI S \x T)   S :> s
    -----------------------------------
    --    e s <: T/(s:S)
    record
      { trgType   = PI - ??? - \\\ ??? - NIL
      ; elimSuj   = ???
      ; elimPrems = [] -, (?? car (cdr (car hole)) :> (_ , hole , oi))
      ; resType   = car (cdr (cdr (car (abst hole)))) ?- ([] -, (
                      (?? cdr (cdr hole) :: ?? car (cdr (car hole))))) }
    -,
    --    e <: (SG S \x T)
    ---------------------------
    --    e CAR <: S
    record
      { trgType   = SG - ??? - \\\ ??? - NIL
      ; elimSuj   = CAR
      ; elimPrems = []
      ; resType   = ?? car (cdr (car hole)) }
    -,
    --    e <: (SG S \x T)
    -------------------------------
    --    e CDR <: T / e CAR
    record
      { trgType   = SG - ??? - \\\ ??? - NIL
      ; elimSuj   = CDR
      ; elimPrems = []
      ; resType   = car (cdr (cdr (car (abst hole)))) ?-
                      ([] -, target $ essl CAR) }
  ; universe =  [] -, record { uniInp = U ; uniPrems = [] }
  ; reducts =
    [] -,
    ([ (\\\ hole (ze su)) :: (PI - hole ze - \\\ hole (ze su) - NIL) ] (hole ze)
       ~> ((car (car (abst hole)) ?-
            ([] -, (?? cdr hole :: ?? car (cdr (cdr (car hole)))))))
       :: (car (cdr (cdr (cdr (car (abst hole))))) ?-
            ([] -, ((cdr hole ?- []) :: (car (cdr (cdr (car hole))) ?- [])))))
    -,
    ([ (hole ze - hole ze) :: (SG - hole ze - \\\ hole (ze su) - NIL) ] CAR
       ~> (?? car (car (car hole)))
       :: (car (cdr (cdr (car hole))) ?- []))
    -,
    ([ (hole ze - hole ze) :: (SG - hole ze - \\\ hole (ze su) - NIL) ] CDR
       ~> ?? car (car (cdr hole))
       :: (car (cdr (cdr (cdr (car (abst hole))))) ?-
            ([] -,
             ((((car (car (car hole)) ?- []) & (car (car (cdr hole)) ?- [])) ::
               (! 3 &
                (car (cdr (cdr (car hole))) ?- []) &
                (\\
                 (car (cdr (cdr (cdr (car (abst hole))))) ?- ([] -, (# (ze su)))))
                & ! 0))
              $ ! 4))))
  }
