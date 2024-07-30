module MLTTcheat where

open import Basics
open import Eq
open import Bwd
open import All
open import Atom
open import Pat
open import Term
open import Action
open import Thin
open import Deriv
open import Rules
open import Stab
open import Par

open TypeTheory

pattern U   = !!! 1
pattern PI  = !!! 2
pattern SG  = !!! 3
pattern CAR = !!! 4
pattern CDR = !!! 5
pattern U'   = ! 1
pattern PI'  = ! 2
pattern SG'  = ! 3
pattern CAR' = ! 4
pattern CDR' = ! 5


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
      { typeSuj   = PI &&& ??? "S" oi &&& \\\ ??? "T" oi
      ; typePrems = []
          -, type (??s "S" oi)
          -, (("S" ??- []) !- type (??s "T" oi))
      }
    -,
    
    --  type S   x : S |- type T
    --------------------------------
    --     type (SG S \x T)
    record
      { typeSuj   = SG &&& ??? "S" oi &&& \\\ ??? "T" oi
      ; typePrems = []
          -, type (??s "S" oi)
          -, (("S" ??- []) !- type (??s "T" oi))
      }
      
  ; checking =   [] -,
  
    --     type T
    -------------------
    --     U :> T
    record
      { chkInp   = U
      ; chkSuj   = ??? "T" oi
      ; chkPrems = [] -, type (??s "T" oi)
      }
    -,
    
    --     x : S |- T :> t
    ------------------------------
    --     (PI S \x T) :> \x t
    record
      { chkInp   = PI &&& ??? "S" oi &&& \\\ ??? "T" oi
      ; chkSuj   = \\\ ??? "t" oi
      ; chkPrems = [] -, (("S" ??- []) !-
                          (("T" ??- idsb)
                             :> (??s "t" oi))) }
    -,
    
    --     S :> s   T/(s:S) :> t
    --------------------------------------
    --     (SG S \x T) :> (s . t)
    record
      { chkInp   = SG &&& ??? "S" oi &&& \\\ ??? "T" oi
      ; chkSuj   = ??? "s" oi &&& ??? "t" oi
      ; chkPrems = []
          -, (("S" ??- [])
               :> ??s "s" oi)
          -, (("T" ??-
                 ([] -, (("s" ??- []) :: ("S" ??- []))))
               :> (??s "t" oi))
      }
      
  ; elimination = [] -,
    --    e <: (PI S \x T)   S :> s
    -----------------------------------
    --    e s <: T/(s:S)
    record
      { trgType   = PI &&& ??? "S" oi &&& \\\ ??? "T" oi
      ; elimSuj   = ??? "s" oi
      ; elimPrems = [] -, (("S" ??- []) :> (??s "s" oi))
      ; resType   = "T" ??- ([] -, (
                      (("s" ??- []) :: ("S" ??- [])))) }
    -,
    --    e <: (SG S \x T)
    ---------------------------
    --    e CAR <: S
    record
      { trgType   = SG &&& ??? "S" oi &&& \\\ ??? "T" oi
      ; elimSuj   = CAR
      ; elimPrems = []
      ; resType   = "S" ??- [] }
    -,
    --    e <: (SG S \x T)
    -------------------------------
    --    e CDR <: T / e CAR
    record
      { trgType   = SG &&& ??? "S" oi &&& \\\ ??? "T" oi
      ; elimSuj   = CDR
      ; elimPrems = []
      ; resType   = "T" ??- ([] -, target $ CAR') }
      
  ; universe =  [] -, record { uniInp = U ; uniPrems = [] }
  
  ; reducts = [] -,
  
    ([ (\\\ ??? "t" (ze su))
       :: (PI &&& ??? "S" ze &&& \\\ ??? "T" (ze su))
     ] (??? "s" ze)
     ~>
     ("t" ??- ([] -, (("s" ??- []) :: ("S" ??- []))))
     ::
     ("T" ??- ([] -, (("s" ??- []) :: ("S" ??- [])))))
    -,
    ([ (??? "s" ze &&& ??? "t" ze)
       :: (SG &&& ??? "S" ze &&& \\\ ??? "T" (ze su))
     ] CAR
     ~>
     "s" ??- []
     ::
     ("S" ??- []))
    -,
    ([ (??? "s" ze &&& ??? "t" ze)
       :: (SG &&& ??? "S" ze &&& \\\ ??? "T" (ze su))
     ] CDR
     ~>
     ("t" ??- [])
     ::
     (car (cdr (cdr (cdr (\\\ ???)))) ?-
       ([] -,
        ((((car (car (car ???)) ?- []) & (car (car (cdr ???)) ?- [])) ::
          (! 3 &
           (car (cdr (cdr (car ???))) ?- []) &
           \\ (car (cdr (cdr (cdr (\\\ ???)))) ?- ([] -, (# (ze su))))))
         $ ! 4))))
  }
