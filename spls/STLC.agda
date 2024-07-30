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
open import Rules
open import Stab
open import Par

open TypeTheory

pattern BASE = !!! 1
pattern BASE' = ! 1
pattern ARROW = !!! 2
pattern ARROW' = ! 2

STLC : TypeTheory
formation STLC = [] -,
  record {
     typeSuj = BASE
   ; typePrems = [] }
  -,
  record {
    typeSuj = ARROW &&& ??? "S" oi &&& ??? "T" oi
  ; typePrems = [] -,
     type (??s "S" oi)
     -,
     type (??s "T" oi) }
checking STLC = [] -,
  record {
    chkInp = ARROW &&& ??? "S" oi &&& ??? "T" oi
  ; chkSuj = \\\ ??? "t" oi
  ; chkPrems = [] -, (("S" ??- []) !-
                   (("T" ??- []) :> ??s "t" oi)) }
elimination STLC = [] -,
  record {
    trgType =  ARROW &&& ??? "S" oi &&& ??? "T" oi
    ; elimSuj = ??? "s" oi
    ; elimPrems = [] -, (("S" ??- []) :> ??s "s" oi)
    ; resType = "T" ??- [] }
universe STLC = []
reducts STLC = [] -,
  ([ (\\\ ??? "t" (ze su))
    :: (ARROW &&& ??? "S" ze &&& ??? "T" ze) ]
    (??? "s" ze)
    ~> "t" ??- ([] -, (("s" ??- []) :: ("S" ??- [])))
    :: ("T" ??- []))
unambiguousFormation STLC = _
unambiguousChecking STLC = _
unambiguousElimination STLC = _
unambiguousUniverse STLC = _

open PARALLEL STLC

foo = confluence


open TYPETHEORY {STLC} {[] , NIL}

-- \ x -> x
example1 : [] != ((ARROW' & BASE' & BASE')
               :> (\\ [ # (oe su) ]))
example1 = chk (oe su)
  (ARROW &&& ((??? BASE') &&& (??? BASE')))
  (\\\ ??? [ # (oe su) ])
  ([] -, extend (thunk var eq))

-- type B -> B
example2 : [] != type (ARROW' & BASE' & BASE')
example2 = type (oe su)
  (ARROW &&& ((??? BASE') &&& (??? BASE')))
  ([] -, type (oe su no) BASE []
      -, type (oe su no) BASE [])

-- (\ x -> x : B -> B) : B -> B
example3 : [] !=
  (((\\ [ # (oe su) ]) ::
    (ARROW' & BASE' & BASE')) <:
    (ARROW' & BASE' & BASE'))
example3 = rad example2 example1

-- f : B -> B |- B -> B :> \ x -> f (f x)
example4 : ([] -, ARROW' & BASE' & BASE')
          != ((ARROW' & BASE' & BASE')
             :> (\\ [ # (oe su no) $
                      [ # (oe su no) $
                        [ # (oe su) ] ] ]))
example4 = chk (oe su)
 (ARROW &&& ((??? BASE') &&& (??? BASE')))
 (\\\ ??? [ # (oe su no) $
                      [ # (oe su no) $
                        [ # (oe su) ] ] ])
 ([] -,
   extend (thunk (elir (ze su)
          (# (oe su no))
          (ARROW &&& ((??? BASE') &&& (??? BASE')))
          (??? [ # (oe su no) $
                        [ # (oe su) ] ])
     var
     ([] -, thunk
        (elir (ze su)
         (# (oe su no))
         (ARROW &&& ((??? BASE') &&& (??? BASE')))
         (??? [ # (oe su) ])
     var
     ([] -, thunk var eq)) eq)) eq))

open STABSBST STLC

example5 = derSbst example4 ([] -, _)
  \ { (() no) ; (x su) → example3 }

-- example5 = example4 [example3 / f]
