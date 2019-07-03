------------------------------------------------------------------------------
-----                                                                    -----
-----     Lib.One                                                        -----
-----                                                                    -----
------------------------------------------------------------------------------

module Lib.One where


------------------------------------------------------------------------------
-- the unit type
------------------------------------------------------------------------------

record One : Set where constructor <>

{-
The unit type, One, is named after the number of values in it.

Being a record type, it has an eta law, meaning it needs no dependent
eliminator.
-}
