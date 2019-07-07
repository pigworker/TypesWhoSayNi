------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin.Thinned                                                   -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin.Thinned where

open import Lib.Bwd
open import Lib.Equality
open import Lib.Pi
open import Lib.Index
open import Lib.Sigma
open import Lib.Sum
open import Thin.Data
open import Thin.Triangle

module _ {B : Set} where  -- B is the type of bindings

 open THIN {B}


------------------------------------------------------------------------------
-- Thinnable Stuff
------------------------------------------------------------------------------

{-
A scope-indexed family of sets is Shifty if its data can be shifted by
thinnings in a way that respects identity and composition.
-}

 record Shifty : Set1 where
   field
     Stuff : Scope -> Set
     shift : forall {de} -> Stuff de -> [(de <=_) -:> Stuff ]
     idsh  : forall {de}(s : Stuff de) -> shift s idth ~ s
     cosh  : forall {ga de xi}(s : Stuff ga)(th : ga <= de)(ph : de <= xi) ->
             shift s (th -<- ph) ~ shift (shift s th) ph
 open Shifty

{-
We get a category (in fact, the presheaves on selections, i.e. <= op)
by defining the appropriately respectful notion of action.
-}

 record _-<=>_ (S T : Shifty) : Set where
   field
     act    : [ Stuff S -:> Stuff T ]
     shifty : forall {de ze}(s : Stuff S de)(ph : de <= ze) ->
              act (shift S s ph) ~ shift T (act s) ph
 open _-<=>_

 idSh : forall {S} -> S -<=> S
 act    (idSh {S}) = id
 shifty (idSh {S}) _ _ = r~

 _-<=>-_ : forall {R S T} -> R -<=> S -> S -<=> T -> R -<=> T
 act    (_-<=>-_ {R} {S} {T} f g) = act f - act g
 shifty (_-<=>-_ {R} {S} {T} f g) s ph = 
   act g (act f (shift R s ph)) ~[ act g $~ shifty f s ph >
   act g (shift S (act f s) ph) ~[ shifty g (act f s) ph >
   shift T (act g (act f s)) ph [QED]

{-
The laws clearly hold up to extensional equality of actions.

It is equally clear that (Stuff, act) is a forgetful functor from
Shifty to scope-indexed sets.
-}


------------------------------------------------------------------------------
-- Making anything Shifty
------------------------------------------------------------------------------

{-
Can we turn any old scope-indexed set freely into a Shifty?

Or, categorically, does Stuff have a left adjoint? Of course it does!

All we do is glue a thinning to it. We represent "things from sometime
in the past", and as we move into the future, they just get more in the
past, and the glued on thinning composes on up.
-}

 Free : (Scope -> Set) -> Shifty
 Stuff (Free T) de = < T :* (_<= de) >        -- left Kan extension
 shift (Free T) (t ^ th) ph = t ^ th -<- ph

{-
           ze       t ^ ps  lives in ze
           /|
        ph/ |
         /  |
      de<   |ps     t ^ th  lives in de
         \  |
        th\ |
           \|
           ga       t       lives in ga
-}

 idsh  (Free T) (t ^ th)       = (t ^_) $~ (th <id)
 cosh  (Free T) (t ^ th) ph ps = (t ^_) $~ assoc< th ph ps


------------------------------------------------------------------------------
-- CodeBruijn means Free - Stuff
------------------------------------------------------------------------------

{-
The CodeBruijn operator :< is exactly this glue-on-a-thinning type
constructor.
-}

 infix 7 _:<_
 _:<_ : (Scope -> Set) -> (Scope -> Set)
 _:<_ = Free - Stuff

 infixl 7 _:-_ _:&_
 _:-_ : forall {T de} -> T :< de -> [(de <=_) -:> (T :<_)]
 _:-_ {T} = shift (Free T)


------------------------------------------------------------------------------
-- Naming of parts
------------------------------------------------------------------------------

 module _ {T : Scope -> Set}{de : Scope} where

{-
T :< de is the type of "Ts from some scope before de". They look like

  t ^ th

where t is a thing in some scope ga, called the *support*, and th : ga <= de,
showing how to get from the support of the thing to the scope in which it is
now somehow being referenced.

Note that :- is polymorphic in T and acts only on the thinning, not the
thing. Thinning stuff does not change its support, only its scope.

de Bruijn representations hide thinnings at the leaves of things: when
you decide to use a particular variable, that is when you decide not to
use the others. That's why the decision to use a new variable nowhere
requires a traversal: you have to tell all the leaves to ignore a new
variable.

CodeBruijn representation insists that you discard the option to refer
to things (i.e., kick them out of scope) as near the root as possible.
Thinning thinned things is just composition.
-}

  support : T :< de -> Scope
  support (ga , _) = ga
  
  thing : (t< : T :< de) -> T (support t<)
  thing (t ^ th) = t
  
  thin  : (t< : T :< de) -> support t< <= de
  thin  (t ^ th) = th


------------------------------------------------------------------------------
-- Functoriality in the data
------------------------------------------------------------------------------

 infixl 3 _:$_
 _:$_ : forall {S T} -> [ S -:> T ] -> [(S :<_) -:> (T :<_)]
 f :$ (s ^ th) = f s ^ th


------------------------------------------------------------------------------
-- Free is left adjoint to Stuff
------------------------------------------------------------------------------

{-
Let us now expose the adjunction.
-}

 module Free-|Stuff (S : Scope -> Set)(T : Shifty) where

  forget : (Free S -<=> T) -> [ S -:> Stuff T ]
  forget f s = act f (s ^ idth)
   
  remind : [ S -:> Stuff T ] -> (Free S -<=> T)
  act    (remind g) (s ^ th) = shift T (g s) th
  shifty (remind g) (s ^ th) ph = cosh T (g s) th ph

  regret : (f : Free S -<=> T) ->
    forall {ga}(s< : S :< ga) -> act (remind (forget f)) s< ~ act f s<
  regret f (s ^ th) =
    shift T (act f (s ^ idth)) th  < shifty f (s ^ idth) th ]~
    act f (s ^ idth -<- th)        ~[ act f $~ ((s ^_) $~ id< th) >
    act f (s ^ th)                 [QED]
     
  foment : (g : [ S -:> Stuff T ]) ->
    forall {ga}(s : S ga) -> forget (remind g) s ~ g s
  foment g s = idsh T (g s)

{-
The idea behind codebruijn programming is to separate the *relevant*
component of stuff, making positive use of its whole support, from the
embedding of that support into the scope.
-}


------------------------------------------------------------------------------
-- By the way, Kripke is right adjoint to Stuff (up to extensionality)
------------------------------------------------------------------------------

 module KRIPKE (ext : {S T : Scope -> Set}{f g : [ S -:> T ]}
                  (q : forall {ga}(s : S ga) -> f s ~ g s) ->
                       _~_ {_}{[ S -:> T ]} f g) where
  Kripke : (Scope -> Set) -> Shifty           -- right Kan extension
  Stuff (Kripke T) ga = [(ga <=_) -:> T ]
  shift (Kripke T) k th ph = k (th -<- ph)
  idsh (Kripke T) k = ext \ th -> k $~ id< th
  cosh (Kripke T) k th ph = ext \ ps -> k $~ assoc< th ph ps ~o

  module Stuff-|Kripke (S : Shifty)(T : Scope -> Set) where

    forget : [ Stuff S -:> T ] -> (S -<=> Kripke T)
    act    (forget f) s th = f (shift S s th)
    shifty (forget f) s th = ext \ ph -> f $~ cosh S s th ph ~o

    remind : (S -<=> Kripke T) -> [ Stuff S -:> T ]
    remind g s = act g s idth

    regret : (f : [ Stuff S -:> T ]) ->
      forall {ga}(s : Stuff S ga) -> remind (forget f) s ~ f s
    regret f s = f $~ idsh S s

    foment : (g : S -<=> Kripke T) ->
      forall {ga de}(s : Stuff S ga)(th : ga <= de) ->
      act (forget (remind g)) s th ~ act g s th
    foment g s th rewrite shifty g s th | th <id = r~


------------------------------------------------------------------------------
-- shifting with triangles, i.e., precooked composition
------------------------------------------------------------------------------

 _:&_ : forall {T de ze}{ph : de <= ze}
        (t : T :< de){ps} -> thin t & ph =< ps -> T :< ze
 _:&_ (t ^ th) {ps = ps} v = t ^ ps


------------------------------------------------------------------------------
-- Going under a binder is an important special case.
------------------------------------------------------------------------------

 infixl 7 _:^_
 
 _:^_ : forall {T xz} -> T :< xz -> forall b -> T :< (xz -, b)
 (t ^ th) :^ b = t ^ th -^ b

 thin1 : forall {T xz}(t : T :< xz) b -> t :- idth -^ b ~ t :^ b
 thin1 (t ^ th) b = (t ^_) $~ ((_-^ b) $~ th <id)


