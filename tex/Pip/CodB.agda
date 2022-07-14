module CodB where

open import Base

data Nat : Set where
  ze : Nat
  _su : Nat -> Nat
infixl 90 _su
{-# BUILTIN NATURAL Nat #-}

data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _-,_ : forall {n} -> Vec X n -> X -> Vec X (n su)
infixl 90 _-,_

data _<=_ : Nat -> Nat -> Set where
  _fu : forall {n m} -> n <= m -> n    <= m su
  _su : forall {n m} -> n <= m -> n su <= m su
  ze : ze <= ze
infix 80 _<=_
infixl 90 _fu

# : Nat -> Set
# = 1 <=_

no : forall {n} -> ze <= n
no {ze} = ze
no {n su} = no fu

noQ : forall {n}(th ph : ze <= n) -> th ~ ph
noQ (th fu) (ph fu) rewrite noQ th ph = r~
noQ ze ze = r~

io : forall {n} -> n <= n
io {ze} = ze
io {n su} = io su

infix 80 [_^_]~_
data [_^_]~_ : forall {l n m} -> l <= n -> n <= m -> l <= m -> Set where
  _su : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m} -> [ th ^ ph ]~ ps ->
        [ th su ^ ph su ]~ ps su
  _ll : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m} -> [ th ^ ph ]~ ps ->
        [ th fu ^ ph su ]~ ps fu
  _rr : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m} -> [ th ^ ph ]~ ps ->
        [ th ^ ph fu ]~ ps fu
  ze : [ ze ^ ze ]~ ze

tri : forall {l n m}(th : l <= n)(ph : n <= m) -> < [ th ^ ph ]~_ >
tri  th     (ph fu) = let ! v = tri th ph in ! v rr
tri (th fu) (ph su) = let ! v = tri th ph in ! v ll
tri (th su) (ph su) = let ! v = tri th ph in ! v su
tri     ze      ze  =                        !   ze

_^_ : forall {l n m} -> l <= n -> n <= m -> l <= m
th ^ ph = fst (tri th ph)
infixl 90 _^_

antiSym : forall {n m}(th : n <= m)(ph : m <= n)
  -> (n ~ m) >< \ { r~ -> (th ~ io) * (ph ~ io) }
antiSym (th fu) ph with ps , v <- tri (io fu) ph | r~ , r~ , r~ <- antiSym th ps | () <- v
antiSym (th su) (ph fu) with r~ , () , r~ <- antiSym (th fu) ph
antiSym (th su) (ph su) with r~ , r~ , r~ <- antiSym th ph = r~ , r~ , r~
antiSym ze ze = r~ , r~ , r~

degenerate : forall {n m}{th : n <= m}{ph : m <= n}
  -> [ th ^ ph ]~ io
  -> (n ~ m) >< \ { r~ -> (th ~ io) * (ph ~ io) }
degenerate {th = th}{ph = ph} _ with r~ , r~ , r~ <- antiSym th ph = r~ , r~ , r~

ioQ : forall {n}(th ph : n <= n) -> th ~ ph
ioQ th ph with r~ , r~ , r~ <- antiSym th ph = r~

triQ : forall {l n m}{th : l <= n}{ph : n <= m}
  (x y : < [ th ^ ph ]~_ >) -> x ~ y
triQ (! x su) (! y su) with r~ <- triQ (! x) (! y) = r~
triQ (! x ll) (! y ll) with r~ <- triQ (! x) (! y) = r~
triQ (! x rr) (! y rr) with r~ <- triQ (! x) (! y) = r~
triQ (! ze) (! ze) = r~

asso03 : forall {i1 i2}
     {(! th01 , th02) : < _<= i1 *: _<= i2 >}
     {(! th13 , th23) : < i1 <=_ *: i2 <=_ >}
  -> < [ th01 ^_]~ th02 *: [_^ th23 ]~ th13 >
  -> < [ th01 ^ th13 ]~_ *: [ th02 ^ th23 ]~_ >
asso03 (! v    , w rr) = let ! x , y = asso03 (! v , w) in ! x rr , y rr
asso03 (! v rr , w ll) = let ! x , y = asso03 (! v , w) in ! x rr , y ll
asso03 (! v ll , w su) = let ! x , y = asso03 (! v , w) in ! x ll , y ll
asso03 (! v su , w su) = let ! x , y = asso03 (! v , w) in ! x su , y su
asso03 (! ze , ze) = ! ze , ze

asso13 : forall {i0 i2}
     {(! th01 , th12) : < i0 <=_ *: _<= i2 >}
     {(! th03 , th23) : < i0 <=_ *: i2 <=_ >}
  -> < [ th01 ^ th12 ]~_ *: [_^ th23 ]~ th03 >
  -> < [ th01 ^_]~ th03 *: [ th12 ^ th23 ]~_ >
asso13 {_}{_}{(! _ , th12)}{(! _ , th13)} (! v , w)
  with ! x <- tri th12 th13
     | ! y , z <- asso03 (! v , x)
     | r~ <- triQ (! w) (! z)
     = ! y , x

asso02 : forall {i0 i2}
     {(! th01 , th12) : < i0 <=_ *: _<= i2 >}
     {(! th03 , th23) : < i0 <=_ *: i2 <=_ >}
  -> < [ th01 ^_]~ th03 *: [ th12 ^ th23 ]~_ >
  -> < [ th01 ^ th12 ]~_ *: [_^ th23 ]~ th03 >
asso02 {_}{_}{(! th01 , th12)} (! v , w)
  with ! x <- tri th01 th12
     | ! y , z <- asso03 (! x , w)
     | r~ <- triQ (! v) (! y)
     = ! x , z

_^Q : forall {l n m}{th : l <= n}{ph : n <= m}{ps : l <= m} ->
  [ th ^ ph ]~ ps -> (th ^ ph) ~ ps
v ^Q with r~ <- triQ (tri _ _) (! v) = r~

no^ : forall {n m}(th : n <= m) -> [ no ^ th ]~ no
no^ (th fu) = no^ th rr
no^ (th su) = no^ th ll
no^ ze = ze

io^ : forall {n m}(th : n <= m) -> [ io ^ th ]~ th
io^ (th fu) = io^ th rr
io^ (th su) = io^ th su
io^ ze = ze

infixl 90 _^io
_^io : forall {n m}(th : n <= m) -> [ th ^ io ]~ th
th fu ^io = th ^io ll
th su ^io = th ^io su
ze ^io = ze

data _/u\_ : forall {n m l} -> n <= m -> l <= m -> Set where
  _su : forall {n m l}{th : n <= m}{ph : l <= m} -> th /u\ ph ->
         th su /u\ ph su
  _ll : forall {n m l}{th : n <= m}{ph : l <= m} -> th /u\ ph ->
         th su /u\ ph fu
  _rr : forall {n m l}{th : n <= m}{ph : l <= m} -> th /u\ ph ->
         th fu /u\ ph su
  ze  : ze /u\ ze
infixl 90 _ll _rr
infix 80 _/u\_

copQ : forall {n m l}{th : n <= m}{ph : l <= m}(u w : th /u\ ph) -> u ~ w
copQ (u su) (w su) with r~ <- copQ u w = r~
copQ (u ll) (w ll) with r~ <- copQ u w = r~
copQ (u rr) (w rr) with r~ <- copQ u w = r~
copQ ze ze = r~

record InjDiag {m i j}(th : i <= m)(ph : j <= m) : Set where
  constructor _/!\_
  field
    {meet} : Nat
    {linj} : i <= meet
    {rinj} : j <= meet
    {slak} : meet <= m
    ltri   : [ linj ^ slak ]~ th
    rtri   : [ rinj ^ slak ]~ ph
open InjDiag public
infix 60 _/!\_

_=InjDiag=>_ : forall {m i j}{th : i <= m}{ph : j <= m}
            -> InjDiag th ph -> InjDiag th ph -> Set
A =InjDiag=> B =
  < [ linj A ^_]~ linj B *: [_^ slak B ]~ slak A *: [ rinj A ^_]~ rinj B >

CopDiag : forall {m i j}(th : i <= m)(ph : j <= m) -> Set
CopDiag th ph = InjDiag th ph >< \ C -> linj C /u\ rinj C

cop : forall {m i j}(th : i <= m)(ph : j <= m) -> CopDiag th ph
cop (th fu) (ph fu) = let v /!\ w , u = cop th ph in v rr /!\ w rr , u
cop (th fu) (ph su) = let v /!\ w , u = cop th ph in v ll /!\ w su , u rr
cop (th su) (ph fu) = let v /!\ w , u = cop th ph in v su /!\ w ll , u ll
cop (th su) (ph su) = let v /!\ w , u = cop th ph in v su /!\ w su , u su
cop ze ze = ze /!\ ze , ze

copU : forall {m i j}{th : i <= m}{ph : j <= m}
     (C : CopDiag th ph)
  -> (D : InjDiag th ph) -> fst C =InjDiag=> D
copU (v0 su /!\ w0 su , u0 su) (v1 su /!\ w1 su) =
  let ! x , y , z = copU (v0 /!\ w0 , u0) (v1 /!\ w1) in
      ! x su , y su , z su
copU (v0 su /!\ w0 ll , u0 ll) (v1 su /!\ w1 ll) = 
  let ! x , y , z = copU (v0 /!\ w0 , u0) (v1 /!\ w1) in
      ! x su , y su , z ll
copU (v0 ll /!\ w0 su , u0 rr) (v1 ll /!\ w1 su) = 
  let ! x , y , z = copU (v0 /!\ w0 , u0) (v1 /!\ w1) in
      ! x ll , y su , z su
copU (v0 rr /!\ w0 rr , u0) (v1 ll /!\ w1 ll) = 
  let ! x , y , z = copU (v0 /!\ w0 , u0) (v1 /!\ w1) in
      ! x rr , y ll , z rr
copU (v0 rr /!\ w0 rr , u0) (v1 rr /!\ w1 rr) = 
  let ! x , y , z = copU (v0 /!\ w0 , u0) (v1 /!\ w1) in
      ! x , y rr , z
copU (ze /!\ ze , ze) (ze /!\ ze) = ! ze , ze , ze

CopQ : forall {m i j}{th : i <= m}{ph : j <= m}
  (C D : CopDiag th ph) -> C ~ D
CopQ C@(cv /!\ cw , cu) D@(dv /!\ dw , du)
  with ch , a , v , b <- copU C (fst D)
     | om , c , w , d <- copU D (fst C)
     | r~ , r~ , r~ <- antiSym ch om
     | r~ , r~ , r~ <-
       triQ (! a) (! _ ^io) , triQ (! v) (! io^ _) , triQ (! b) (! _ ^io)
     | r~ , r~ , r~ <- triQ (! cv) (! dv) , triQ (! cw) (! dw) , copQ cu du
     = r~

dupLemma : forall {m}{(! th) (! ph) (! ps) : < _<= m >}
     ((A , _) : CopDiag th ph)
     ((B , _) : CopDiag th ps)
     ((C , _) : CopDiag ph ps)
  -> slak A /u\ ps
  -> slak B /u\ slak C
dupLemma AC (B@(vB0 /!\ vB1) , uB) (C@(vC0 /!\ vC1) , uC) u
  with wB /!\ wC , u' <- cop (slak B) (slak C)
     | ! _ , v1 <- asso02 (! vB0 , wB)
     | ! _ , v3 <- asso02 (! vB1 , wB)
     | ! _ , v5 <- asso02 (! vC0 , wC)
  -- | ! v6 , v7 <- asso02 (! vC1 , wC)
     | ! _ , w1 , _ <- copU AC (v1 /!\ v5)
     | ! _ , w4 , _ <- copU (_ ^io /!\ _ ^io , u) (w1 /!\ v3)
     | r~ , r~ , r~ <- degenerate w4
     | r~ , r~ <- triQ (! wC) (! _ ^io) , triQ (! wB) (! _ ^io)
  = u'

rotLemma : forall {m}{(! th) (! ph) (! ps) : < _<= m >}
     ((A , _) : CopDiag th ph)
     ((C , _) : CopDiag ph ps)
  -> slak A /u\ ps
  -> th /u\ slak C
rotLemma {_}{(! th)}  AC@(A@(vA0 /!\ vA1) , uA) (C@(vC0 /!\ vC1) , uC) u
  with w0 /!\ w1 , u' <- cop th (slak C)
     | ! v0 , v1 <- asso02 (! vC0 , w1)
     | ! v2 , v3 <- asso02 (! vC1 , w1)
     | ! w2 , w3 , w4 <- copU AC (w0 /!\ v1)
     | ! w5 , w6 , w7 <- copU (_ ^io /!\ _ ^io , u) (w3 /!\ v3)
     | r~ , r~ , r~ <- degenerate w6
     | r~ , r~ <- triQ (! w0 ) (! _ ^io) , triQ (! w1) (! _ ^io)
     = u'

swap : forall {n m l}{th : n <= m}{ph : l <= m}(u : th /u\ ph) -> ph /u\ th
swap (u su) = swap u su
swap (u ll) = swap u rr
swap (u rr) = swap u ll
swap ze = ze

lll : forall {n} -> io {n} /u\ no {n}
lll {ze}   = ze
lll {n su} = lll ll

rrr : forall {n} -> no {n} /u\ io {n}
rrr = swap lll

allRight : forall {n m}{th : 0 <= m}{ph : n <= m}
  (u : th /u\ ph) -> (n ~ m) >< \ { r~ -> (th ~ no) >< \ { r~ -> (ph ~ io) >< \ { r~ -> u ~ rrr }}}
allRight (u rr) with r~ , r~ , r~ , r~ <- allRight u = r~ , r~ , r~ , r~
allRight ze = r~ , r~ , r~ , r~

allRightQ : forall {m} -> allRight (rrr {m}) ~ (r~ , r~ , r~ , r~)
allRightQ {ze} = r~
allRightQ {m su} rewrite allRightQ {m} = r~

module _ {n m l}{th : n <= m}{ph : l <= m}(u : th /u\ ph) where
  luth = th
  ruth = ph

infixl 90 _<?_
_<?_ : forall {X}{i j} -> i <= j -> Vec X j -> Vec X i
th fu <? (xs -, x) = th <? xs
th su <? (xs -, x) = th <? xs -, x
ze <? xs = []

only : forall {X} -> Vec X 1 -> X
only (_ -, x) = x

_-?_ : forall {X n}(i : # n) -> Vec X n -> X
i -? xs = only (i <? xs)

{-
rot : forall {m}{(k , th0) (n , th1) : < _<= m >} -> th0 /u\ th1
   -> {(i , ph0) (j , ph1) : < _<= k >} -> ph0 /u\ ph1
   -> (< _<= m >) >< \ (l , ps) -> < [ ph0 ^ th0 ]~_ *: _/u\ ps >
    * j <= l >< \ ch0
    -> < [ ph1 ^ th0 ]~_ *: [ ch0 ^ ps ]~_ > * < ch0 /u\_ *: [_^ ps ]~ th1 >
rot (u su) (v su) = let ! (! a , b) , ! (! c , d) , ! e , f = rot u v in
                   ! (! a su , b su) , ! (! c su , d su) , ! e su , f su
rot (u su) (v ll) = let ! (! a , b) , ! (! c , d) , ! e , f = rot u v in
                   ! (! a su , b su) , ! (! c ll , d ll) , ! e rr , f su
rot (u su) (v rr) = let ! (! a , b) , ! (! c , d) , ! e , f = rot u v in
                   ! (! a ll , b rr) , ! (! c su , d su) , ! e su , f su
rot (u ll) (v su) = let ! (! a , b) , ! (! c , d) , ! e , f = rot u v in
                   ! (! a su , b su) , ! (! c su , d su) , ! e ll , f ll
rot (u ll) (v ll) = let ! (! a , b) , ! (! c , d) , ! e , f = rot u v in
                   ! (! a su , b ll) , ! (! c ll , d rr) , ! e , f rr
rot (u ll) (v rr) = let ! (! a , b) , ! (! c , d) , ! e , f = rot u v in
                   ! (! a ll , b rr) , ! (! c su , d su) , ! e ll , f ll
rot (u rr) v = let ! (! a , b) , ! (! c , d) , ! e , f = rot u v in
                   ! (! a rr , b rr) , ! (! c rr , d ll) , ! e rr , f su
rot ze ze = ! (! ze , ze) , ! (! ze , ze) , ! ze , ze

rot-lll : forall {m}{(k , th0) (n , th1) : < _<= m >}(u : th0 /u\ th1)
  -> rot u lll ~ ! (! io^ _ , u) , ! ( ! no^ _ , no^ _) , ! swap lll , io^ _
rot-lll (u su) rewrite rot-lll u = r~
rot-lll (u ll) rewrite rot-lll u = r~
rot-lll (u rr) rewrite rot-lll u = r~
rot-lll ze = r~

rotlll : forall {m}
   -> {(i , ph0) (j , ph1) : < _<= m >}(u : ph0 /u\ ph1)
   -> rot (lll {m}) u ~ (! ( ! _ ^io , u) , ! (! _ ^io , io^ _) , ! lll , no^ _)
rotlll (u su) rewrite rotlll u = r~
rotlll (u ll) rewrite rotlll u = r~
rotlll (u rr) rewrite rotlll u = r~
rotlll ze = r~

rotrrr : forall {m}
   -> rot (rrr {m}) ze ~ (! ( ! io^ no , rrr) , ! (! io^ no , no ^io) , ! rrr , io^ _)
rotrrr {ze} = r~
rotrrr {m su} rewrite rotrrr {m} = r~

rot-rrr : forall {m}{(k , th0) (n , th1) : < _<= m >}(u : th0 /u\ th1)
  -> rot u (swap lll) ~ ! (! no^ _ , rrr) , ! ( ! io^ _ , _ ^io) , ! u , _ ^io
rot-rrr (u su) rewrite rot-rrr u = r~
rot-rrr (u ll) rewrite rot-rrr u = r~
rot-rrr (u rr) rewrite rot-rrr u = r~
rot-rrr ze = r~
-}

_^^_ : (Nat -> Set) -> (Nat -> Set)
P ^^ m = < P *: _<= m >

