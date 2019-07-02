------------------------------------------------------------------------------
-----                                                                    -----
-----     Thin                                                           -----
-----                                                                    -----
------------------------------------------------------------------------------

module Thin where

open import Basics
open import Bwd

module _ {X : Set} where

 infix 4 _<=_ _<-_
 infixl 8 _-^_
 data _<=_ : Bwd X -> Bwd X -> Set where
   [] : [] <= []
   _-,_ : forall {xz yz} ->
     xz <= yz -> forall x ->  xz -, x  <=  yz -, x
   _-^_ : forall {xz yz} ->
     xz <= yz -> forall x ->  xz       <=  yz -, x

 _<-_ : X -> Bwd X -> Set
 x <- xz = [] -, x <= xz

 idth : forall {xz} -> xz <= xz
 idth {[]} = []
 idth {xz -, x} = idth -, x

 _-<-_ : forall {ga0 ga1 ga2} -> ga0 <= ga1 -> ga1 <= ga2 -> ga0 <= ga2
 th       -<- (ph -^ x) = th -<- ph -^ x
 th -, .x -<- (ph -, x) = th -<- ph -, x
 th -^ .x -<- (ph -, x) = th -<- ph -^ x
 []       -<- [] = []

 infixl 8 _-<-_

 antisym : forall {xz yz}(th : xz <= yz)(ph : yz <= xz) ->
   xz ~ yz *\ \ { r~ -> (th ~ idth) * (ph ~ idth) }
 antisym [] [] = r~ , r~ , r~
 antisym (th -, x) (ph -, .x) with antisym th ph
 antisym (.idth -, x) (.idth -, .x)
   | r~ , r~ , r~ = r~ , r~ , r~
 antisym (th -, x) (ph -^ .x) with antisym th ((idth -^ _) -<- ph)
 antisym (th -, x) ((ph -, .x) -^ .x) | r~ , p , ()
 antisym (th -, x) ((ph -^ _) -^ .x) | r~ , p , ()
 antisym (th -^ x) ph with antisym th ((idth -^ _) -<- ph)
 antisym (th -^ x) (ph -, .x) | r~ , p , ()
 antisym (th -^ x) (ph -^ _) | r~ , p , ()

 infixr 6 _<?_
 _<?_ : forall {P xz yz} -> xz <= yz -> Env P yz -> Env P xz
 []        <? [] = []
 (th -, x) <? (pz -, p) = (th <? pz) -, p
 (th -^ x) <? (pz -, p) = th <? pz

 nat<? : forall {P Q : X -> Set}(f : [ P -:> Q ]){xz yz}(th : xz <= yz)
   (pz : Env P yz) -> th <? env f pz ~ env f (th <? pz)
 nat<? f []        []        = r~
 nat<? f (th -, x) (pz -, p) = (_-, f p) $~ nat<? f th pz
 nat<? f (th -^ x) (pz -, p) = nat<? f th pz

 noth : [([] <=_)]
 noth {[]}      = []
 noth {xz -, x} = noth -^ x

 nothU : forall {xz}(th ph : [] <= xz) -> th ~ ph
 nothU [] [] = r~
 nothU (th -^ x) (ph -^ .x) rewrite nothU th ph = r~

 not : forall {iz jz}(th : iz <= jz) -> <(_<= jz)>
 not []        = ! []
 not (th -, x) = ! not th ?? -^ x
 not (th -^ x) = ! not th ?? -, x

 Tri : (forall {iz jz kz}
          (th : iz <= jz)(ph : jz <= kz)(ps : iz <= kz) -> Set) -> Set
 Tri T = forall {iz jz kz}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
           T th ph ps

 infixl 8 _-^,_
 infix 7 _&_=<_
 data _&_=<_ : forall {iz jz kz}
   (th : iz <= jz)(ph : jz <= kz)(ps : iz <= kz) -> Set where
   []    : [] & [] =< []
   _-,_  : Tri \ th ph ps -> th & ph =< ps -> forall x ->
     th -, x & ph -, x =< ps -, x
   _-^,_ : Tri \ th ph ps -> th & ph =< ps -> forall x ->
     th -^ x & ph -, x =< ps -^ x
   _-^_  : Tri \ th ph ps -> th & ph =< ps -> forall x ->
     th & ph -^ x =< ps -^ x

 infixl 8 _-&-_
 _-&-_ : forall {ga0 ga1 ga2}(th : ga0 <= ga1)(ph : ga1 <= ga2) ->
   th & ph =< th -<- ph
 th       -&- (ph -^ x) = th -&- ph -^ x
 th -, .x -&- (ph -, x) = th -&- ph -, x
 th -^ .x -&- (ph -, x) = th -&- ph -^, x
 []       -&- []        = []

 irr& : Tri \ th ph ps -> (v w : th & ph =< ps) -> v ~ w
 irr& [] [] = r~
 irr& (v -, x)  (w -, .x)  rewrite irr& v w = r~
 irr& (v -^, x) (w -^, .x) rewrite irr& v w = r~
 irr& (v -^ x)  (w -^ .x)  rewrite irr& v w = r~

 infix 7 _~&~_
 _~&~_ : Tri \ th ph ps0 -> forall {ps1} ->
   th & ph =< ps0 -> th & ph =< ps1 -> ps0 ~ ps1
 [] ~&~ [] = r~
 v0 -, x  ~&~ v1 -, .x  rewrite v0 ~&~ v1 = r~
 v0 -^, x ~&~ v1 -^, .x rewrite v0 ~&~ v1 = r~
 v0 -^ x  ~&~ v1 -^ .x  rewrite v0 ~&~ v1 = r~

 infix 9 _&id
 _&id : forall {ga de}(th : ga <= de) -> th & idth =< th
 [] &id = []
 (th -, x) &id = th &id -, x
 (th -^ x) &id = th &id -^, x

 id& : forall {ga de}(th : ga <= de) -> idth & th =< th
 id& [] = []
 id& (th -, x) = id& th -, x
 id& (th -^ x) = id& th -^ x

 no& : forall {ga de}(th : ga <= de) -> noth & th =< noth
 no& [] = []
 no& (th -, x) = no& th -^, x
 no& (th -^ x) = no& th -^ x

 assoc03 : forall {ga0 ga1 ga2 ga3}{th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th02 : ga0 <= ga2}{th13 : ga1 <= ga3} ->
   <(th01 &_=< th02) :* (_& th23 =< th13)> ->
   <(th01 & th13 =<_) :* (th02 & th23 =<_)>
 assoc03 (u        ^ v -^ x)  =
   let u ^ v = assoc03 (u ^ v) in   u -^ x  ^ v -^ x
 assoc03 (u -^ .x  ^ v -^, x) =
   let u ^ v = assoc03 (u ^ v) in   u -^ x  ^ v -^, x
 assoc03 (u -^, .x ^ v -, x)  =
   let u ^ v = assoc03 (u ^ v) in   u -^, x ^ v -^, x
 assoc03 (u -, .x  ^ v -, x)  =
   let u ^ v = assoc03 (u ^ v) in   u -, x  ^ v -, x
 assoc03 ([] ^ [])            =     []      ^ []

 assoc02 : forall {ga0 ga1 ga2 ga3}{th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th03 : ga0 <= ga3}{th12 : ga1 <= ga2} ->
   <(th01 &_=< th03) :* (th12 & th23 =<_)> ->
   <(th01 & th12 =<_) :* (_& th23 =< th03)>
 assoc02 (u -^ .x  ^ v -^ x)  =
   let u ^ v = assoc02 (u ^ v) in   u ^     v -^ x
 assoc02 (u -^ .x  ^ v -^, x) =
   let u ^ v = assoc02 (u ^ v) in   u -^ x  ^ v -^, x
 assoc02 (u -^, .x ^ v -, x)  =
   let u ^ v = assoc02 (u ^ v) in   u -^, x ^ v -^, x
 assoc02 (u -, .x  ^ v -, x)  =
   let u ^ v = assoc02 (u ^ v) in   u -, x  ^ v -, x
 assoc02 ([] ^ [])            =     []      ^ []
   
 assoc13 : forall {ga0 ga1 ga2 ga3}{th01 : ga0 <= ga1}{th23 : ga2 <= ga3}
   {th12 : ga1 <= ga2}{th03 : ga0 <= ga3} ->
   <(th01 & th12 =<_) :* (_& th23 =< th03)> ->
   <(th01 &_=< th03) :* (th12 & th23 =<_)>
 assoc13 (u        ^ v -^ x)  =
   let u ^ v = assoc13 (u ^ v) in   u -^ x  ^ v -^ x
 assoc13 (u -^, .x ^ v -^, x) =
   let u ^ v = assoc13 (u ^ v) in   u -^, x ^ v -, x
 assoc13 (u -^ .x  ^ v -^, x) =
   let u ^ v = assoc13 (u ^ v) in   u -^ x  ^ v -^, x
 assoc13 (u -, .x  ^ v -, x)  =
   let u ^ v = assoc13 (u ^ v) in   u -, x  ^ v -, x
 assoc13 ([] ^ [])            =     []      ^ []

 infix 7 _~1&1~_
 _~1&1~_ : Tri \ th0 ph ps -> forall {th1} ->
   th0 & ph =< ps -> th1 & ph =< ps -> th0 ~ th1
 [] ~1&1~ [] = r~
 v0 -, x  ~1&1~ v1 -, .x  rewrite v0 ~1&1~ v1 = r~
 v0 -^, x ~1&1~ v1 -^, .x rewrite v0 ~1&1~ v1 = r~
 v0 -^ x  ~1&1~ v1 -^ .x  rewrite v0 ~1&1~ v1 = r~

 _&<_ : Tri \ th ph ps -> (v : th & ph =< ps) -> YAN (_ <=_) \ ch ->
   th & ph -<- ch =< ps -<- ch
 v &< ch with assoc03 (v ^ _ -&- ch)
 ... | ! u0 , u1 rewrite u1 ~&~ _ -&- ch = u0

 _<&_ : Tri \ th ph ps -> YAN (_<= _) \ ch -> (v : th & ph =< ps) ->
   ch -<- th & ph =< ch -<- ps
 ch <& v with assoc02 (ch -&- _ ^ v)
 ... | ! u0 , u1 rewrite u0 ~&~ ch -&- _ = u1

 _<id : forall {ga de}(th : ga <= de) -> th -<- idth ~ th
 th <id = th -&- idth ~&~ th &id

 id< : forall {ga de}(th : ga <= de) -> idth -<- th ~ th
 id< th = idth -&- th ~&~ id& th

 infix 7 _&<?_
 _&<?_ : forall {P} -> Tri \ th ph ps -> th & ph =< ps ->
   (pz : Env P _) -> th <? ph <? pz ~ ps <? pz
 []      &<? []                             = r~
 t -, x  &<? pz -, p rewrite t &<? pz = r~
 t -^, x &<? pz -, p rewrite t &<? pz = r~
 t -^ x  &<? pz -, p rewrite t &<? pz = r~

 infix 7 _/u\_
 infixl 8 _-,^_
 data _/u\_ : forall {lz mz rz : Bwd X} -> lz <= mz -> rz <= mz -> Set where
   [] : [] /u\ []
   _-,^_ : forall {lz mz rz}{th : lz <= mz}{ph : rz <= mz} ->
     th /u\ ph -> forall x -> th -, x /u\ ph -^ x
   _-^,_ : forall {lz mz rz}{th : lz <= mz}{ph : rz <= mz} ->
     th /u\ ph -> forall x -> th -^ x /u\ ph -, x
   _-,_ : forall {lz mz rz}{th : lz <= mz}{ph : rz <= mz} ->
     th /u\ ph -> forall x -> th -, x /u\ ph -, x

 irr/u\ : forall {lz mz rz : Bwd X}{th : lz <= mz}{ph : rz <= mz}
   (u w : th /u\ ph) -> u ~ w
 irr/u\ []        []                            = r~
 irr/u\ (u -,^ x) (w -,^ .x) rewrite irr/u\ u w = r~
 irr/u\ (u -^, x) (w -^, .x) rewrite irr/u\ u w = r~
 irr/u\ (u -, x)  (w -, .x)  rewrite irr/u\ u w = r~

 module _ {lz mz rz : Bwd X}{th : lz <= mz}{ph : rz <= mz}(u : th /u\ ph)
  where
  u/ : lz <= mz  ;  u\ : rz <= mz
  u/ = th        ;  u\ = ph

 cover1 : forall {lz mz rz : Bwd X}{x}(i : x <- mz)
   {th : lz <= mz}{ph : rz <= mz}(u : th /u\ ph) ->
     <(_& u/ u =< i)> + <(_& u\ u =< i)>
 cover1 (i -, x) (u -,^ .x)   rewrite nothU i noth = inl (! no& _ -, x)
 cover1 (i -, x) (u -^, .x)   rewrite nothU i noth = inr (! no& _ -, x)
 cover1 (i -, x) (u -, .x)    rewrite nothU i noth = inl (! no& _ -, x)
 cover1 (i -^ x) (u -,^ .x)   with cover1 i u
 ... | inl (! v) = inl (! v -^, x)
 ... | inr (! v) = inr (! v -^ x)
 cover1 (i -^ x) (u -^, .x)   with cover1 i u
 ... | inl (! v) = inl (! v -^ x)
 ... | inr (! v) = inr (! v -^, x)
 cover1 (i -^ x) (u -, .x)    with cover1 i u
 ... | inl (! v) = inl (! v -^, x)
 ... | inr (! v) = inr (! v -^, x)

 module _ {iz jz kz}(th : iz <= kz)(ph : jz <= kz) where
  Cop : Set
  Cop = <(iz <=_) :* (_<= kz) :* (jz <=_)> *\ \ { (! th' , ps , ph') ->
        th' & ps =< th * ph' & ps =< ph * th' /u\ ph' }

 infix 7 _/+\_
 _/+\_ : forall {iz jz} -> TAN (iz <=_) (jz <=_) Cop
 []      /+\ []       =     ! []      , []      , []      
 th -, x /+\ ph -, .x = let ! v       , w       , u       = th /+\ ph
                        in  ! v -, x  , w -, x  , u -, x  
 th -, x /+\ ph -^ .x = let ! v       , w       , u       = th /+\ ph
                        in  ! v -, x  , w -^, x , u -,^ x 
 th -^ x /+\ ph -, .x = let ! v       , w       , u       = th /+\ ph
                        in  ! v -^, x , w -, x  , u -^, x 
 th -^ x /+\ ph -^ .x = let ! v       , w       , u       = th /+\ ph
                        in  ! v -^ x  , w -^ x  , u

 copU : forall {iz jz} -> Tan (iz <=_) (jz <=_) \ th  ph  ->
                          Tan (iz <=_) (jz <=_) \ th' ph' ->
                          TAN (th' &_=< th) (ph' &_=< ph) \ {ps'} _ _ ->
        (y : Cop th ph) -> let (! _ , ps , _) , _ , _ , u = y in
        <(u/ u &_=< th')> * <(_& ps' =< ps)> * <(u\ u &_=< ph')>
 copU [] [] (! [] , [] , []) = (! []) , (! []) , (! [])        
 copU (v0 -, x)  (v1 -, .x)  (! v -, .x  , w -, .x  , u -, .x)  =
   let (! a)       , (! b)       , (! c)    = copU v0 v1 (! v , w , u) in 
       (! a -, x)  , (! b -, x)  , (! c -, x)
 copU (v0 -, x)  (v1 -^, .x) (! v -, .x  , w -^, .x , u -,^ .x) = 
   let (! a)       , (! b)       , (! c)    = copU v0 v1 (! v , w , u) in 
       (! a -, x)  , (! b -, x)  , (! c -^, x)
 copU (v0 -^, x) (v1 -, .x)  (! v -^, .x , w -, .x  , u -^, .x) = 
   let (! a)       , (! b)       , (! c)    = copU v0 v1 (! v , w , u) in 
       (! a -^, x) , (! b -, x)  , (! c -, x)
 copU (v0 -^, x) (v1 -^, .x) (! v -^ .x  , w -^ .x  , u)        = 
   let (! a)       , (! b)       , (! c)    = copU v0 v1 (! v , w , u) in 
       (! a -^ x)  , (! b -^, x) , (! c -^ x)
 copU (v0 -^ x)  (v1 -^ .x)  (! v -^ .x  , w -^ .x  , u)        = 
   let a , (! b) , c = copU v0 v1 (! v , w , u) in a , (! b -^ x) , c
 copU (v0 -^, x) (v1 -^, .x) (! v -^, .x , w -^, .x , ())
 copU (v0 -^ x)  (v1 -^ .x)  (! v -^, .x , w -^, .x , ())

 copQ : forall {iz jz} -> Tan (iz <=_) (jz <=_) \ th ph ->
        (c d : Cop th ph) -> c ~ d
 copQ c@((! th0 , _   , ph0) , l0 , r0 , u0)
      d@((! _   , ps1 , _)   , l1 , r1 , u1)
   with copU l1 r1 c | copU l0 r0 d
 ... | (th2 , w0) , (ps2 , w1) , (ph2 , w2)
     | (th3 , t0) , (ps3 , t1) , (ph3 , t2)
   with antisym th2 th3 | antisym ps2 ps3 | antisym ph2 ph3
 ... | r~ , r~ , r~ | r~ , r~ , r~ | r~ , r~ , r~
   with w0 ~&~ th0 &id | w1 ~&~ id& ps1 | w2 ~&~ ph0 &id
 ... | r~ | r~ | r~ rewrite irr& l1 l0 | irr& r1 r0 | irr/u\ u1 u0 = r~

 module _ (T : Bwd X -> Set)(jz : Bwd X) where

  infixl 3 _:<_
  _:<_ : Set
  _:<_ = < T :* (_<= jz) >

 module _ {T : Bwd X -> Set}{jz : Bwd X} where
 
  thing : (x : T :< jz) -> T _
  thing (t ^ th) = t
  thin  : (x : T :< jz) -> _ <= jz
  thin  (t ^ th) = th

 infixl 3 _:$_
 _:$_ : forall {S T} -> [ S -:> T ] -> [(S :<_) -:> (T :<_)]
 f :$ (s ^ th) = f s ^ th

 infixl 7 _:-_ _:^_ _:&_
 _:-_ : forall {S xz}(s : S :< xz) -> [(xz <=_) -:> (S :<_)]
 (s ^ th) :- ph = s ^ th -<- ph
 _:^_ : forall {S xz} -> S :< xz -> forall x -> S :< (xz -, x)
 (t ^ th) :^ x = t ^ th -^ x
 _:&_ : forall {ga T}(t : T :< ga){de}{ph : ga <= de}{ps} ->
        thin t & ph =< ps -> T :< de
 _:&_ (t ^ th) {ps = ps} v = t ^ ps

 thin1 : forall {S xz}(s : S :< xz) x -> s :- idth -^ x ~ s :^ x
 thin1 (s ^ th) x = (s ^_) $~ ((_-^ x) $~ th <id)

 data _!-_ (x : X)(T : Bwd X -> Set)(xz : Bwd X) : Set where
   ll : T (xz -, x) -> (x !- T) xz
   kk : T xz        -> (x !- T) xz

 infixr 4 _\\_
 _\\_ : forall x {T xz} -> T :< xz -, x -> x !- T :< xz
 x \\ t ^ th -, .x = ll t ^ th
 x \\ t ^ th -^ .x = kk t ^ th

 infixl 4 _/*\_
 infix 6 _</_\>_
 record _/*\_ (S T : Bwd X -> Set)(scope : Bwd X) : Set where
   constructor _</_\>_
   field
     {lsupp rsupp} : Bwd X
     {lthin} : lsupp <= scope
     {rthin} : rsupp <= scope
     outl  : S lsupp
     cover : lthin /u\ rthin
     outr  : T rsupp

 module _ {S T : Bwd X -> Set} where

  infixl 2 _/,\_
  _/,\_ : [(S :<_) -:> (T :<_) -:> (S /*\ T :<_)]
  s ^ th /,\ t ^ ph = let (! _ , ps , _) , _ , _ , u = th /+\ ph
                      in  s </ u \> t ^ ps

  data Pr {xz}(s : S :< xz)(t : T :< xz) : S /*\ T :< xz -> Set
    where
    mkPr : {x : <(_ <=_) :* (_<= xz) :* (_ <=_)>} -> let ! th , ps , ph = x in
      th & ps =< thin s -> (u : th /u\ ph) -> ph & ps =< thin t ->
      Pr s t (thing s </ u \> thing t ^ ps)

  covPr : forall {iz jz kz xz}{th : iz <= kz}{ph : jz <= kz}{ps : kz <= xz}
    {s : S iz}{t : T jz}{c : th /u\ ph} ->
    Pr (s ^ th -<- ps) (t ^ ph -<- ps) (s </ c \> t ^ ps)
  covPr = mkPr (_ -&- _) _ (_ -&- _)

  prPr : Tan (S :<_) (T :<_) \ s t -> Pr s t (s /,\ t)
  prPr {_}{s ^ th}{t ^ ph} with th /+\ ph
  prPr {_}{s ^ th}{t ^ ph} | ! v , w , u = mkPr v u w

  pr< : Tether (S :<_) (T :<_) ((S /*\ T) :<_) \ s t st ->
    Pr s t st -> YAN (_ <=_) \ th -> Pr (s :- th) (t :- th) (st :- th)
  pr< (mkPr v u w) th = mkPr (v &< th) u (w &< th)

  prInj : forall {ga}{s s' : S :< ga}{t t' : T :< ga}{st : S /*\ T :< ga} ->
    Pr s t st -> Pr s' t' st -> (s ~ s') * (t ~ t')
  prInj (mkPr lv c rv) (mkPr lu .c ru) rewrite lv ~&~ lu | rv ~&~ ru = r~ , r~

  _~Pr~_ : forall {ga}{s : S :< ga}{t : T :< ga}{st st' : S /*\ T :< ga} ->
     Pr s t st -> Pr s t st' -> st ~ st'
  mkPr lv c rv ~Pr~ mkPr lu b ru with copQ (! lv , rv , c) (! lu , ru , b)
  ... | r~ = r~

 module _ {ga de}(a b : <(ga <=_) :* (_<= de)>) where

  Square : Set
  Square = let th0 ^ ph0 = a ; th1 ^ ph1 = b in
    <(th0 & ph0 =<_) :* (th1 & ph1 =<_)>

 stkSq : Tri \ th0 th1 th -> th0 & th1 =< th ->
         Tri \ ph0 ph1 ph -> ph0 & ph1 =< ph ->
   forall {ps0 ps1 ps2} ->
   Square (ps0 ^ ph0) (th0 ^ ps1) -> Square (ps1 ^ ph1) (th1 ^ ps2) ->
   Square (ps0 ^ ph) (th ^ ps2)
 stkSq x y (v0 ^ v1) (v2 ^ v3)
   with assoc03 (x ^ v3) | assoc03 (v1 ^ v2) | assoc03 (v0 ^ y)
 ... | ch0 , v4 , v5 | ch1 , v6 , v7 | ch2 , v8 , v9
   with v4 ~&~ v6 | v7 ~&~ v9
 ... | r~ | r~ = v8 ^ v5
 

 data Pullback : forall {ga de}{a b : <(ga <=_) :* (_<= de)>} -> Square a b ->
   Set where
   [] : Pullback ([] ^ [])
   _-,_ : forall {ga de}{a b : <(ga <=_) :* (_<= de)>}{s : Square a b} ->
     let v ^ w = s in Pullback s -> (x : X) -> Pullback (v -, x  ^ w -, x)
   _-^,_ : forall {ga de}{a b : <(ga <=_) :* (_<= de)>}{s : Square a b} ->
     let v ^ w = s in Pullback s -> (x : X) -> Pullback (v -^ x  ^ w -^, x)
   _-,^_ : forall {ga de}{a b : <(ga <=_) :* (_<= de)>}{s : Square a b} ->
     let v ^ w = s in Pullback s -> (x : X) -> Pullback (v -^, x ^ w -^ x)
   _-^_ : forall {ga de}{a b : <(ga <=_) :* (_<= de)>}{s : Square a b} ->
     let v ^ w = s in Pullback s -> (x : X) -> Pullback (v -^ x  ^ w -^ x)

 infix 7 _\^/_
 _\^/_ : forall {ga1 ga2} -> TAN (ga1 <=_) (ga2 <=_) \ th1 th2 ->
   <(_<= ga1) :* (_<= ga2)> *\ \ { (ph1 ^ ph2) ->
   Square (ph1 ^ th1) (ph2 ^ th2) *\ Pullback }
 [] \^/ [] = ! ! []
 ph13 -, x \^/ ph23 -, .x = ! ! (ph13 \^/ ph23) ?? ?? -, x
 ph13 -, x \^/ ph23 -^ .x = ! ! (ph13 \^/ ph23) ?? ?? -,^ x
 ph13 -^ x \^/ ph23 -, .x = ! ! (ph13 \^/ ph23) ?? ?? -^, x
 ph13 -^ x \^/ ph23 -^ .x = ! ! (ph13 \^/ ph23) ?? ?? -^ x

 pullU :  forall {ga1 ga2}
  {a b : <(_<= ga1) :* (_<= ga2)>} -> let ph1 ^ ph2 = a ; ch1 ^ ch2 = b in
  {x   : <(ga1 <=_) :* (ga2 <=_)>} -> let th1 ^ th2 = x in
  Square (ch1 ^ th1) (ch2 ^ th2) ->
  {z : Square (ph1 ^ th1) (ph2 ^ th2)} -> Pullback z ->
    <(_& ph1 =< ch1) :* (_& ph2 =< ch2)>
 pullU ([]       ^ [])        []         =                []       ^ []
 pullU (v1 -, x  ^ v2 -, .x)  (p -, .x)  = 
                       let w1 ^ w2 = pullU (v1 ^ v2) p in w1 -, x  ^ w2 -, x
 pullU (v1 -^, x ^ v2 -^, .x) (p -, .x)  =
                       let w1 ^ w2 = pullU (v1 ^ v2) p in w1 -^, x ^ w2 -^, x
 pullU (v1 -^, x ^ v2 -^ .x)  (p -,^ .x) =
                       let w1 ^ w2 = pullU (v1 ^ v2) p in w1 -^ x  ^ w2
 pullU (v1 -^ x  ^ v2 -^, .x) (p -^, .x) =
                       let w1 ^ w2 = pullU (v1 ^ v2) p in w1       ^ w2 -^ x
 pullU (v1 -^ x  ^ v2 -^ .x)  (p -^ .x)  = 
                       let w1 ^ w2 = pullU (v1 ^ v2) p in w1       ^ w2

 infix 7 _<u_
 _<u_ : forall {ga0 ga1 ga}{th0 : ga0 <= ga}{th1 : ga1 <= ga} ->
   th0 /u\ th1 -> forall {de}(ps : ga <= de) ->
   (<(ga0 <=_) :* (_<= de)> * <(ga1 <=_) :* (_<= de)>) *\
   /\ <>\ \ ps0 ph0 -> <>\ \ ps1 ph1 -> ph0 /u\ ph1 *
   (Square (th0 ^ ps) (ps0 ^ ph0) * Square (th1 ^ ps) (ps1 ^ ph1)) *\
   /\ \ s0 s1 -> Pullback s0 * Pullback s1
 u        <u th -^ x = let ! u       , ! a       , b       = u <u th
                       in  ! u -, x  , ! a -^, x , b -^, x
 u -,^ .x <u th -, x = let ! u       , ! a       , b       = u <u th
                       in  ! u -,^ x , ! a -, x  , b -,^ x
 u -^, .x <u th -, x = let ! u       , ! a       , b       = u <u th
                       in  ! u -^, x , ! a -,^ x , b -, x 
 u -, .x  <u th -, x = let ! u       , ! a       , b       = u <u th
                       in  ! u -, x  , ! a -, x  , b -, x
 []       <u []      =     ! []      , ! []      , []

