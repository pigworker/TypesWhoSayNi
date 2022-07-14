module Fmla where

open import Base
open import CodB

data Sort : Set where
  chk syn : Sort
  sub : Nat -> Sort
  _su : Sort -> Sort
  _**_ : Sort -> Sort -> Sort
infixr 80 _**_

module TM (M : Nat -> Set) where

  data _-<_> : Sort -> Sort -> Set where
    em : chk -< syn >
    pi : chk -< chk ** (chk su) >
    la : chk -< chk su >
    me : forall {m} -> M m -> chk -< sub m >
    ra : syn -< chk ** chk >
    ap : syn -< syn ** chk >
    sb : forall {m} -> sub (m su) -< sub m ** syn >
    kk : forall {s} -> (s su) -< s >

  infix 60 _-!_
  data _-!_ : Sort -> Nat -> Set where
    _$_ : forall {n t s} -> t -< s > -> s -! n -> t -! n
    ty : chk -! 0
    va : syn -! 1
    ze : sub 0 -! 0
    bb : forall {n s} -> s -! n su -> s su -! n
    pp : forall {i j n s t}{th : i <= n}{ph : j <= n} ->
           s -! i -> th /u\ ph -> t -! j -> s ** t -! n
  infixr  90 _$_

module _ {M : Nat -> Set} where
  open TM M

  infix 80 _=>_
  _=>_ : Nat -> Nat -> Set
  m => n = sub m -! n

  infix 80 _%%_
  data _%%_ : forall {i k}
    -> < i <=_ *: _=> k > -> < i =>_ *: _<= k >
    -> Set where
    naw : forall {i k k0}
          {lt@(! th , sg) : < i <=_ *: _=> k0 >}
          {br@(! ta , ph) : < i =>_ *: _<= k0 >}
       -> lt %% br
       -> {ps : k0 <= k}{(k1 , e , ph1) : syn -!_ ^^ k}
       -> {u : ps /u\ ph1}
       -> ((ph0 , _) : < [ ph ^ ps ]~_ >)
       -> (! th fu , sb $ pp sg u e) %% (! ta , ph0)
    aye : forall {i k k0}
          {lt@(! th , sg) : < i <=_ *: _=> k0 >}
          {br@(! ta , ph) : < i =>_ *: _<= k0 >}
       -> lt %% br
       -> {ps : k0 <= k}{(k1 , e , ph1) : syn -!_ ^^ k}
       -> {u : ps /u\ ph1}
       -> ((ph0 , _) : < [ ph ^ ps ]~_ >)
       -> ((C , u') : CopDiag ph0 ph1)
       -> (! th su , sb $ pp sg u e) %% (! sb $ pp ta u' e , slak C)
    ze : (! ze , ze) %% (! ze , ze)

  module _ {i k}{lt : < i <=_ *: _=> k >}{br : < i =>_ *: _<= k >}
           (x : lt %% br) where
    l%% = fst (snd lt)
    t%% = snd (snd lt)
    b%% = fst (snd br)
    r%% = snd (snd br)

  sel : forall {i k}(lt : < i <=_ *: _=> k >)
     -> < i =>_ *: _<= k > >< \ br -> lt %% br
  sel (! th fu , sb $ pp sg u e)
    with (! ta , ph) , a <- sel (! th , sg)
       | ph0 , v <- tri ph (luth u)
       = ! naw a (! v)
  sel (! th su , sb $ pp sg u e)
    with (! ta , ph) , a <- sel (! th , sg)
       | ph0 , v <- tri ph (luth u)
       | v1 /!\ v2 , w <- cop ph0 (ruth u)
    = ! aye a (! v) (v1 /!\ v2 , w)
  sel (! ze , ze) = ! ze

  selQ : forall {i k}{lt : < i <=_ *: _=> k >}
     -> (x y : < i =>_ *: _<= k > >< \ br -> lt %% br) -> x ~ y
  selQ (! naw x (! a)) (! naw y (! b))
    with r~ <- selQ (! x) (! y)
       | r~ <- triQ (! a) (! b)
       = r~
  selQ (! aye x (! a) A) (! aye y (! b) B)
    with r~ <- selQ (! x) (! y)
       | r~ <- triQ (! a) (! b)
       | r~ <- CopQ A B
       = r~
  selQ (! ze) (! ze) = r~

  pastev : forall {i i' k k'}
    {(j , th , ph) : < i <=_ *: _<= k >}
    {(j' , th' , ph') : < i' <=_ *: _<= k' >}
    {rh : i => i'}{sg : j => j'}{ta : k => k'}
    -> (! th , sg) %% (! rh , th')
    -> (! ph , ta) %% (! sg , ph')
    -> ((ps , _) : < [ th ^ ph ]~_ >)
    -> ((ps' , _) : < [ th' ^ ph' ]~_ >)
    -> (! ps , ta) %% (! rh , ps')
  pastev x (naw y (! a)) (! v rr) (! w) = let ! b , c = asso02 (! w , a) in
    naw (pastev x y (! v) (! b)) (! c)
  pastev (naw x (! b)) (aye y (! a) (l /!\ r , u)) (! v ll) (! w)
    with ! c , d <- asso13 (! b , w)
       | r~ <- triQ (! l) (! d)
       | ! e , f <- asso02 (! c , a)
    =  naw (pastev x y (! v) (! e)) (! f)
  pastev (aye x (! b) (l1 /!\ r1 , u1)) (aye y (! a) (l2 /!\ r2 , u2)) (! v su) (! w)
    with ! c , d <- asso03 (! b , l2)
       | ! e , f <- asso02 (! c , a)
       | ! g , h <- asso13 (! l1 , d)
       | ! i , j <- asso13 (! r1 , r2)
       | r~ , r~ <- triQ (! w) (! h) , triQ (! w) (! j)
    = aye (pastev x y (! v) (! e)) (! f) (g /!\ i , u1)
  pastev ze ze (! ze) (! ze) = ze

  splitv : forall {i j k}{th : i <= j}{ph : j <= k}{ps : i <= k}
    -> [ th ^ ph ]~ ps
    -> forall {i' k'}{rh : i => i'}{ta : k => k'}{ps' : i' <= k'}
    -> (! ps , ta) %% (! rh , ps')
    -> < i' <=_ *: _<= k' *: j =>_ > >< \ (! th' , ph' , sg)
    -> (! th , sg) %% (! rh , th')
     * (! ph , ta) %% (! sg , ph')
     * [ th' ^ ph' ]~ ps'
  splitv {th = th} {ph} v {ta = ta} x
    with (! sg , ph') , z <- sel (! ph , ta)
       | (! rh' , th') , y <- sel (! th , sg)
       | ! w <- tri th' ph'
       | x' <- pastev y z (! v) (! w)
       | r~ <- selQ (! x) (! x')
       = ! y , z , w

  roof : forall {i0 i1 j k l0 l1}
       {th0 : i0 <= j}{th1 : i1 <= j}(u : th0 /u\ th1)
       {sg : j => k}
       {sg0 : i0 => l0}{ph0 : l0 <= k} -> (! th0 , sg) %% (! sg0 , ph0)
    -> {sg1 : i1 => l1}{ph1 : l1 <= k} -> (! th1 , sg) %% (! sg1 , ph1)
    -> ph0 /u\ ph1
  roof (u su) (aye x0 {u = u0} (! v0) A) (aye x1 (! v3) B)
    = dupLemma (v0 /!\ v3 , roof u x0 x1) A B u0
  roof (u ll) (aye x0 {u = u0} (! v0) A) (naw x1 (! v3))
    = swap (rotLemma (v3 /!\ v0 , swap (roof u x0 x1)) A u0) 
  roof (u rr) (naw x0 (! v0)) (aye x1 {u = u1} (! v3) B)
    = rotLemma (v0 /!\ v3 , roof u x0 x1) B u1
  roof ze ze ze = ze

  infix 80 [_/_]~_
  data [_/_]~_ : forall {m n s} -> s -! m -> m => n -> s -! n -> Set where
    _$_ : forall {o i m n}(c : o -< i >){t : i -! m}{sg : m => n}{t'}
       -> [ t / sg ]~ t' -> [ c $ t / sg ]~ c $ t'
    ty : [ ty / ze ]~ ty
    va : forall {n}{e : syn -! n}
      -> [ va / sb $ pp ze rrr e ]~ e
    ze : [ ze / ze ]~ ze
    bb : forall {m n s}{t : s -! m su}{t'}{sg : m => n}
      -> [ t / sb $ pp sg (lll rr) va ]~ t' -> [ bb t / sg ]~ bb t'
    pp : forall {m n s0 s1}
         {(! t0 , th0) : s0 -!_ ^^ m}
         {(! t1 , th1) : s1 -!_ ^^ m}
         {u : th0 /u\ th1}
         {sg : m => n}
         {(! t0' , ph0) : s0 -!_ ^^ n}
         {(! t1' , ph1) : s1 -!_ ^^ n}
         {sg0 sg1} ->
         (! th0 , sg) %% (! sg0 , ph0) ->
         [ t0 / sg0 ]~ t0' ->
         (! th1 , sg) %% (! sg1 , ph1) ->
         [ t1 / sg1 ]~ t1' ->
         (u' : ph0 /u\ ph1) ->
         [ pp t0 u t1 / sg ]~ pp t0' u' t1'

  module _ {m n s}{f : s -! m}{b : m => n}{c : s -! n}(c : [ f / b ]~ c) where
    f/ = f
    b/ = b
    c/ = c

  sbst : forall {m n s}(t : s -! m)(sg : m => n)
      -> < [ t / sg ]~_ >
  sbst (x $ t) sg = let ! t' = sbst _ _ in ! x $ t'
  sbst ty ze = ! ty
  sbst va (sb $ pp ze u e) with r~ , r~ , r~ , r~ <- allRight u = ! va
  sbst ze ze = ! ze
  sbst (bb t) sg = let ! t' = sbst _ _ in ! bb t'
  sbst (pp t0 u t1) sg = 
    let (! sg0 , ph0) , x0 = sel _ in let ! t0' = sbst _ _ in
    let (! sg1 , ph1) , x1 = sel _ in let ! t1' = sbst _ _ in
    ! pp x0 t0' x1 t1' (roof u x0 x1) 

  _/_ : forall {m n s}(t : s -! m)(sg : m => n) -> s -! n
  t / sg = fst (sbst t sg)

  sbstQ : forall {m n s}{t : s -! m}{sg : m => n}(x y : < [ t / sg ]~_ >) -> x ~ y
  sbstQ (! (c $ x)) (! (.c $ y)) with r~ <- sbstQ (! x) (! y) = r~
  sbstQ (! ty) (! ty) = r~
  sbstQ (! va) (! va) = r~
  sbstQ (! ze) (! ze) = r~
  sbstQ (! bb x) (! bb y) with r~ <- sbstQ (! x) (! y) = r~
  sbstQ (! pp x0 x1 x2 x3 ux) (! pp y0 y1 y2 y3 uy)
    with r~ <- selQ (! x0) (! y0)
       | r~ <- sbstQ (! x1) (! y1)
       | r~ <- selQ (! x2) (! y2)
       | r~ <- sbstQ (! x3) (! y3)
       | r~ <- copQ ux uy
    = r~

  is : forall {n} -> sub n -! n
  is {ze} = ze
  is {n su} = sb $ pp is (lll rr) va

  iosel : forall {m n}(sg : m => n) -> (! io , sg) %% (! sg , io)
  iosel (sb $ pp sg u e) = aye (iosel sg) (! io^ _) (_ ^io /!\  _ ^io , u)
  iosel ze = ze

  nosel : forall {m n}(sg : m => n) -> (! no , sg) %% (! ze , no)
  nosel (sb $ pp sg u e) = naw (nosel sg) (! no^ _)
  nosel ze = ze

  selis : forall {n m}(th : n <= m) -> (! th , is) %% (! is , th)
  selis (th fu) = naw (selis th) (! th ^io rr)
  selis (th su) = aye (selis th) (! th ^io rr) (io^ th ll /!\ no^ _ su , lll rr)
  selis ze = ze

  is/_ : forall {m n}(sg : m => n) -> [ is / sg ]~ sg
  is/ (sb $ pp sg u e) = sb $ pp
    (naw (iosel sg) (! io^ _)) (is/ sg)
    (aye (nosel sg) (! no^ _) (no^ _ /!\ io^ _ , rrr)) va
    u
  is/ ze = ze

  _/is : forall {m s}(t : s -! m) -> [ t / is ]~ t
  (c $ t) /is = c $ (t /is)
  ty /is = ty
  va /is = va
  ze /is = ze
  bb t /is = bb (t /is)
  pp t0 u t1 /is = pp (selis (luth u)) (t0 /is) (selis (ruth u)) (t1 /is) u

  pasteh : forall {i j k i' j' k'}
    {rh  : i  => j }{sg  : j  => k }{ta  : i  => k }
    {rh' : i' => j'}{sg' : j' => k'}{ta' : i' => k'}
    {th : i <= i'}{ph : j <= j'}{ps : k <= k'}
    -> (! th , rh') %% (! rh , ph)
    -> [ rh' / sg' ]~ ta'
    -> (! ph , sg') %% (! sg , ps)
    -> [ rh / sg ]~ ta
    -> (! th , ta') %% (! ta , ps)
  pasteh (naw x (! a)) (.sb $ pp x0 v0 x1 v1 u) y w
    with ! b , c , d <- splitv a y
       | r~ <- selQ (! x0) (! c)
       = naw (pasteh x v0 b w) (! d)
  pasteh (aye x (! a) (l /!\ r , u0)) (.sb $ pp x0 v0 x1 v1 u)
         y                            (.sb $ pp y0 w0 y1 w1 u1)
    with y2 <- pastev y0 y (! l) (tri _ _)
       | ! y3 , y4 , b <- splitv a y2
       | r~ <- selQ (! x0) (! y4)
       | y6 <- pastev y1 y (! r) (tri _ _)
       | r~ <- selQ (! x1) (! y6)
       | r~ <- sbstQ (! v1) (! w1)
       = aye (pasteh x v0 y3 w0) (! b) (snd (tri _ _) /!\ snd (tri _ _) , u1)
  pasteh ze ze ze ze = ze

  asbo03 : forall {i1 i2}
       {(! sg01 , sg02) : < _-! i1 *: _-! i2 >}
       {(! sg13 , sg23) : < i1 =>_ *: i2 =>_ >}
    -> < [ sg01 /_]~ sg02 *: [_/ sg23 ]~ sg13 >
    -> < [ sg01 / sg13 ]~_ *: [ sg02 / sg23 ]~_ >
  asbo03 (! x , y) = go x y where
    go : forall {i1 i2}
       {(! sg01 , sg02) : < _-! i1 *: _-! i2 >}
       {(! sg13 , sg23) : < i1 =>_ *: i2 =>_ >}
       {sg12}
      -> [ sg01 / sg12 ]~ sg02 -> [ sg12 / sg23 ]~ sg13
      -> < [ sg01 / sg13 ]~_ *: [ sg02 / sg23 ]~_ >
    go (c $ x) y = let ! p , q = go x y in ! c $ p , c $ q
    go ty ze = ! ty , ty
    go va (.sb $ pp x ze y sg u)
      with r~ <- selQ (! x) (! nosel _)
         | r~ <- selQ (! y) (! iosel _)
         | r~ , r~ , r~ , r~ <- allRight u
         = ! va , sg
    go ze ze = ! ze , ze
    go (bb x) y =
      let ! p , q = go x
             (sb $ pp (naw (iosel _) {u = lll rr} (! io^ _)) y
                      (aye (nosel _) (! no^ _) (no^ _ /!\ io^ _ , rrr))
                        (va { e = va })
                      (lll rr))
      in  ! bb p , bb q
    go (pp a0 x0 a1 x1 u) y =
      let ! b0 = sel (! r%% a0 , b/ y)
          ! y0 = sbst (b%% a0) (b%% b0)
          ! p0 , q0 = go x0 y0
          ! b1 = sel (! r%% a1 , b/ y)
          ! y1 = sbst (b%% a1) (b%% b1)
          ! p1 , q1 = go x1 y1
          u' = roof u b0 b1
      in  ! pp (pasteh a0 y b0 y0) p0 (pasteh a1 y b1 y1) p1 u'
           , pp b0 q0 b1 q1 u'
