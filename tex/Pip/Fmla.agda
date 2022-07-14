module Fmla where

open import Base
open import CodB

data Sort : Set where
  chk syn : Sort
  sub : Nat -> Sort
  _su : Sort -> Sort
  _**_ : Sort -> Sort -> Sort

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

  data Tm : Sort -> Nat -> Set where
    _$_ : forall {n t s} -> t -< s > -> Tm s n -> Tm t n
    ty : Tm chk 0
    va : Tm syn 1
    ze : Tm (sub 0) 0
    bb : forall {n s} -> Tm s (n su) -> Tm (s su) n
    pp : forall {i j n s t}{th : i <= n}{ph : j <= n} ->
           Tm s i -> th /u\ ph -> Tm t j -> Tm (s ** t) n
  infixr  60 _$_

module _ {M : Nat -> Set} where
  open TM M

  infix 80 _=>_
  _=>_ : Nat -> Nat -> Set
  m => n = Tm (sub m) n

  infix 80 _%%_
  data _%%_ : forall {i k}
    -> < i <=_ *: _=> k > -> < i =>_ *: _<= k >
    -> Set where
    naw : forall {i k k0}
          {lt@(! th , sg) : < i <=_ *: _=> k0 >}
          {br@(! ta , ph) : < i =>_ *: _<= k0 >}
       -> lt %% br
       -> {ps : k0 <= k}{(k1 , e , ph1) : Tm syn ^^ k}
       -> {u : ps /u\ ph1}
       -> ((ph0 , _) : < [ ph ^ ps ]~_ >)
       -> (! th fu , sb $ pp sg u e) %% (! ta , ph0)
    aye : forall {i k k0}
          {lt@(! th , sg) : < i <=_ *: _=> k0 >}
          {br@(! ta , ph) : < i =>_ *: _<= k0 >}
       -> lt %% br
       -> {ps : k0 <= k}{(k1 , e , ph1) : Tm syn ^^ k}
       -> {u : ps /u\ ph1}
       -> ((ph0 , _) : < [ ph ^ ps ]~_ >)
       -> ((C , u') : CopDiag ph0 ph1)
       -> (! th su , sb $ pp sg u e) %% (! sb $ pp ta u' e , slak C)
    ze : (! ze , ze) %% (! ze , ze)

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

  data [_/_]~_ : forall {m n s} -> Tm s m -> m => n -> Tm s n -> Set where
    _$_ : forall {o i m n}(c : o -< i >){t : Tm i m}{sg : m => n}{t'}
       -> [ t / sg ]~ t' -> [ c $ t / sg ]~ c $ t'
    ty : [ ty / ze ]~ ty
    va : forall {n}{e : Tm syn n}
      -> [ va / sb $ pp ze rrr e ]~ e
    ze : [ ze / ze ]~ ze
    bb : forall {m n s}{t : Tm s (m su)}{t'}{sg : m => n}
      -> [ t / sb $ pp sg (lll rr) va ]~ t' -> [ bb t / sg ]~ bb t'
    pp : forall {m n s0 s1}
         {(! t0 , th0) : Tm s0 ^^ m}
         {(! t1 , th1) : Tm s1 ^^ m}
         {u : th0 /u\ th1}
         {sg : m => n}
         {(! t0' , ph0) : Tm s0 ^^ n}
         {(! t1' , ph1) : Tm s1 ^^ n}
         {sg0 sg1} ->
         (! th0 , sg) %% (! sg0 , ph0) ->
         [ t0 / sg0 ]~ t0' ->
         (! th1 , sg) %% (! sg1 , ph1) ->
         [ t1 / sg1 ]~ t1' ->
         (u' : ph0 /u\ ph1) ->
         [ pp t0 u t1 / sg ]~ pp t0' u' t1'

  sbst : forall {m n s}(t : Tm s m)(sg : m => n)
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

  _/_ : forall {m n s}(t : Tm s m)(sg : m => n) -> Tm s n
  t / sg = fst (sbst t sg)

  sbstQ : forall {m n s}{t : Tm s m}{sg : m => n}(x y : < [ t / sg ]~_ >) -> x ~ y
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

  is : forall {n} -> Tm (sub n) n
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

  _/is : forall {m s}(t : Tm s m) -> [ t / is ]~ t
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


{-
  pp~ : forall {n s t}
        {a@(! i , th0) b@(! j , ph0) : Tm s ^^ n}
        {c@(! k , th1) d@(! l , ph1) : Tm t ^^ n}
     -> a ~ b -> c ~ d
     -> {u : th0 /u\ th1}{w : ph0 /u\ ph1}
     -> pp i u k ~ pp j w l
  pp~ r~ r~ {u}{w} with r~ <- copIrr u w = r~

  roof : forall {i0 i1 m n}{th0 : i0 <= m}{th1 : i1 <= m}
         (u : th0 /u\ th1)(sg : Tm (sub m) n)
      -> Tm (sub i0 ** sub i1) n
  roof (u0 su) (sb (pp sg u1 e))
    with pp sg0 u2 sg1 <- roof u0 sg
       | ! a , ! b , ! c <- lem1 u1 u2
       = pp (sb (pp sg0 b e)) a (sb (pp sg1 c e))
  roof (u0 ll) (sb (pp sg u1 e))
    with pp sg0 u2 sg1 <- roof u0 sg
       | ! (! _ , a) , ! ! ! b , _ <- rot u1 (swap u2)
       = pp (sb (pp sg0 b e)) (swap a) sg1
  roof (u0 rr) (sb (pp sg u1 e))
    with pp sg0 u2 sg1 <- roof u0 sg
       | ! (! _ , a) , ! ! ! b , _ <- rot u1 u2
       = pp sg0 a (sb (pp sg1 b e))
  roof ze ze = pp ze ze ze
    
  _/_ : forall {m n s} -> Tm s m -> Tm (sub m) n -> Tm s n
  em t / sg = em (t / sg)
  ty / ze = ty
  pi t / sg = pi (t / sg)
  la t / sg = la (t / sg)
  (m $ t) / sg = m $ (t / sg)
  va / sb (pp ze u e) with r~ , _ <- allRight u = e
  ra t / sg = ra (t / sg)
  ap t / sg = ap (t / sg)
  ze / ze = ze
  sb t / sg = sb (t / sg)
  kk t / sg = kk (t / sg)
  bb t / sg = bb (t / sb (pp sg (lll rr) va))
  pp s u t / sg with pp sg0 u' sg1 <- roof u sg = pp (s / sg0) u' (t / sg1)

  is : forall {n} -> Tm (sub n) n
  is {ze} = ze
  is {n su} = sb (pp is (lll rr) va)

  rooflll : forall {m n}(sg : Tm (sub m) n) -> roof lll sg ~ pp sg lll ze
  rooflll ze = r~
  rooflll (sb (pp sg u e)) rewrite rooflll sg | rot-rrr u = pp~ r~ r~

  roofrrr : forall {m n}(sg : Tm (sub m) n) -> roof rrr sg ~ pp ze rrr sg
  roofrrr ze = r~
  roofrrr (sb (pp sg u e)) rewrite roofrrr sg | rot-rrr u = r~

  is/ : forall {m n}(sg : Tm (sub m) n) -> (is / sg) ~ sg
  is/ {ze} ze = r~
  is/ {m su} (sb (pp {j = j} sg u e))
    rewrite rooflll sg | rot-lll u | allRightQ {j} | is/ sg = r~

  roof-is : forall {i j n}{th : i <= n}{ph : j <= n}(u : th /u\ ph)
    -> roof u is ~ pp is u is
  roof-is (u su) rewrite roof-is u | lem1lll u = r~
  roof-is (u ll) rewrite roof-is u | rotlll (swap u) = pp~ r~ r~
  roof-is (u rr) rewrite roof-is u | rotlll u = r~
  roof-is ze = r~

  _/is : forall {n s}(t : Tm s n) -> (t / is) ~ t
  em t /is rewrite t /is = r~
  ty /is = r~
  pi t /is rewrite t /is = r~
  la t /is rewrite t /is = r~
  (m $ t) /is rewrite t /is = r~
  va /is = r~
  ra t /is rewrite t /is = r~
  ap t /is rewrite t /is = r~
  ze /is = r~
  sb t /is rewrite t /is = r~
  kk t /is rewrite t /is = r~
  bb t /is rewrite t /is = r~
  pp s u t /is rewrite roof-is u | s /is | t /is = r~

  compw : forall {l n m}(sg : Tm (sub l) n)(ta : Tm (sub n) m)
       -> sb (pp (sg / ta) (lll rr) va)
        ~ (sb (pp sg (lll rr) va) / sb (pp ta (lll rr) va))
  compw {l}{n}{m} sg ta
    rewrite rooflll ta | rotlll (lll {m}) = r~

  compr : forall {l n m}{(! th0) (! ph0) : < _<= l >}(u0 : th0 /u\ ph0)
          (sg : Tm (sub l) n)(ta : Tm (sub n) m)
          {(! th1) (! ph1) : < _<= n >}(u1 : th1 /u\ ph1)
          {sg0 sg1} -> roof u0 sg ~ pp sg0 u1 sg1 ->
          forall {(! th2) (! ph2) : < _<= m >}(u2 : th2 /u\ ph2)
          {ta0 ta1} -> roof u1 ta ~ pp ta0 u2 ta1 ->
          roof u0 (sg / ta) ~ pp (sg0 / ta0) u2 (sg1 / ta1)
  compr (u0 su) (TM.sb (TM.pp sg u3 e)) ta u1 q1 u2 q2
    with pp tal u4 tar <- roof u3 ta
       | z <- compr u0 sg tal
       | pp sg0 u5 sg1 <- roof u0 sg
       | y <- z u5 r~
       | pp ta2 u6 ta3 <- roof u5 tal
       | x <- y u6 r~
       | pp up0 u7 up1 <- roof u0 (sg / tal)
       | r~ <- x
       | r~ <- q1
       = {!!}
  compr (u0 ll) sg ta u1 q1 u2 q2 = {!!}
  compr (u0 rr) sg ta u1 q1 u2 q2 = {!!}
  compr ze TM.ze TM.ze .ze r~ .ze r~ = r~

  compo : forall {l n m s}(t : Tm s l)(sg : Tm (sub l) n)(ta : Tm (sub n) m)
       -> (t / (sg / ta)) ~ ((t / sg) / ta)
  compo (em t) sg ta rewrite compo t sg ta = r~
  compo ty ze ze = r~
  compo (pi t) sg ta rewrite compo t sg ta = r~
  compo (TM.la t) sg ta rewrite compo t sg ta = r~
  compo (x TM.$ t) sg ta rewrite compo t sg ta = r~
  compo {m = m} TM.va (TM.sb (TM.pp TM.ze u e)) ta
    with r~ , r~ , r~ , r~ <- allRight u
    rewrite roofrrr ta | allRightQ {m}
    = r~
  compo (TM.ra t) sg ta rewrite compo t sg ta = r~
  compo (TM.ap t) sg ta rewrite compo t sg ta = r~
  compo TM.ze TM.ze TM.ze = r~
  compo (TM.sb t) sg ta rewrite compo t sg ta = r~
  compo (TM.kk t) sg ta rewrite compo t sg ta = r~
  compo (TM.bb t) sg ta
    rewrite compw sg ta
          | compo t (sb (pp sg (lll rr) va)) (sb (pp ta (lll rr) va))
    = r~
  compo (TM.pp s u0 t) sg ta
    with z <- compr u0 sg ta
       | pp sg0 u1 sg1 <- roof u0 sg
       | y <- z u1 r~
       | pp ta0 u2 ta1 <- roof u1 ta
    rewrite y u2 r~ | compo s sg0 ta0 | compo t sg1 ta1
       = r~
-}
