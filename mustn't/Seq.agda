module Seq where

open import Basics
open import Bwd
open import Thin


module _ (A : Set) where
  data Fmla : Set where
    atom : A -> Fmla
    _\/_ _/\_ : Fmla -> Fmla -> Fmla
    Not : Fmla -> Fmla
    Ff Tt : Fmla

module _ {A : Set} where

  fmlaSize : Fmla A -> Nat
  fmlaSize (p \/ q) = su (fmlaSize p +N fmlaSize q)
  fmlaSize (p /\ q) = su (fmlaSize p +N fmlaSize q)
  fmlaSize (Not p) = su (fmlaSize p)
  fmlaSize _ = 1

  fmlazSize : Bwd (Fmla A) -> Nat
  fmlazSize [] = 0
  fmlazSize (pz -, p) = fmlazSize pz +N fmlaSize p

module _ {A : Set} where

  data [_*_]-[_+_] : Bwd (Fmla A) -> Bwd A -> Bwd (Fmla A) -> Bwd A -> Set where
    Axi : forall {ga al de be} -> <: _<1 al :* _<1 be :> -> [ ga * al ]-[ de + be ]
    AtE : forall {ga al de be x}
       -> [ ga * al -, x ]-[ de + be ]
       -> [ ga -, atom x * al ]-[ de + be ]
    AtI : forall {ga al de be x}
       -> [ ga * al ]-[ de + be -, x ]
       -> [ ga * al ]-[ de -, atom x + be ]
    FfE : forall {ga al de be}
       -> [ ga -, Ff * al ]-[ de + be ]
    FfI : forall {ga al de be}
       -> [ ga * al ]-[ de + be ]
       -> [ ga * al ]-[ de -, Ff + be ]
    TtE : forall {ga al de be}
       -> [ ga * al ]-[ de + be ]
       -> [ ga -, Tt * al ]-[ de + be ]
    TtI : forall {ga al de be}
       -> [ ga * al ]-[ de -, Tt + be ]
    OrE : forall {ga al de be p q}
       -> [ ga -, p * al ]-[ de + be ]
       -> [ ga -, q * al ]-[ de + be ]
       -> [ ga -, (p \/ q) * al ]-[ de + be ]
    OrI : forall {ga al de be p q}
       -> [ ga * al ]-[ de -, p -, q + be ]
       -> [ ga * al ]-[ de -, (p \/ q) + be ]
    AnE : forall {ga al de be p q}
       -> [ ga -, p -, q * al ]-[ de + be ]
       -> [ ga -, (p /\ q) * al ]-[ de + be ]
    AnI : forall {ga al de be p q}
       -> [ ga * al ]-[ de -, p + be ]
       -> [ ga * al ]-[ de -, q + be ]
       -> [ ga * al ]-[ de -, (p /\ q) + be ]
    NoE : forall {ga al de be p}
       -> [ ga * al ]-[ de -, p + be ]
       -> [ ga -, Not p * al ]-[ de + be ]
    NoI : forall {ga al de be p}
       -> [ ga -, p * al ]-[ de + be ]
       -> [ ga * al ]-[ de -, Not p + be ]

  module _ (aq? : EqDec A) where
  
    wangGas : Nat -> forall ga al de be -> Maybe [ ga * al ]-[ de + be ]
    wangGas _ (ga -, Ff) _ _ _ = tt , FfE
    wangGas (su n) (ga -, Tt) al de be = wangGas n ga al de be >>= \ d -> tt , TtE d
    wangGas (su n) (ga -, (p /\ q)) al de be = wangGas n (ga -, p -, q) al de be >>= \ d -> tt , AnE d
    wangGas (su n) (ga -, Not p) al de be = wangGas n ga al (de -, p) be >>= \ d -> tt , NoE d
    wangGas _ _ _ (de -, Tt) _ = tt , TtI
    wangGas (su n) ga al (de -, Ff) be = wangGas n ga al de be >>= \ d -> tt , FfI d
    wangGas (su n) ga al (de -, (p \/ q)) be = wangGas n ga al (de -, p -, q) be >>= \ d -> tt , OrI d
    wangGas (su n) ga al (de -, Not p) be = wangGas n (ga -, p) al de be >>= \ d -> tt , NoI d
    wangGas _ ga al de be with joint? aq? al be
    ... | tt , ij = tt , Axi ij
    wangGas (su n) (ga -, atom a) al de be | ff , <> = wangGas n ga (al -, a) de be >>= \ d -> tt , AtE d
    wangGas (su n) ga al (de -, atom b) be | ff , <> = wangGas n ga al de (be -, b) >>= \ d -> tt , AtI d 
    wangGas (su n) (ga -, (p \/ q)) al de be | ff , <> = 
      wangGas n (ga -, p) al de be >>= \ d0 ->
      wangGas n (ga -, q) al de be >>= \ d1 ->
      tt , OrE d0 d1
    wangGas (su n) ga al (de -, (p /\ q)) be | ff , <> = 
      wangGas n ga al (de -, p) be >>= \ d0 ->
      wangGas n ga al (de -, q) be >>= \ d1 ->
      tt , AnI d0 d1
    wangGas _ ga al de be | ff , <> = ff , <>

    wang : forall ga al de be -> Maybe [ ga * al ]-[ de + be ]
    wang ga al de be = wangGas (fmlazSize ga +N fmlazSize de) ga al de be
    

module _ {X : Set}{xi : Bwd X}(rh : Nat -> <: _<= xi :>)  where

  Diag : Fmla Nat -> Set
  diag : (p : Fmla Nat) -> Diag p -> <: _<= xi :>
  Diag (atom x) = One
  Diag (p \/ q) = Diag p >< \ P -> Diag q >< \ Q -> Cop (diag p P .snd) (diag q Q .snd)
  Diag (p /\ q) =
    Diag p >< \ P -> Diag q >< \ Q -> <: _<= xi :> >< \ (_ , ps) ->
    <: [_-< diag p P .snd ]~ ps :> >< \ (_ , v) ->
    <: [_-< diag q Q .snd ]~ ps :> >< \ (_ , w) ->
    Pub (ps , v , w)
  Diag (Not p) = Diag p >< \ P -> <: _<= xi :> >< \ pop ->
    pop .snd /u\ diag p P .snd * Pub (no , no-< (pop .snd) , no-< (diag p P .snd))
  Diag Ff = One
  Diag Tt = One
  diag (atom x) <> = rh x
  diag (p \/ q) (P , Q , C , u) = _ , C .uuth
  diag (p /\ q) (P , Q , x , _) = x
  diag (Not p) (P , x , _) = x
  diag Ff <> = _ , no
  diag Tt <> = _ , io
  
  model : forall {ga al de be x}(i : x <1 xi)
     -> [ ga * al ]-[ de + be ]
     -> All (\ p -> Diag p >< \ P -> <: [_-< diag p P .snd ]~ i :>) ga
     -> All (\ n -> <: [_-< rh n .snd ]~ i :>) al
     -> (Dz : All Diag de)
     -> Any (\ (p , P) -> <: [_-< diag p P .snd ]~ i :>) (zipA de Dz)
      + Any (\ n -> <: [_-< rh n .snd ]~ i :>) be

  model i (Axi (_ , j , k)) gaz alz Dez with <> , x <- j <? alz = tt , ((tt , x) ?< k)
  model i (AtE d) (gaz , <> , y) alz Dez = model i d gaz (alz , y) Dez
  model i (AtI d) gaz alz (Dez , <>) with model i d gaz alz Dez
  ... | ff , z = ff , ff , z
  ... | tt , ff , z = tt , z
  ... | tt , tt , z = ff , tt , z 
  model i (FfI d) gaz alz (Dez , <>) with model i d gaz alz Dez
  ... | ff , z = ff , ff , z
  ... | tt , z = tt , z
  model i (TtE d) (gaz , _) alz Dez = model i d gaz alz Dez
  model i TtI gaz alz _ = ff , tt , _ , i -<io
  model i (OrE d0 d1) (gaz , (P , Q , v </\> w , u) , (j , x)) alz Dez with egtbs u (_ , j)
  model i (OrE d0 d1) (gaz , (P , Q , v </\> w , u) , (j , x)) alz Dez | ff , _ , z
    with asso13 (_ , z , x)
  ... | _ , v0 , v1 with unique (tri _ _) {_ , v}{_ , v1}
  ... | r~ = model i d0 (gaz , P , _ , v0) alz Dez
  model i (OrE d0 d1) (gaz , (P , Q , v </\> w , u) , (_ , x)) alz Dez | tt , _ , z
    with asso13 (_ , z , x)
  ... | _ , w0 , w1 with unique (tri _ _) {_ , w}{_ , w1}
  ... | r~ = model i d1 (gaz , Q , _ , w0) alz Dez
  model i (OrI d) gaz alz (Dez , P , Q , v </\> w , u)
    with model i d gaz alz ((Dez , P) , Q)
  ... | ff , ff , ff , z = ff , ff , z
  ... | ff , ff , tt , _ , v0 = ff , tt , 
    let _ , v1 , v2 = asso02 (_ , v0 , v) in
    _ , v2
  ... | ff , tt , _ , w0 = ff , tt , 
    let _ , w1 , w2 = asso02 (_ , w0 , w) in
    _ , w2
  ... | tt , z = tt , z
  model i (AnE d) (gaz , (P , Q , z , (_ , v) , (_ , w) , pb) , (_ , y)) alz Dez
    with _ , _ , j <- asso02 (_ , y , v) | _ , _ , k <- asso02 (_ , y , w)
    = model i d ((gaz , P , _ , j) , Q , _ , k) alz Dez
  model i (AnI d0 d1) gaz alz (Dez , P , Q , z , (_ , v) , (_ , w) , pb)
    with model i d0 gaz alz (Dez , P) | model i d1 gaz alz (Dez , Q)
  ... | ff , x | tt , y = tt , y
  ... | tt , x | b , y = tt , x
  ... | ff , ff , x | ff , b , y = ff , ff , x
  ... | ff , tt , x | ff , ff , y = ff , ff , y
  ... | ff , tt , _ , v0 | ff , tt , _ , w0 = ff , tt ,
    let _ , _ , b , _ = pubU pb (_ , v0 , w0) in
    _ , b
  model i (NoE d) (gaz , (P , pop , u , pb) , _ , y) alz Dez with model i d gaz alz (Dez , P)
  ... | tt , z = tt , z
  ... | ff , ff , z = ff , z
  ... | ff , tt , _ , z with pubU pb (_ , y , z)
  ... | () , _
  model i (NoI d) gaz alz (Dez , P , pop , u , pb) with egtbs u (_ , i)
  ... | ff , z = ff , tt , z
  ... | tt , z with model i d (gaz , P , z) alz Dez
  ... | ff , z = ff , ff , z
  ... | tt , z = tt , z

  thump : forall ga al de be ((_ , i) : <: _<1 xi :>)
        {prf : So (wang natEq? ga al de be .fst)}
     -> All (\ p -> Diag p >< \ P -> <: [_-< diag p P .snd ]~ i :>) ga
     -> All (\ n -> <: [_-< rh n .snd ]~ i :>) al
     -> (Dz : All Diag de)
     -> Any (\ (p , P) -> <: [_-< diag p P .snd ]~ i :>) (zipA de Dz)
      + Any (\ n -> <: [_-< rh n .snd ]~ i :>) be
  thump ga al de be (_ , i) with wang natEq? ga al de be
  ... | tt , d = model i d
