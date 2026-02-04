module UD where

open import Basics
open import UF

data UD : Set where
  Tt : UD
  Ff : UD
  Aa : (X : UF)(D : ElF X -> UD) -> UD
  Ex : (X : UF)(D : ElF X -> UD) -> UD

Not : UD -> UD
Not Tt = Ff
Not Ff = Tt
Not (Aa X D) = Ex X \ x -> Not (D x)
Not (Ex X D) = Aa X \ x -> Not (D x)

ElD : UD -> Set
ElD Tt = One
ElD Ff = Zero
ElD (Aa X D) = (x : ElF X) -> ElD (D x)
ElD (Ex X D) = ElF X >< \ x -> ElD (D x)

contra : (D : UD) -> ElD (Not D) -> ElD D -> Zero
contra (Aa X D) (x , ndx) d = contra (D x) ndx (d x)
contra (Ex X D) nd (x , dx) = contra (D x) (nd x) dx

decideAa# : (n : Nat)(D : Fin n -> UD) ->
  ((x : Fin n) -> ElD (Not (D x)) + ElD (D x)) ->
  (Fin n >< (\ x -> ElD (Not (D x)))) + ((x : Fin n) -> ElD (D x))
decideAa# ze D d = # 1 , \ ()
decideAa# (su n) D d with d (# 0) | decideAa# n (fs - D) (fs - d)
... | # 0 , x | _ = # 0 , # 0 , x
... | # 1 , x | # 0 , i , z = # 0 , fs i , z 
... | # 1 , x | # 1 , y = # 1 , \ { (# ze) -> x ; (# (su i) {l}) -> y (# i {l}) }

decideAa : (X : UF)(D : ElF X -> UD) ->
  ((x : ElF X) -> ElD (Not (D x)) + ElD (D x)) ->
  (ElF X >< (\ x -> ElD (Not (D x)))) + ((x : ElF X) -> ElD (D x))
decideAa `0 D d = # 1 , \ ()
decideAa `1 D d with d <>
... | # 0 , x = # 0 , <> , x
... | # 1 , x = # 1 , \ _ -> x
decideAa (`Fin n) D d = decideAa# n D d
decideAa (S `>< T) D d
  with decideAa S (\ s -> Aa (T s) \ t -> D (s , t))
    (\ s -> decideAa (T s) (\ t -> D (s , t)) (\ t -> d (s , t)))
... | # 0 , s , t , x = # 0 , (s , t) , x
... | # 1 , r = # 1 , \ (s , t) -> r s t

decideEx# : (n : Nat)(D : Fin n -> UD) ->
  ((x : Fin n) -> ElD (Not (D x)) + ElD (D x)) ->
  ((x : Fin n) -> ElD (Not (D x))) + (Fin n >< \ x -> ElD (D x))
decideEx# ze D d = # 0 , \ ()
decideEx# (su n) D d with d (# 0) | decideEx# n (fs - D) (fs - d)
... | # 0 , x | # 0 , y = # 0 , \ { (# ze) -> x ; (# (su i) {l}) -> y (# i {l}) }
... | # 0 , x | # 1 , i , y = # 1 , fs i , y
... | # 1 , x | _ = # 1 , # 0 , x

decideEx : (X : UF)(D : ElF X -> UD) ->
  ((x : ElF X) -> ElD (Not (D x)) + ElD (D x)) ->
  ((x : ElF X) -> ElD (Not (D x))) + (ElF X >< \ x -> ElD (D x))
decideEx `0 D d = # 0 , \ ()
decideEx `1 D d with d <>
... | # 0 , x = # 0 , \ _ -> x
... | # 1 , x = # 1 , _ , x
decideEx (`Fin n) D d = decideEx# n D d
decideEx (S `>< T) D d
  with decideEx S (\ s -> Ex (T s) \ t -> D (s , t))
    (\ s -> decideEx (T s) (\ t -> D (s , t)) (\ t -> d (s , t)))
... | # 0 , r = # 0 , \ (s , t) -> r s t
... | # 1 , s , t , x = # 1 , (s , t) , x

decide : (D : UD) -> ElD (Not D) + ElD D
decide Tt = # 1 , <>
decide Ff = # 0 , <>
decide (Aa X D) = decideAa X D \ x -> decide (D x)
decide (Ex X D) = decideEx X D \ x -> decide (D x)

decideF : (X : UF) -> (ElF X -> Zero) + ElF X
decideF X with decide (Ex X \ _ -> Tt)
... | # 0 , r = # 0 , r
... | # 1 , x , <> = # 1 , x

eq# : (n : Nat)(a b : Fin n) -> UD >< \ Q -> ElD Q -> a ~ b
eq# (su n) (# ze) (# ze) = Tt , \ _ -> r~
eq# (su n) (# ze) (# (su j)) = Ff , \ ()
eq# (su n) (# (su i)) (# ze) = Ff , \ ()
eq# (su n) (# (su i) {l}) (# (su j) {k}) .fst = eq# n (# i {l}) (# j {k}) .fst
eq# (su n) (# (su i) {l}) (# (su j) {k}) .snd q
  with r~ <- eq# n (# i {l}) (# j {k}) .snd q = r~

eqF : (X : UF)(a b : ElF X) -> UD >< \ Q -> ElD Q -> a ~ b
eqF `1 a b = Tt , \ _ -> r~
eqF (`Fin n) a b = eq# n a b
eqF (S `>< T) (as , at) (bs , bt) with eqF S as bs
... | QS , qs with decide QS
... | # 0 , x = Ff , \ ()
... | # 1 , x with qs x
... | r~ with eqF (T as) at bt
... | QT , qt = QT , \ x -> rf (as ,_) ~$~ qt x

rf# : (n : Nat)(i : Fin n) -> ElD (eq# n i i .fst)
rf# (su n) (# ze) = <>
rf# (su n) (# (su i) {l}) = rf# n (# i {l})

rfF : (X : UF)(x : ElF X) -> ElD (eqF X x x .fst)
rfF `1 <> = <>
rfF (`Fin n) i = rf# n i
rfF (S `>< T) (s , t) with eqF S s s | rfF S s
... | QS , qs | xs with decide QS
... | # 0 , x = contra QS x xs
... | # 1 , x with qs x
... | r~ with eqF (T s) t t | rfF (T s) t
... | QT , qt | xt = xt
