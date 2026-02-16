module UD where

open import Basics
open import UF

{- A universe of decisions.
   You can do without Tt and Ff, but it's not so neat.
-}

data UD : Set where
  Tt : UD
  Ff : UD
  Aa : (X : UF)(D : ElF X -> UD) -> UD
  Ex : (X : UF)(D : ElF X -> UD) -> UD

_/\_ _\/_ : UD -> UD -> UD
A /\ B = Aa (`Fin 2) (A <01> B)
A \/ B = Ex (`Fin 2) (A <01> B)

-- Negation is de Morgan
Not : UD -> UD
Not Tt = Ff
Not Ff = Tt
Not (Aa X D) = Ex X \ x -> Not (D x)  -- look! a witness!
Not (Ex X D) = Aa X \ x -> Not (D x)

-- interpretation goes via UF
DF : UD -> UF
DF Tt = `1
DF Ff = `0
DF (Aa X D) = X `#> \ x -> DF (D x)
DF (Ex X D) = X `>< \ x -> DF (D x)

ElD : UD -> Set
ElD = DF - ElF

-- a decision is not both no and yes
contra : (D : UD) -> ElD (Not D) -> ElD D -> Zero
contra (Aa X D) (x , ndx) d = contra (D x) ndx (out d $$ x)
contra (Ex X D) nd (x , dx) = contra (D x) (out nd $$ x) dx

-- now we've got to show we can figure out the decision...

-- explore Fin
decideAa# : (n : Nat)(D : Fin n -> UD) ->
  ((x : Fin n) -> ElD (Not (D x)) + ElD (D x)) ->
  (Fin n >< (\ x -> ElD (Not (D x)))) + ElF (`Fin n `#> (D - DF))
decideAa# ze D d = # 1 , <>
decideAa# (su n) D d with d (# 0) | decideAa# n (fs - D) (fs - d)
... | # 0 , x | _ = # 0 , # 0 , x
... | # 1 , x | # 0 , i , z = # 0 , fs i , z 
... | # 1 , x | # 1 , y = # 1 , x , y

-- explore UF
decideAa : (X : UF)(D : ElF X -> UD) ->
  ((x : ElF X) -> ElD (Not (D x)) + ElD (D x)) ->
  (ElF X >< (\ x -> ElD (Not (D x)))) + ElD (Aa X D)
decideAa `0 D d = # 1 , <>
decideAa `1 D d with d <>
... | # 0 , x = # 0 , <> , x
... | # 1 , x = # 1 , x
decideAa (`Fin n) D d = decideAa# n D d
decideAa (S `>< T) D d
  with decideAa S (\ s -> Aa (T s) \ t -> D (s , t)) (\ s ->
    decideAa (T s) (\ t -> D (s , t)) (\ t -> d (s , t)))
... | # 0 , s , t , x = # 0 , (s , t) , x 
... | # 1 , z = # 1 , z 

-- the existential counterparts should perhaps exploit
-- de Morgan duality

decideEx# : (n : Nat)(D : Fin n -> UD) ->
  ((x : Fin n) -> ElD (Not (D x)) + ElD (D x)) ->
  ElF (`Fin n `#> ((D - Not) - DF)) + (Fin n >< \ x -> ElD (D x))
decideEx# ze D d = # 0 , <>
decideEx# (su n) D d with d (# 0) | decideEx# n (fs - D) (fs - d)
... | # 0 , x | # 0 , y = # 0 , x , y
... | # 0 , x | # 1 , i , y = # 1 , fs i , y
... | # 1 , x | _ = # 1 , # 0 , x

decideEx : (X : UF)(D : ElF X -> UD) ->
  ((x : ElF X) -> ElD (Not (D x)) + ElD (D x)) ->
  ElF (X `#> ((D - Not) - DF)) + (ElF X >< \ x -> ElD (D x))
decideEx `0 D d = # 0 , <>
decideEx `1 D d with d <>
... | # 0 , x = # 0 , x
... | # 1 , x = # 1 , _ , x
decideEx (`Fin n) D d = decideEx# n D d
decideEx (S `>< T) D d
  with decideEx S (\ s -> Ex (T s) \ t -> D (s , t))
    (\ s -> decideEx (T s) (\ t -> D (s , t)) (\ t -> d (s , t)))
... | # 0 , r = # 0 , r 
... | # 1 , s , t , x = # 1 , (s , t) , x

-- put it together and what do you get?
decide : (D : UD) -> ElD (Not D) + ElD D
decide Tt = # 1 , <>
decide Ff = # 0 , <>
decide (Aa X D) = decideAa X D \ x -> decide (D x)
decide (Ex X D) = decideEx X D \ x -> decide (D x)

-- as a consequence, UF is decided
decideF : (X : UF) -> (ElF X -> Zero) + ElF X
decideF X with decide (Ex X \ _ -> Tt)
... | # 0 , r = # 0 , \ x -> out r $$ x
... | # 1 , x , _ = # 1 , x


-- now, let's talk about *equality* decisions

record DEQ {X : Set}(a b : X): Set where
  field
    DEq : UD
    dEqEq : ElD DEq -> a ~ b
    eqDEq : a ~ b -> ElD DEq
open DEQ public

-- first for Fin
eq# : (n : Nat)(a b : Fin n) -> DEQ a b
eq# (su n) (# ze) (# ze) .DEq = Tt
eq# (su n) (# ze) (# ze) .dEqEq _ = r~
eq# (su n) (# ze) (# ze) .eqDEq _ = <>
eq# (su n) (# ze) (# (su b)) .DEq = Ff
eq# (su n) (# ze) (# (su b)) .dEqEq ()
eq# (su n) (# ze) (# (su b)) .eqDEq ()
eq# (su n) (# (su a)) (# ze) .DEq = Ff
eq# (su n) (# (su a)) (# ze) .dEqEq ()
eq# (su n) (# (su a)) (# ze) .eqDEq ()
eq# (su n) (# (su a) {k}) (# (su b) {l}) =
  help (eq# n (# a {k}) (# b {l}))  
  where
    help : DEQ {Fin n}(# a {k}) (# b {l})
        -> DEQ {Fin (su n)}(# (su a) {k}) (# (su b) {l})
    help dab .DEq = dab .DEq
    help dab .dEqEq q with r~ <- dab .dEqEq q = r~
    help dab .eqDEq r~ = dab .eqDEq r~

-- then for UF
eqF : (X : UF)(a b : ElF X) -> DEQ a b
eqF `1 a b .DEq = Tt
eqF `1 a b .dEqEq _ = r~
eqF `1 a b .eqDEq _ = <>
eqF (`Fin n) a b = eq# n a b

-- now the fun bit (is this tidyable?)
eqF (S `>< T) (as , at) (bs , bt) .DEq
  with decide (eqF S as bs .DEq)
... | # 0 , x = Ff
... | # 1 , ds with r~ <- eqF S as bs .dEqEq ds
  = eqF (T as) at bt .DEq
  
eqF (S `>< T) (as , at) (bs , bt) .dEqEq dt
  with decide (eqF S as bs .DEq)
eqF (S `>< T) (as , at) (bs , bt) .dEqEq () | # 0 , x
eqF (S `>< T) (as , at) (bs , bt) .dEqEq dt | # 1 , ds
  with eqF S as bs .dEqEq ds
eqF (S `>< T) (as , at) (bs , bt) .dEqEq dt | # 1 , ds | r~
  with r~ <- eqF (T as) at bt .dEqEq dt
  = r~
  
eqF (S `>< T) (as , at) (bs , bt) .eqDEq r~
  with decide (eqF S as as .DEq)
... | # 0 , x = contra (eqF S as as .DEq) x (eqF S as as .eqDEq r~)
... | # 1 , x with eqF S as as .dEqEq x
... | r~ = eqF (T as) at at .eqDEq r~
