module UFNot where

open import Basics
open import UF

finj : {n : Nat}(a b : Fin (n)) -> fs a ~ fs b -> a ~ b
finj a b r~ = r~

avoid : {n : Nat}(x : Fin (su n)) -> Fin n -> Fin (su n) >< \ y -> x ~ y -> Zero
avoid (# ze) (# y {l}) = # (su y) {l} , \ ()
avoid (# (su x)) (# ze) = # ze , \ ()
avoid {su n} (# (su x) {l}) (# (su y) {k}) = 
  let z , r = avoid (# x {l}) (# y {k})
  in  fs z , \ q -> r (finj _ _ q)

data FinQ : {n : Nat} -> Fin n -> Fin n -> Set where
  same# : {n : Nat}{x : Fin n} -> FinQ x x
  diff# : {n : Nat}{x : Fin (su n)}(y : Fin n) -> FinQ x (avoid x y .fst)

finQ : {n : Nat}(x y : Fin n) -> FinQ x y
finQ {su n} (# ze) (# ze) = same#
finQ {su n} (# ze) (# (su y)) = diff# (# y)
finQ {su (su n)} (# (su x)) (# ze) = diff# (# ze)
finQ {su (su n)} (# (su x) {k}) (# (su y) {l}) with finQ {su n} (# x {k}) (# y {l})
... | same# = same#
... | diff# z = diff# (fs z)

_-not_ : (X : UF)(x : ElF X) -> UF >< \ W -> ElF W -> ElF X >< \ y -> x ~ y -> Zero
`1 -not x = `0 , \ ()
`Fin (su n) -not x = `Fin n , avoid x
(S `>< T) -not (s , t) = 
  let R , rs = S -not s in let U , ut = T s -not t in
  ((R `>< \ r -> T (rs r .fst)) `+ U) , \
  { (# 0 , r , t) -> (rs r . fst , t) , (fstq - rs r .snd)
  ; (# 1 , u) -> (s , ut u .fst) , (sndq - ut u .snd)
  }

data UFQ (X : UF)(x : ElF X) : ElF X -> Set where
  same : UFQ X x x
  diff : (y : ElF ((X -not x) .fst)) -> UFQ X x ((X -not x) .snd y .fst)

ufQ : (X : UF)(x y : ElF X) -> UFQ X x y
ufQ `1 <> <> = same
ufQ (`Fin n) i j with finQ i j
... | same# = same
... | diff# y = diff y
ufQ (S `>< T) (xs , xt) (ys , yt) with ufQ S xs ys
... | diff y = diff (# 0 , y , yt)
... | same with ufQ (T xs) xt yt
... | diff y = diff (# 1 , y)
... | same = same
