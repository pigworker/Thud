module Thud where

open import Basics
open import UF
open import Ctn
open import Cata
open import UD


decideMu : (C : Ctn) -> (Mu C -> Zero) + Mu C
decideMu (S <! P) with decideF (S `>< \ s -> P s `#> \ p -> `0)
... | # 1 , s , k = # 1 , < s , (\\ \ p -> magic (out {P s} k $$ p)) >
... | # 0 , r = # 0 , (rec - loop) where
  loop : {x : (S <! P) <* Zero} -> Rec x -> Zero
  loop < s / k > with decideF (P s)
  ... | # 0 , b = magic (r (s , inn {P s} (\\ b)))
  ... | # 1 , p = loop (k p)

BTree : Ctn
BTree .Sh = `Fin 2
BTree .Po (# 0) = `0
BTree .Po (# 1) = `Fin 2

