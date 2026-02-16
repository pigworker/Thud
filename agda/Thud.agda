module Thud where

open import Basics
open import UF
open import Ctn
open import Cata
open import UD
open import CtnEq


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

thudBasis : (C : Ctn) -> UF >< \ B -> B #> \ _ -> Mu C
thudBasis C with decideMu C
... | # 0 , bad = `0 , \\ \ ()
... | # 1 , thud = C .Sh , \\ \ s -> < s , (\\ \ _ -> thud) >


module _ {C D : Ctn}(mystery : Mu C -> Mu D) where

  guessTemplate : (Mu C -> Zero) + (C -*> D)
  guessTemplate with decideMu C
  ... | # 0 , b = # 0 , b
  ... | # 1 , thud
    with decide (Aa (C .Sh) \ s -> fmEq (\ ()) (mystery thud) -- thud is the parent
                                               (mystery < s , \\ (\ _ -> thud) >) -- all the kids are thud
                                               .DEq)
  ... | # 1 , y = # 1 , \\ \ s -> mystery thud >>= \ ()
  ... | # 0 , u , diff = let blunder : Mu C
                             blunder = < u ,  \\ (\ _ -> thud) >
                             -- we know mystery blunder is different from mystery thud
                             -- we may now construct the *perturbed* basis
                             -- in which for every shape s and position p
                             -- we have s with blunder in p and thud everywhere else
                             -- and wherever the output from p-perturbed differs from unperturbed
                             -- we put the variable p!
                         in {!!}
