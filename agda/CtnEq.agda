module CtnEq where

open import Basics
open import UF
open import UD
open import Ctn

module _ {X : Set}(dX : (a b : X) -> DEQ a b){C : Ctn} where

  fmEqHelp : {a : C <* X}(r : Rec a)(b : C <* X) -> DEQ a b
  fmEqHelp < s / r > < t , g > .DEq
    with decide (eqF (C .Sh) s t .DEq)
  ... | # 0 , b = Ff
  ... | # 1 , d with r~ <- eqF (C .Sh) s t .dEqEq d
    = Aa (C .Po s) \ p -> fmEqHelp (r p) (g $$ p) .DEq
  fmEqHelp {< s , k >} < s / r > < t , g > .dEqEq d
    with decide (eqF (C .Sh) s t .DEq)
  fmEqHelp < _ / r > < t , g > .dEqEq () | # 0 , b
  ... | # 1 , c with dEqEq (eqF (C .Sh) s t) c
  ... | r~ = rf ((t ,_) - <_>) ~$~ extIn (eta k) (eta g) \ p -> fmEqHelp (r p) (g $$ p) .dEqEq (out d $$ p)
  fmEqHelp < s / r > < .s , g > .eqDEq r~
     with decide (eqF (C .Sh) s s .DEq)
  ... | # 0 , b with () <- contra (eqF (C .Sh) s s .DEq) b (eqF (C .Sh) s s .eqDEq r~)
  ... | # 1 , d with r~ <- dEqEq (eqF (C .Sh) s s) d
                   = inn (\\ \ p -> fmEqHelp (r p) (g $$ p) .eqDEq r~)
  fmEqHelp < s / r > (! x) .DEq = Ff
  fmEqHelp < s / r > (! x) .dEqEq ()
  fmEqHelp < s / r > (! x) .eqDEq ()
  fmEqHelp (! x) < _ > .DEq = Ff
  fmEqHelp (! x) < _ > .dEqEq () 
  fmEqHelp (! x) < _ > .eqDEq ()
  fmEqHelp (! x) (! y) .DEq = dX x y .DEq
  fmEqHelp (! x) (! y) .dEqEq d with r~ <- dX x y .dEqEq d = r~
  fmEqHelp (! x) (! y) .eqDEq r~ = dX x y .eqDEq r~

  fmEq : (a b : C <* X) -> DEQ a b
  fmEq = rec - fmEqHelp
