module TmEq where

open import Basics
open import UF
open import Ctn
open import UD

module _ {C : Ctn}{X : Set}(dX : X -> X -> UD) where

  tmDecRelHelp : {a : C <* X}(r : Rec a) -> C <* X -> UD
  tmDecRelHelp < s / k > < t , j > = {!!}
  tmDecRelHelp < s / r > (! _) = Ff
  tmDecRelHelp (! _) < _ > = Ff
  tmDecRelHelp (! x) (! y) = dX x y
  
  tmDecRel : C <* X -> C <* X -> UD
  tmDecRel = rec - tmDecRelHelp
