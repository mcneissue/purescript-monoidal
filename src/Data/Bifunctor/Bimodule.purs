module Data.Profunctor.Bimodule where

import Control.Category.Tensor (class Associative)
import Data.Profunctor (class Profunctor)

-- TODO: This is too restrictive, we only need `l` and `r` to be monoidal actions, not full
-- tensors. Generalize this.

class (Associative l c, Associative r c, Profunctor p) <= LeftModule c l r p
  where
  lstrength :: forall a b x. c (p a b) (p (l a x) (r b x))

class (Associative l c, Associative r c, Profunctor p) <= RightModule c l r p
  where
  rstrength :: forall a b x. c (p a b) (p (l x a) (r x b))

class (LeftModule c l r p, RightModule c l r p) <= Bimodule c l r p
