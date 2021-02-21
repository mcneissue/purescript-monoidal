module Data.Trifunctor.Monoidal where

import Control.Category.Tensor (class Associative, class Tensor)

-- {{{ SEMIGROUPAL

class (Associative t1 c, Associative t2 c, Associative t3 c, Associative to c) <= Semigroupal c t1 t2 t3 to p
  where
  combine :: ∀ x x' y y' z z'.
    c
      (to
        (p     x         y         z   )
        (p       x'        y'        z'))
        (p (t1 x x') (t2 y y') (t3 z z'))

-- }}}

-- {{{ UNITAL

class Unital c i1 i2 i3 o p
  where
  punit :: c o (p i1 i2 i3)

-- }}}

-- {{{ MONOIDAL

class (Tensor t1 i1 c, Tensor t2 i2 c, Tensor t3 i3 c, Tensor to io c, Semigroupal c t1 t2 t3 to p, Unital c i1 i2 i3 io p) <= Monoidal c t1 i1 t2 i2 t3 i3 to io p

-- }}}
