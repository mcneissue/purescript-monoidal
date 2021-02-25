module Functor.Monoidal where

import Control.Category.Tensor (class Associative, class Tensor)

-- {{{ SEMIGROUPAL

class (Associative t1 c, Associative to c) <= Semigroupal c t1 to f
  where
  combine :: ∀ x x'.
    c
      (to
        (f     x   )
        (f       x'))
        (f (t1 x x'))

-- }}}

-- {{{ UNITAL

class Unital c i1 io f
  where
  introduce :: c io (f i1)

-- }}}

-- {{{ MONOIDAL

class (Tensor t1 i1 c, Tensor to io c, Semigroupal c t1 to f, Unital c i1 io f) <= Monoidal c t1 i1 to io f

-- }}}
