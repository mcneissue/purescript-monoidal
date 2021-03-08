module Data.Trifunctor.Monoidal where

import Control.Category.Kinds (KHom)
import Control.Category.Tensor (class Associative, class Tensor)

-- {{{ SEMIGROUPAL

class Semigroupal :: ∀ k.
  KHom k
  -> (k -> k -> k)
  -> (k -> k -> k)
  -> (k -> k -> k)
  -> (k -> k -> k)
  -> (k -> k -> k -> k)
  -> Constraint
class
  ( Associative t1 cat
  , Associative t2 cat
  , Associative t3 cat
  , Associative to cat
  ) <=
  Semigroupal cat t1 t2 t3 to f
  where
  combine :: ∀ x x' y y' z z'.
    cat
      (to
        (f     x         y         z   )
        (f       x'        y'        z'))
        (f (t1 x x') (t2 y y') (t3 z z'))

-- }}}

-- {{{ UNITAL

class Unital :: ∀ k.
  KHom k
  -> k
  -> k
  -> k
  -> k
  -> (k -> k -> k -> k)
  -> Constraint
class Unital cat i1 i2 i3 o f
  where
  introduce :: cat o (f i1 i2 i3)

-- }}}

-- {{{ MONOIDAL

class Monoidal :: ∀ k.
  KHom k
  -> (k -> k -> k) -> k
  -> (k -> k -> k) -> k
  -> (k -> k -> k) -> k
  -> (k -> k -> k) -> k
  -> (k -> k -> k -> k)
  -> Constraint
class
  ( Tensor t1 i1 cat
  , Tensor t2 i2 cat
  , Tensor t3 i3 cat
  , Tensor to io cat
  , Semigroupal cat t1 t2 t3 to f
  , Unital cat i1 i2 i3 io f
  ) <=
  Monoidal cat t1 i1 t2 i2 t3 i3 to io f

-- }}}
