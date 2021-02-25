module Functor.Module where

class LeftModule c t f
  where
  lstrength :: forall a x. c (f a) (f (t a x))

class RightModule c t f
  where
  rstrength :: forall a x. c (f a) (f (t x a))

class (LeftModule c t f, RightModule c t f) <= Bimodule c t f
