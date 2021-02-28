module Data.Functor.Module where

class LeftModule cat t1 f
  where
  lstrength :: ∀ a x. cat (f a) (f (t1 a x))

class RightModule cat t1 f
  where
  rstrength :: ∀ a x. cat (f a) (f (t1 x a))

class (LeftModule cat t1 f, RightModule cat t1 f) <= Bimodule cat t1 f
