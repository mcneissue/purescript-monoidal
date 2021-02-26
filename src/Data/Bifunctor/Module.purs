module Data.Bifunctor.Module where

class LeftModule cat t1 t2 f
  where
  lstrength :: forall a b x. cat (f a b) (f (t1 a x) (t2 b x))

class RightModule cat t1 t2 f
  where
  rstrength :: forall a b x. cat (f a b) (f (t1 x a) (t2 x b))

class (LeftModule cat t1 t2 f, RightModule cat t1 t2 f) <= Bimodule cat t1 t2 f
