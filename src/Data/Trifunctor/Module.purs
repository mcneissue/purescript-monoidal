module Data.Trifunctor.Module where

class LeftModule cat t1 t2 t3 p
  where
  lstrength :: forall a b c x. cat (p a b c) (p (t1 a x) (t2 b x) (t3 c x))

class RightModule cat t1 t2 t3 p
  where
  rstrength :: forall a b c x. cat (p a b c) (p (t1 x a) (t2 x b) (t3 x c))

class (LeftModule cat t1 t2 t3 p, RightModule cat t1 t2 t3 p) <= Bimodule cat t1 t2 t3 p
