module Data.Bifunctor.Bimodule where

class LeftModule c l r p
  where
  lstrength :: forall a b x. c (p a b) (p (l a x) (r b x))

class RightModule c l r p
  where
  rstrength :: forall a b x. c (p a b) (p (l x a) (r x b))

class (LeftModule c l r p, RightModule c l r p) <= Bimodule c l r p
