module Data.Bifunctor.Monoidal where

import Prelude hiding ((&&),(||))

import Control.Alt (class Alt, alt, (<|>))
import Control.Alternative (class Plus, empty)
import Control.Biapply (biapply)
import Control.Category.Kinds (KHom)
import Control.Category.Tensor (class Associative, class Tensor, assoc, runit, swap)
import Data.Bifunctor (bimap, lmap)
import Data.Either (Either(..), either)
import Data.Functor.Joker (Joker(..))
import Data.Newtype (class Newtype)
import Data.Profunctor (class Profunctor, dimap)
import Data.Profunctor.Star (Star(..))
import Data.Profunctor.Strong (class Strong, first, second)
import Data.These (These(..))
import Data.Tuple (Tuple, fst, snd)
import Data.Tuple.Nested ((/\))

-- {{{ SEMIGROUPAL

class Semigroupal :: ∀ k.
  KHom k
  -> (k -> k -> k)
  -> (k -> k -> k)
  -> (k -> k -> k)
  -> (k -> k -> k)
  -> Constraint
class
  ( Associative t1 cat
  , Associative t2 cat
  , Associative to cat
  ) <=
  Semigroupal cat t1 t2 to f
  where
  combine :: ∀ x x' y y'.
    cat
      (to
        (f     x         y   )
        (f       x'        y'))
        (f (t1 x x') (t2 y y'))

-- }}}

-- {{{ UNITAL

class Unital :: ∀ k.
  KHom k
  -> k
  -> k
  -> k
  -> (k -> k -> k)
  -> Constraint
class Unital cat i1 i2 io f
  where
  introduce :: cat io (f i1 i2)

-- }}}

-- {{{ MONOIDAL

class Monoidal :: ∀ k.
  KHom k
  -> (k -> k -> k) -> k
  -> (k -> k -> k) -> k
  -> (k -> k -> k) -> k
  -> (k -> k -> k)
  -> Constraint
class
  ( Tensor t1 i1 cat
  , Tensor t2 i2 cat
  , Tensor to io cat
  , Semigroupal cat t1 t2 to f
  , Unital cat i1 i2 io f
  ) <=
  Monoidal cat t1 i1 t2 i2 to io f

-- }}}

-- {{{ INSTANCES

-- {{{ ABSTRACT

-- This class of monoidal functors is trivial
instance trivial :: Profunctor p => Semigroupal (->) Tuple Either Either p
  where
  combine = either (dimap fst Left) (dimap snd Right)

-- Strong Category
newtype StrongCategory :: ∀ k. KHom k -> KHom k
newtype StrongCategory p a b = StrongCategory (p a b)

derive instance newtypeStrongCategory :: Newtype (StrongCategory p a b) _

derive newtype instance profunctorStrongCategory :: Profunctor p => Profunctor (StrongCategory p)
derive newtype instance strongStrongCateogry :: Strong p => Strong (StrongCategory p)
derive newtype instance semigroupoidStrongCategory :: Semigroupoid p => Semigroupoid (StrongCategory p)
derive newtype instance categoryStrongCategory :: Category p => Category (StrongCategory p)

-- Every Strong Category is Muxable
instance tttSemigroupalStrongCategory :: (Strong p, Semigroupoid p) => Semigroupal (->) Tuple Tuple Tuple (StrongCategory p) where
  combine (StrongCategory pab /\ StrongCategory pcd) = StrongCategory (second pcd <<< first pab)

instance tttUnitalStrongCategory :: (Profunctor p, Category p) => Unital (->) Unit Unit Unit (StrongCategory p) where
  introduce _ = StrongCategory identity

instance tttMonoidalStrongCategory :: (Strong p, Category p) => Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (StrongCategory p)

-- }}}

-- {{{ TUPLE

-- {{{ MUX

-- If `t` is some tensor, `t` is a monoidal functor from `t, t` to `t`

instance tttsemigroupalTuple :: Semigroupal (->) Tuple Tuple Tuple Tuple
  where
  combine = assoc.fwd <<< map (assoc.bwd <<< lmap swap <<< assoc.fwd) <<< assoc.bwd

instance tttunitalTuple :: Unital (->) Unit Unit Unit Tuple
  where
  introduce = runit.bwd

instance tttMonoidalTuple :: Monoidal (->) Tuple Unit Tuple Unit Tuple Unit Tuple

-- }}}

-- {{{ DIVERGE

instance eeeSemigroupalTuple :: Semigroupal (->) Either Either Either Tuple
  where
  combine = either (bimap Left Left) (bimap Right Right)

instance eeeUnitalTuple :: Unital (->) Void Void Void Tuple
  where
  introduce = absurd

instance eeeMonoidalTuple :: Monoidal (->) Either Void Either Void Either Void Tuple

-- }}}

-- }}}

-- {{{ EITHER

-- {{{ DIVERGE

-- If `t` is some tensor, `t` is a monoidal functor from `t, t` to `t`

instance eeeSemigroupalEither :: Semigroupal (->) Either Either Either Either
  where
  combine = assoc.fwd <<< map (assoc.bwd <<< lmap swap <<< assoc.fwd) <<< assoc.bwd

instance eeeUnitalEither :: Unital (->) Void Void Void Either
  where
  introduce = runit.bwd

instance eeeMonoidalEither :: Monoidal (->) Either Void Either Void Either Void Either

-- }}}

-- {{{ SPLICE

instance ettSemigroupalEither :: Semigroupal (->) Either Tuple Tuple Either
  where
  combine (e1 /\ e2) = (/\) <$> lmap Left e1 <*> lmap Right e2

instance ettUnitalEither :: Unital (->) Void Unit Unit Either
  where
  introduce = pure

instance ettMonoidalEither :: Monoidal (->) Either Void Tuple Unit Tuple Unit Either

-- }}}

-- NB: There is no point in doing both `×, +` and `+, ×` for a symmetric bifunctor, you can just get one from
-- the other using swap

instance sttSemigroupalEither :: Semigroupal (->) These Tuple Tuple Either
  where
  combine (Left x /\ Left y) = Left $ Both x y
  combine (Left x /\ Right _) = Left $ This x
  combine (Right _ /\ Left y) = Left $ That y
  combine (Right x /\ Right y) = Right $ x /\ y

instance sttMonoidalEither :: Monoidal (->) These Void Tuple Unit Tuple Unit Either

-- }}}

-- {{{ FUNCTION

-- {{{ MUX

instance tttSemigroupalFunction :: Semigroupal (->) Tuple Tuple Tuple (->) where
  combine = biapply

instance tttUnitalFunction :: Unital (->) Unit Unit Unit (->) where
  introduce = pure

instance tttMonoidalFunction :: Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (->)

-- }}}

-- {{{ DEMUX

instance eetSemigroupalFunction :: Semigroupal (->) Either Either Tuple (->) where
  combine (f /\ g) = bimap f g

instance eetUnitalFunction :: Unital (->) Void Void Unit (->) where
  introduce = const absurd

instance eetMonoidalFunction :: Monoidal (->) Either Void Either Void Tuple Unit (->)

-- }}}

-- }}}

-- {{{ JOKER

-- {{{ MUX

instance tttSemigroupalJoker :: Apply f => Semigroupal (->) Tuple Tuple Tuple (Joker f) where
  combine (Joker f /\ Joker g) = Joker $ (/\) <$> f <*> g

instance tttUnitalJoker :: Applicative f => Unital (->) Unit Unit Unit (Joker f) where
  introduce = Joker <<< pure

instance tttMonoidalJoker :: Applicative f => Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (Joker f)

-- }}}

-- {{{ DEMUX

instance eetSemigroupalJoker :: Alt f => Semigroupal (->) Either Either Tuple (Joker f) where
  combine (Joker f /\ Joker g) = Joker $ (Left <$> f) <|> (Right <$> g)

instance eetUnitalJoker :: Plus f => Unital (->) Void Void Unit (Joker f) where
  introduce = const $ Joker $ empty

instance eetMonoidalJoker :: Plus f => Monoidal (->) Either Void Either Void Tuple Unit (Joker f)

-- }}}

-- {{{ DIVERGE

instance eeeSemigroupalJoker :: Functor f => Semigroupal (->) Either Either Either (Joker f) where
  combine (Left (Joker f)) = Joker $ map Left f
  combine (Right (Joker f)) = Joker $ map Right f

instance eeeUnitalJoker :: Functor f => Unital (->) Void Void Void (Joker f) where
  introduce = absurd

instance eeeMonoidalJoker :: Functor f => Monoidal (->) Either Void Either Void Either Void (Joker f)

-- }}}

-- }}}

-- {{{ STAR

-- {{{ MUX

instance tttSemigroupalStar :: Apply f => Semigroupal (->) Tuple Tuple Tuple (Star f) where
  combine (Star f /\ Star g) = Star $ \(a /\ b) -> (/\) <$> f a <*> g b

instance tttUnitalStar :: Applicative f => Unital (->) Unit Unit Unit (Star f) where
  introduce = const $ Star $ pure

instance tttMonoidalStar :: Applicative f => Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (Star f)

-- }}}

-- {{{ DEMUX

instance eetSemigroupalStar :: Functor f => Semigroupal (->) Either Either Tuple (Star f) where
  combine (Star f /\ Star g) = Star $ either (map Left <<< f) (map Right <<< g)

instance eetUnitalStar :: Functor f => Unital (->) Void Void Unit (Star f) where
  introduce = const $ Star $ absurd

instance eetMonoidalStar :: Functor f => Monoidal (->) Either Void Either Void Tuple Unit (Star f)

-- }}}

-- {{{ DIVERGE

instance eeeSemigroupalStar :: Plus f => Semigroupal (->) Either Either Either (Star f) where
  combine (Left (Star f)) = Star $ either (map Left <<< f) (const empty)
  combine (Right (Star f)) = Star $ either (const empty) (map Right <<< f)

instance eeeUnitalStar :: Plus f => Unital (->) Void Void Void (Star f) where
  introduce = absurd

instance eeeMonoidalStar :: Plus f => Monoidal (->) Either Void Either Void Either Void (Star f)

-- }}}

-- {{{ SWITCH

instance tetSemigroupalStar :: Alt f => Semigroupal (->) Tuple Either Tuple (Star f) where
  combine (Star f /\ Star g) = Star $ \(x /\ y) -> alt (Left <$> f x) (Right <$> g y)

instance tetUnitalStar :: Plus f => Unital (->) Unit Void Unit (Star f) where
  introduce = const $ Star $ const empty

instance tetMonoidalStar :: Plus f => Monoidal (->) Tuple Unit Either Void Tuple Unit (Star f)

-- }}}

-- }}}

-- }}}
