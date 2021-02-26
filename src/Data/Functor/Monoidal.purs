module Data.Functor.Monoidal where

import Prelude

import Control.Alt (class Alt, alt)
import Control.Category.Tensor (class Associative, class Tensor)
import Control.Plus (class Plus, empty)
import Data.Either (Either(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))

-- {{{ SEMIGROUPAL

class (Associative t1 c, Associative to c) <= Semigroupal c t1 to f
  where
  combine :: ∀ x x'.
    c
      (to
        (f     x   )
        (f       x'))
        (f (t1 x x'))

instance semigroupalApply :: Apply f => Semigroupal (->) Tuple Tuple f
  where
  combine (fa /\ fb) = (/\) <$> fa <*> fb

instance semigroupalAlt :: Alt f => Semigroupal (->) Either Tuple f
 where
 combine (fa /\ fb) = alt (Left <$> fa) (Right <$> fb)

-- }}}

-- {{{ UNITAL

class Unital c i1 io f
  where
  introduce :: c io (f i1)

instance unitalApplicative :: Applicative f => Unital (->) Unit Unit f
  where
  introduce = pure

instance unitalPlus :: Plus f => Unital (->) Void Unit f
  where
  introduce = const empty

-- }}}

-- {{{ MONOIDAL

class (Tensor t1 i1 c, Tensor to io c, Semigroupal c t1 to f, Unital c i1 io f) <= Monoidal c t1 i1 to io f

instance monoidalApplicative :: Applicative f => Monoidal (->) Tuple Unit Tuple Unit f

instance monoidalPlus :: Plus f => Monoidal (->) Either Void Tuple Unit f

-- }}}
