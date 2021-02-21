module Data.Bifunctor.Monoidal where

import Prelude hiding ((&&),(||))

import Control.Alt (class Alt, (<|>))
import Control.Alternative (class Alternative, empty)
import Control.Biapply (biapply)
import Control.Category.Tensor (class Associative, class Tensor, assoc, dup, merge, runit, swap)
import Data.Bifunctor (bimap, lmap)
import Data.Either (Either(..), either)
import Data.Either.Nested (type (\/))
import Data.Maybe (Maybe, maybe)
import Data.Newtype (un, class Newtype)
import Data.Op (Op(..))
import Data.Profunctor (class Profunctor, dimap, lcmap, rmap)
import Data.Profunctor.Joker (Joker(..))
import Data.Profunctor.Star (Star(..))
import Data.Profunctor.Strong (class Strong, first, second)
import Data.Tuple (Tuple, curry, fst, snd)
import Data.Tuple.Nested (type (/\), (/\))

-- {{{ SEMIGROUPAL

class (Associative l c, Associative r c, Associative o c) <= Semigroupal c l r o p
  where
  combine :: ∀ d e f g.
    c (o (p d e) (p f g)) (p (l d f) (r e g))

-- Mux     = (×) (×) (×)
-- Demux   = (+) (+) (×)
-- Switch  = (×) (+) (×)
-- Splice  = (+) (×) (×)
-- Diverge = (+) (+) (+)
-- Trivial = (×) (+) (+)

-- Mux
mux :: ∀ p a b c d. Semigroupal (->) Tuple Tuple Tuple p => p a b -> p c d -> p (a /\ c) (b /\ d)
mux = curry combine

infixr 5 mux as &&

zip :: ∀ p x a b. Profunctor p => Semigroupal (->) Tuple Tuple Tuple p => p x a -> p x b -> p x (a /\ b)
zip x y = lcmap dup $ x && y

-- Demux
demux :: ∀ p a b c d. Semigroupal (->) Either Either Tuple p => p a b -> p c d -> p (a \/ c) (b \/ d)
demux = curry combine

infixr 4 demux as ||

fanin :: ∀ p x a b. Profunctor p => Semigroupal (->) Either Either Tuple p => p a x -> p b x -> p (a \/ b) x
fanin x y = rmap merge $ x || y

-- Switch
switch :: ∀ p a b c d. Semigroupal (->) Tuple Either Tuple p => p a b -> p c d -> p (a /\ c) (b \/ d)
switch = curry combine

infixr 5 switch as &|

union :: ∀ p x a b. Profunctor p => Semigroupal (->) Tuple Either Tuple p => p x a -> p x b -> p x (a \/ b)
union x y = lcmap dup $ x &| y

divide :: ∀ p x a b. Profunctor p => Semigroupal (->) Tuple Either Tuple p => p a x -> p b x -> p (a /\ b) x
divide x y = rmap merge $ x &| y

-- Splice
splice :: ∀ p a b c d. Semigroupal (->) Either Tuple Tuple p => p a b -> p c d -> p (a \/ c) (b /\ d)
splice = curry combine

infixr 5 splice as |&

-- Diverge
diverge :: ∀ p a b c d. Semigroupal (->) Either Either Either p => p a b \/ p c d -> p (a \/ c) (b \/ d)
diverge = combine

contramapMaybe :: ∀ p a b x. Profunctor p => Semigroupal (->) Either Either Either p => (a -> Maybe b) -> p b x -> p a x
contramapMaybe f = dimap (maybe (Right unit) Left <<< f) merge <<< ultraleft

-- {{{ ULTRA STRENGTHS

-- NB: The thing to notice about these is that in a profunctor, there is a "trivially monoidal" tensor on each source category
-- On the contravariant end, this is the (/\) tensor, on the covariant end it is the (\/) tensor. When we take the output tensor
-- to be (\/), we can pick the source tensors in two ways such that precisely one is trivial and one is not. Doing this twice lets
-- us "dodge" a quantified variable past the variables of an actual `p a b`, so that you get a `p a b -> p (t1 a x) (t2 b x)`, i.e.
-- a strength.

zig :: ∀ p t a b x. Profunctor p => Semigroupal (->) Tuple t Either p => p x a \/ p x b -> p x (t a b)
zig = lcmap dup <<< combine

zag :: ∀ p t a b x. Profunctor p => Semigroupal (->) t Either Either p => p a x \/ p b x -> p (t a b) x
zag = rmap merge <<< combine

ultrafirst :: ∀ p a b x y.
  Profunctor p =>
  Semigroupal (->) Tuple Tuple  Either p =>
  p a b -> p (a /\ x) (b /\ y)
ultrafirst = zag <<< Left <<< zig <<< Left

ultrasecond :: ∀ p a b x y.
  Profunctor p =>
  Semigroupal (->) Tuple Tuple  Either p =>
  p a b -> p (x /\ a) (y /\ b)
ultrasecond = zag <<< Right <<< zig <<< Right

ultraleft :: ∀ p a b x y.
  Profunctor p =>
  Semigroupal (->) Either Either Either p =>
  p a b -> p (a \/ x) (b \/ y)
ultraleft = zag <<< Left <<< zig <<< Left

ultraright :: ∀ p a b x y.
  Profunctor p =>
  Semigroupal (->) Either Either Either p =>
  p a b -> p (x \/ a) (y \/ b)
ultraright = zag <<< Right <<< zig <<< Right

-- }}}

-- Comux
comux :: ∀ p a b c d. Semigroupal Op Tuple Tuple Tuple p => p (a /\ c) (b /\ d) -> p a b /\ p c d
comux = un Op combine

undivide :: ∀ p x a b. Profunctor p => Semigroupal Op Tuple Tuple Tuple p => p (a /\ b) x -> p a x /\ p b x
undivide = comux <<< rmap dup

-- Codemux
codemux :: ∀ p a b c d. Semigroupal Op Either Either Tuple p => p (a \/ c) (b \/ d) -> p a b /\ p c d
codemux = un Op combine

partition :: ∀ p x a b. Profunctor p => Semigroupal Op Either Either Tuple p => p x (a \/ b) -> p x a /\ p x b
partition = codemux <<< lcmap merge

-- Coswitch
coswitch :: ∀ p a b c d. Semigroupal Op Either Tuple Tuple p => p (a \/ c) (b /\ d) -> p a b /\ p c d
coswitch = un Op combine

unfanin :: ∀ p x a b. Profunctor p => Semigroupal Op Either Tuple Tuple p => p (a \/ b) x -> p a x /\ p b x
unfanin = coswitch <<< rmap dup

unzip :: ∀ p x a b. Profunctor p => Semigroupal Op Either Tuple Tuple p => p x (a /\ b) -> p x a /\ p x b
unzip = coswitch <<< lcmap merge

-- Cosplice
cosplice :: ∀ p a b c d. Semigroupal Op Tuple Either Tuple p => p (a /\ c) (b \/ d) -> p a b /\ p c d
cosplice = un Op combine

-- }}}

-- {{{ UNITAL

class Unital c l r o p
  where
  punit :: c o (p l r)

terminal :: ∀ p a. Profunctor p => Unital (->) Unit Unit Unit p => p a Unit
terminal = lcmap (const unit) $ punit unit

ppure :: ∀ p a. Profunctor p => Unital (->) Unit Unit Unit p => Strong p => p a a
ppure = dimap (unit /\ _) snd $ first $ (punit unit :: p Unit Unit)

initial :: ∀ p a. Profunctor p => Unital (->) Void Void Unit p => p Void a
initial = rmap absurd $ punit unit

poly :: ∀ p a b. Profunctor p => Unital (->) Unit Void Unit p => p a b
poly = dimap (const unit) absurd $ punit unit

mono :: ∀ p. Unital (->) Void Unit Unit p => p Void Unit
mono = punit unit

-- }}}

-- {{{ MONOIDAL

class (Tensor l il c, Tensor r ir c, Tensor o io c, Semigroupal c l r o p, Unital c il ir io p) <= Monoidal c l il r ir o io p

-- }}}

-- {{{ INSTANCES

-- {{{ ABSTRACT

-- This class of monoidal functors is trivial
instance trivial :: Profunctor p => Semigroupal (->) Tuple Either Either p
  where
  combine = either (dimap fst Left) (dimap snd Right)

-- Strong Category
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
  punit _ = StrongCategory identity

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
  punit = runit.bwd

instance tttMonoidalTuple :: Monoidal (->) Tuple Unit Tuple Unit Tuple Unit Tuple

-- }}}

-- {{{ DIVERGE

instance eeeSemigroupalTuple :: Semigroupal (->) Either Either Either Tuple
  where
  combine = either (bimap Left Left) (bimap Right Right)

instance eeeUnitalTuple :: Unital (->) Void Void Void Tuple
  where
  punit = absurd

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
  punit = runit.bwd

instance eeeMonoidalEither :: Monoidal (->) Either Void Either Void Either Void Either

-- }}}

-- {{{ SPLICE

instance ettSemigroupalEither :: Semigroupal (->) Either Tuple Tuple Either
  where
  combine (e1 /\ e2) = (/\) <$> lmap Left e1 <*> lmap Right e2

instance ettUnitalEither :: Unital (->) Void Unit Unit Either
  where
  punit = pure

instance ettMonoidalEither :: Monoidal (->) Either Void Tuple Unit Tuple Unit Either

-- }}}

-- NB: There is no point in doing both `×, +` and `+, ×` for a symmetric bifunctor, you can just get one from
-- the other using swap

-- }}}

-- {{{ FUNCTION

-- {{{ MUX

instance tttSemigroupalFunction :: Semigroupal (->) Tuple Tuple Tuple (->) where
  combine = biapply

instance tttUnitalFunction :: Unital (->) Unit Unit Unit (->) where
  punit = pure

instance tttMonoidalFunction :: Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (->)

-- }}}

-- {{{ DEMUX

instance eetSemigroupalFunction :: Semigroupal (->) Either Either Tuple (->) where
  combine (f /\ g) = bimap f g

instance eetUnitalFunction :: Unital (->) Void Void Unit (->) where
  punit = const absurd

instance eetMonoidalFunction :: Monoidal (->) Either Void Either Void Tuple Unit (->)

-- }}}

-- }}}

-- {{{ JOKER

-- {{{ MUX

instance tttSemigroupalJoker :: Apply f => Semigroupal (->) Tuple Tuple Tuple (Joker f) where
  combine (Joker f /\ Joker g) = Joker $ (/\) <$> f <*> g

instance tttUnitalJoker :: Applicative f => Unital (->) Unit Unit Unit (Joker f) where
  punit = Joker <<< pure

instance tttMonoidalJoker :: Applicative f => Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (Joker f)

-- }}}

-- {{{ DEMUX

instance eetSemigroupalJoker :: Alt f => Semigroupal (->) Either Either Tuple (Joker f) where
  combine (Joker f /\ Joker g) = Joker $ (Left <$> f) <|> (Right <$> g)

instance eetUnitalJoker :: Alternative f => Unital (->) Void Void Unit (Joker f) where
  punit = const $ Joker $ empty

instance eetMonoidalJoker :: Alternative f => Monoidal (->) Either Void Either Void Tuple Unit (Joker f)

-- }}}

-- {{{ DIVERGE

instance eeeSemigroupalJoker :: Functor f => Semigroupal (->) Either Either Either (Joker f) where
  combine (Left (Joker f)) = Joker $ map Left f
  combine (Right (Joker f)) = Joker $ map Right f

instance eeeUnitalJoker :: Functor f => Unital (->) Void Void Void (Joker f) where
  punit = absurd

instance eeeMonoidalJoker :: Functor f => Monoidal (->) Either Void Either Void Either Void (Joker f)

-- }}}

-- }}}

-- {{{ STAR

-- {{{ MUX

instance tttSemigroupalStar :: Apply f => Semigroupal (->) Tuple Tuple Tuple (Star f) where
  combine (Star f /\ Star g) = Star $ \(a /\ b) -> (/\) <$> f a <*> g b

instance tttUnitalStar :: Applicative f => Unital (->) Unit Unit Unit (Star f) where
  punit = const $ Star $ pure

instance tttMonoidalStar :: Applicative f => Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (Star f)

-- }}}

-- {{{ DEMUX

instance eetSemigroupalStar :: Functor f => Semigroupal (->) Either Either Tuple (Star f) where
  combine (Star f /\ Star g) = Star $ either (map Left <<< f) (map Right <<< g)

instance eetUnitalStar :: Functor f => Unital (->) Void Void Unit (Star f) where
  punit = const $ Star $ absurd

instance eetMonoidalStar :: Functor f => Monoidal (->) Either Void Either Void Tuple Unit (Star f)

-- }}}

-- {{{ DIVERGE

instance eeeSemigroupalStar :: Alternative f => Semigroupal (->) Either Either Either (Star f) where
  combine (Left (Star f)) = Star $ either (map Left <<< f) (const empty)
  combine (Right (Star f)) = Star $ either (const empty) (map Right <<< f)

instance eeeUnitalStar :: Alternative f => Unital (->) Void Void Void (Star f) where
  punit = absurd

instance eeeMonoidalStar :: Alternative f => Monoidal (->) Either Void Either Void Either Void (Star f)

-- }}}

-- }}}

-- }}}
