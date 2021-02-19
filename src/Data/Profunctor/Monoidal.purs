module Data.Profunctor.Monoidal where

import Prelude

import Control.Alt (class Alt, (<|>))
import Control.Alternative (class Alternative, empty)
import Control.Category.Tensor (class Associative, class Tensor)
import Data.Either (Either(..), either)
import Data.Either.Nested (type (\/))
import Data.Newtype (un, class Newtype)
import Data.Op (Op(..))
import Data.Profunctor (class Profunctor, dimap, lcmap, rmap)
import Data.Profunctor.Joker (Joker(..))
import Data.Profunctor.Star (Star(..))
import Data.Profunctor.Strong (class Strong, first, second)
import Data.Tuple (Tuple, curry, snd)
import Data.Tuple.Nested (type (/\), (/\))

dup :: forall a. a -> a /\ a
dup a = a /\ a

merge :: forall a. a \/ a -> a
merge = either identity identity

-- {{{ SEMIGROUPAL

class (Associative l c, Associative r c, Associative o c) <= Semigroupal c l r o p
  where
  pzip :: forall d e f g.
    c (o (p d e) (p f g)) (p (l d f) (r e g))

-- Mux
mux :: forall p a b c d. Semigroupal (->) Tuple Tuple Tuple p => p a b -> p c d -> p (a /\ c) (b /\ d)
mux = curry pzip

infixr 5 mux as &&

zip :: forall p x a b. Profunctor p => Semigroupal (->) Tuple Tuple Tuple p => p x a -> p x b -> p x (a /\ b)
zip x y = lcmap dup $ x && y

-- Demux
demux :: forall p a b c d. Semigroupal (->) Either Either Tuple p => p a b -> p c d -> p (a \/ c) (b \/ d)
demux = curry pzip

infixr 4 demux as ||

fanin :: forall p x a b. Profunctor p => Semigroupal (->) Either Either Tuple p => p a x -> p b x -> p (a \/ b) x
fanin x y = rmap merge $ x || y

-- Switch
switch :: forall p a b c d. Semigroupal (->) Tuple Either Tuple p => p a b -> p c d -> p (a /\ c) (b \/ d)
switch = curry pzip

infixr 5 switch as &|

union :: forall p x a b. Profunctor p => Semigroupal (->) Tuple Either Tuple p => p x a -> p x b -> p x (a \/ b)
union x y = lcmap dup $ x &| y

divide :: forall p x a b. Profunctor p => Semigroupal (->) Tuple Either Tuple p => p a x -> p b x -> p (a /\ b) x
divide x y = rmap merge $ x &| y

-- Splice
splice :: forall p a b c d. Semigroupal (->) Either Tuple Tuple p => p a b -> p c d -> p (a \/ c) (b /\ d)
splice = curry pzip

infixr 5 splice as |&

-- Comux
comux :: forall p a b c d. Semigroupal Op Tuple Tuple Tuple p => p (a /\ c) (b /\ d) -> p a b /\ p c d
comux = un Op pzip

undivide :: forall p x a b. Profunctor p => Semigroupal Op Tuple Tuple Tuple p => p (a /\ b) x -> p a x /\ p b x
undivide = comux <<< rmap dup

-- Codemux
codemux :: forall p a b c d. Semigroupal Op Either Either Tuple p => p (a \/ c) (b \/ d) -> p a b /\ p c d
codemux = un Op pzip

partition :: forall p x a b. Profunctor p => Semigroupal Op Either Either Tuple p => p x (a \/ b) -> p x a /\ p x b
partition = codemux <<< lcmap merge

-- Coswitch
coswitch :: forall p a b c d. Semigroupal Op Either Tuple Tuple p => p (a \/ c) (b /\ d) -> p a b /\ p c d
coswitch = un Op pzip

unfanin :: forall p x a b. Profunctor p => Semigroupal Op Either Tuple Tuple p => p (a \/ b) x -> p a x /\ p b x
unfanin = coswitch <<< rmap dup

unzip :: forall p x a b. Profunctor p => Semigroupal Op Either Tuple Tuple p => p x (a /\ b) -> p x a /\ p x b
unzip = coswitch <<< lcmap merge

-- Cosplice
cosplice :: forall p a b c d. Semigroupal Op Tuple Either Tuple p => p (a /\ c) (b \/ d) -> p a b /\ p c d
cosplice = un Op pzip

-- }}}

-- {{{ UNITAL

class Unital c l r o p
  where
  punit :: c o (p l r)

terminal :: forall p a. Profunctor p => Unital (->) Unit Unit Unit p => p a Unit
terminal = lcmap (const unit) $ punit unit

ppure :: forall p a. Profunctor p => Unital (->) Unit Unit Unit p => Strong p => p a a
ppure = dimap (unit /\ _) snd $ first $ (punit unit :: p Unit Unit)

initial :: forall p a. Profunctor p => Unital (->) Void Void Unit p => p Void a
initial = rmap absurd $ punit unit

poly :: forall p a b. Profunctor p => Unital (->) Unit Void Unit p => p a b
poly = dimap (const unit) absurd $ punit unit

mono :: forall p. Unital (->) Void Unit Unit p => p Void Unit
mono = punit unit

-- }}}

-- {{{ MONOIDAL

class (Tensor l il c, Tensor r ir c, Tensor o io c, Semigroupal c l r o p, Unital c il ir io p) <= Monoidal c l il r ir o io p

-- }}}

-- {{{ INSTANCES

-- Joker
instance tttSemigroupalJoker :: Apply f => Semigroupal (->) Tuple Tuple Tuple (Joker f) where
  pzip (Joker f /\ Joker g) = Joker $ (/\) <$> f <*> g

instance tttUnitalJoker :: Applicative f => Unital (->) Unit Unit Unit (Joker f) where
  punit = Joker <<< pure

instance tttMonoidalJoker :: Applicative f => Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (Joker f)

instance eetSemigroupalJoker :: Alt f => Semigroupal (->) Either Either Tuple (Joker f) where
  pzip (Joker f /\ Joker g) = Joker $ (Left <$> f) <|> (Right <$> g)

instance eetUnitalJoker :: Alternative f => Unital (->) Void Void Unit (Joker f) where
  punit = const $ Joker $ empty

instance eetMonoidalJoker :: Alternative f => Monoidal (->) Either Void Either Void Tuple Unit (Joker f)

instance eeeSemigroupalJoker :: Functor f => Semigroupal (->) Either Either Either (Joker f) where
  pzip (Left (Joker f)) = Joker $ map Left f
  pzip (Right (Joker f)) = Joker $ map Right f

instance eeeUnitalJoker :: Functor f => Unital (->) Void Void Void (Joker f) where
  punit = absurd

instance eeeMonoidalJoker :: Functor f => Monoidal (->) Either Void Either Void Either Void (Joker f)

-- Star
instance tttSemigroupalStar :: Apply f => Semigroupal (->) Tuple Tuple Tuple (Star f) where
  pzip (Star f /\ Star g) = Star $ \(a /\ b) -> (/\) <$> f a <*> g b

instance tttUnitalStar :: Applicative f => Unital (->) Unit Unit Unit (Star f) where
  punit = const $ Star $ pure

instance tttMonoidalStar :: Applicative f => Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (Star f)

instance eetSemigroupalStar :: Functor f => Semigroupal (->) Either Either Tuple (Star f) where
  pzip (Star f /\ Star g) = Star $ either (map Left <<< f) (map Right <<< g)

instance eetUnitalStar :: Functor f => Unital (->) Void Void Unit (Star f) where
  punit = const $ Star $ absurd

instance eetMonoidalStar :: Functor f => Monoidal (->) Either Void Either Void Tuple Unit (Star f)

instance eeeSemigroupalStar :: Alternative f => Semigroupal (->) Either Either Either (Star f) where
  pzip (Left (Star f)) = Star $ either (map Left <<< f) (const empty)
  pzip (Right (Star f)) = Star $ either (const empty) (map Right <<< f)

instance eeeUnitalStar :: Alternative f => Unital (->) Void Void Void (Star f) where
  punit = absurd

instance eeeMonoidalStar :: Alternative f => Monoidal (->) Either Void Either Void Either Void (Star f)

-- Strong Category

newtype StrongCategory p a b = StrongCategory (p a b)

derive instance newtypeStrongCategory :: Newtype (StrongCategory p a b) _

derive newtype instance profunctorStrongCategory :: Profunctor p => Profunctor (StrongCategory p)
derive newtype instance strongStrongCateogry :: Strong p => Strong (StrongCategory p)
derive newtype instance semigroupoidStrongCategory :: Semigroupoid p => Semigroupoid (StrongCategory p)
derive newtype instance categoryStrongCategory :: Category p => Category (StrongCategory p)

-- Every Strong Category is Muxable

instance tttSemigroupalStrongCategory :: (Strong p, Semigroupoid p) => Semigroupal (->) Tuple Tuple Tuple (StrongCategory p) where
  pzip (StrongCategory pab /\ StrongCategory pcd) = StrongCategory (second pcd <<< first pab)

instance tttUnitalStrongCategory :: (Profunctor p, Category p) => Unital (->) Unit Unit Unit (StrongCategory p) where
  punit _ = StrongCategory identity

instance tttMonoidalStrongCategory :: (Strong p, Category p) => Monoidal (->) Tuple Unit Tuple Unit Tuple Unit (StrongCategory p)

-- }}}
