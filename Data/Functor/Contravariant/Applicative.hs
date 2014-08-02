module Data.Functor.Contravariant.Applicative 
  ( ContravariantApplicative(..), divided
  , ContravariantAlternative(..), lost, chosen
  ) where

import Data.Functor.Contravariant
import Data.Monoid
import Data.Void

--------------------------------------------------------------------------------
-- * Contravariant Applicative
--------------------------------------------------------------------------------

class Contravariant f => ContravariantApplicative f where
  divide  :: (a -> (b, c)) -> f b -> f c -> f a
  conquer :: f a

divided :: ContravariantApplicative f => f a -> f b -> f (a, b)
divided = divide id
  
instance Monoid r => ContravariantApplicative (Op r) where
  divide f (Op g) (Op h) = Op $ \a -> case f a of
    (b, c) -> g b `mappend` h c
  conquer = Op $ const mempty

instance ContravariantApplicative Comparison where
  divide f (Comparison g) (Comparison h) = Comparison $ \a b -> case f a of
    (a',a'') -> case f b of
      (b',b'') -> g a' b' `mappend` h a'' b''
  conquer = Comparison $ \_ _ -> EQ

instance ContravariantApplicative Equivalence where
  divide f (Equivalence g) (Equivalence h) = Equivalence $ \a b -> case f a of
    (a',a'') -> case f b of
      (b',b'') -> g a' b' && h a'' b''
  conquer = Equivalence $ \_ _ -> True

instance ContravariantApplicative Predicate where
  divide f (Predicate g) (Predicate h) = Predicate $ \a -> case f a of
    (b, c) -> g b && h c
  conquer = Predicate $ const True

--------------------------------------------------------------------------------
-- * Contravariant Alternative
--------------------------------------------------------------------------------

class ContravariantApplicative f => ContravariantAlternative f where
  lose :: (a -> Void) -> f a
  choose :: (a -> Either b c) -> f b -> f c -> f a

lost :: ContravariantAlternative f => f Void
lost = lose id

chosen :: f b -> f c -> f (Either b c)
chosen = choose id

instance ContravariantAlternative Comparison where
  lose f = Comparison $ \a _ -> absurd (f a)
  choose f (Comparison g) (Comparison h) = Comparison $ \a b -> case f a of
    Left c -> case f b of
      Left d -> g c d
      Right{} -> LT
    Right c -> case f b of
      Left{} -> GT
      Right d -> h c d

instance ContravariantAlternative Equivalence where
  lose f = Equivalence $ \a -> absurd (f a)
  choose f (Equivalence g) (Equivalence h) = Equivalence $ \a b -> case f a of
    Left c -> case f b of
      Left d -> g c d
      Right{} -> False
    Right c -> case f b of
      Left{} -> False
      Right d -> h c d

instance ContravariantAlternative Predicate where
  lose f = Predicate $ \a -> absurd (f a)
  choose f (Predicate g) (Predicate h) = Predicate $ either g h . f

instance Monoid r => ContravariantAlternative (Op r) where
  lose f = Op $ absurd . f
  choose f (Op g) (Op h) = Op $ either g h . f
