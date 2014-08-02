module Data.Functor.Contravariant.Coapplicative where

import Data.Functor.Contravariant
import Data.Monoid

class Contravariant f => Coapplicative f where
  divide  :: (a -> (b, c)) -> f b -> f c -> f a
  conquer :: f a
  
instance Monoid r => Coapplicative (Op r) where
  divide f (Op g) (Op h) = Op $ \a -> case f a of
    (b, c) -> g b `mappend` h c
  conquer = Op $ const mempty

instance Coapplicative Comparison where
  divide f (Comparison g) (Comparison h) = Comparison $ \a b -> case f a of
    (a',a'') -> case f b of
      (b',b'') -> g a' b' `mappend` h a'' b''
  conquer = Comparison $ \_ _ -> EQ

instance Coapplicative Equivalence where
  divide f (Equivalence g) (Equivalence h) = Equivalence $ \a b -> case f a of
    (a',a'') -> case f b of
      (b',b'') -> g a' b' && h a'' b''
  conquer = Equivalence $ \_ _ -> True

instance Coapplicative Predicate where
  divide f (Predicate g) (Predicate h) = Predicate $ \a -> case f a of
    (b, c) -> g b && h c
  conquer = Predicate $ const True
