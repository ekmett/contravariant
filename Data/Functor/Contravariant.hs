{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveDataTypeable #-}
#if __GLASGOW_HASKELL__ >= 702
#if MIN_VERSION_transformers(0,3,0)
#if MIN_VERSION_tagged(0,6,1)
{-# LANGUAGE Safe #-}
#else
{-# LANGUAGE Trustworthy #-}
#endif
#else
{-# LANGUAGE Trustworthy #-}
#endif
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Contravariant
-- Copyright   :  (C) 2007-2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- 'Contravariant' functors, sometimes referred to colloquially as @Cofunctor@,
-- even though the dual of a 'Functor' is just a 'Functor'. As with 'Functor'
-- the definition of 'Contravariant' for a given ADT is unambiguous.
----------------------------------------------------------------------------

module Data.Functor.Contravariant (
  -- * Contravariant Functors
    Contravariant(..)

  -- * Operators
  , (>$<), (>$$<)

  -- * Predicates
  , Predicate(..)

  -- * Comparisons
  , Comparison(..)
  , defaultComparison

  -- * Equivalence Relations
  , Equivalence(..)
  , defaultEquivalence

  -- * Dual arrows
  , Op(..)
  ) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Category
import Data.Functor.Product
import Data.Functor.Constant
import Data.Functor.Compose
import Data.Functor.Reverse
import GHC.Generics
import Prelude hiding ((.),id)
import Data.Typeable
#if __GLASGOW_HASKELL__ < 707
import Data.Proxy
#endif

-- | Any instance should be subject to the following laws:
--
-- > contramap id = id
-- > contramap f . contramap g = contramap (g . f)
--
-- Note, that the second law follows from the free theorem of the type of
-- 'contramap' and the first law, so you need only check that the former
-- condition holds.

class Contravariant f where
  contramap :: (a -> b) -> f b -> f a

infixl 4 >$<, >$$<

(>$<) :: Contravariant f => (a -> b) -> f b -> f a
(>$<) = contramap
{-# INLINE (>$<) #-}

(>$$<) :: Contravariant f => f b -> (a -> b) -> f a
(>$$<) = flip contramap
{-# INLINE (>$$<) #-}

instance Contravariant V1 where
  contramap _ x = x `seq` undefined

instance Contravariant U1 where
  contramap _ U1 = U1

instance Contravariant f => Contravariant (Rec1 f) where
  contramap f (Rec1 fp)= Rec1 (contramap f fp)

instance Contravariant f => Contravariant (M1 i c f) where
  contramap f (M1 fp) = M1 (contramap f fp)

instance Contravariant (K1 i c) where
  contramap _ (K1 c) = K1 c

instance (Contravariant f, Contravariant g) => Contravariant (f :*: g) where
  contramap f (xs :*: ys) = contramap f xs :*: contramap f ys

instance (Functor f, Contravariant g) => Contravariant (f :.: g) where
  contramap f (Comp1 fg) = Comp1 (fmap (contramap f) fg)
  {-# INLINE contramap #-}

instance (Contravariant f, Contravariant g) => Contravariant (f :+: g) where
  contramap f (L1 xs) = L1 (contramap f xs)
  contramap f (R1 ys) = R1 (contramap f ys)

instance (Contravariant f, Contravariant g) => Contravariant (Product f g) where
  contramap f (Pair a b) = Pair (contramap f a) (contramap f b)

instance Contravariant (Constant a) where
  contramap _ (Constant a) = Constant a

instance Contravariant (Const a) where
  contramap _ (Const a) = Const a

instance (Functor f, Contravariant g) => Contravariant (Compose f g) where
  contramap f (Compose fga) = Compose (fmap (contramap f) fga)
  {-# INLINE contramap #-}

instance Contravariant f => Contravariant (Backwards f) where
  contramap f = Backwards . contramap f . forwards
  {-# INLINE contramap #-}

instance Contravariant f => Contravariant (Reverse f) where
  contramap f = Reverse . contramap f . getReverse
  {-# INLINE contramap #-}

instance Contravariant Proxy where
  contramap _ Proxy = Proxy

newtype Predicate a = Predicate { getPredicate :: a -> Bool }
#ifdef __GLASGOW_HASKELL__
  deriving Typeable
#endif



-- | A 'Predicate' is a 'Contravariant' 'Functor', because 'contramap' can
-- apply its function argument to the input of the predicate.
instance Contravariant Predicate where
  contramap f g = Predicate $ getPredicate g . f

-- | Defines a total ordering on a type as per 'compare'
newtype Comparison a = Comparison { getComparison :: a -> a -> Ordering }
#ifdef __GLASGOW_HASKELL__
  deriving Typeable
#endif

-- | A 'Comparison' is a 'Contravariant' 'Functor', because 'contramap' can
-- apply its function argument to each input to each input to the
-- comparison function.
instance Contravariant Comparison where
  contramap f g = Comparison $ \a b -> getComparison g (f a) (f b)

-- | Compare using 'compare'
defaultComparison :: Ord a => Comparison a
defaultComparison = Comparison compare

-- | Define an equivalence relation
newtype Equivalence a = Equivalence { getEquivalence :: a -> a -> Bool }
#ifdef __GLASGOW_HASKELL__
  deriving Typeable
#endif

-- | Equivalence relations are 'Contravariant', because you can
-- apply the contramapped function to each input to the equivalence
-- relation.
instance Contravariant Equivalence where
  contramap f g = Equivalence $ \a b -> getEquivalence g (f a) (f b)

-- | Check for equivalence with '=='
defaultEquivalence :: Eq a => Equivalence a
defaultEquivalence = Equivalence (==)

-- | Dual function arrows.
newtype Op a b = Op { getOp :: b -> a }
#ifdef __GLASGOW_HASKELL__
  deriving Typeable
#endif

instance Category Op where
  id = Op id
  Op f . Op g = Op (g . f)

instance Contravariant (Op a) where
  contramap f g = Op (getOp g . f)

