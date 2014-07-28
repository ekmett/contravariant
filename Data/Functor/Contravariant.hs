{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}

#ifdef __GLASGOW_HASKELL__
#define LANGUAGE_DeriveDataTypeable
{-# LANGUAGE DeriveDataTypeable #-}
#endif

#ifndef MIN_VERSION_tagged
#define MIN_VERSION_tagged(x,y,z) 1
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702 && MIN_VERSION_transformers(0,3,0) && MIN_VERSION_tagged(0,6,1)
{-# LANGUAGE Safe #-}
#else
{-# LANGUAGE Trustworthy #-}
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
  , comparisonEquivalence

  -- * Dual arrows
  , Op(..)
  ) where

import Control.Applicative
import Control.Applicative.Backwards

import Control.Category

import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Constant
import Data.Functor.Compose
import Data.Functor.Reverse

import Data.Semigroup (Semigroup(..), Monoid(..))

#ifdef LANGUAGE_DeriveDataTypeable
import Data.Typeable
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 707 && defined(VERSION_tagged)
import Data.Proxy
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
#define GHC_GENERICS
import GHC.Generics
#endif

import Prelude hiding ((.),id)

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

  -- | Replace all locations in the output with the same value.
  -- The default definition is @'contramap' . 'const'@, but this may be
  -- overridden with a more efficient version.
  (>$) :: b -> f b -> f a
  (>$) = contramap . const

infixl 4 >$, >$<, >$$<

(>$<) :: Contravariant f => (a -> b) -> f b -> f a
(>$<) = contramap
{-# INLINE (>$<) #-}

(>$$<) :: Contravariant f => f b -> (a -> b) -> f a
(>$$<) = flip contramap
{-# INLINE (>$$<) #-}

#ifdef GHC_GENERICS
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
#endif

instance (Contravariant f, Contravariant g) => Contravariant (Sum f g) where
  contramap f (InL xs) = InL (contramap f xs)
  contramap f (InR ys) = InR (contramap f ys)

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

#if (defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707) || defined(VERSION_tagged)
instance Contravariant Proxy where
  contramap _ Proxy = Proxy
#endif

newtype Predicate a = Predicate { getPredicate :: a -> Bool }
#ifdef LANGUAGE_DeriveDataTypeable
  deriving Typeable
#endif

-- | A 'Predicate' is a 'Contravariant' 'Functor', because 'contramap' can
-- apply its function argument to the input of the predicate.
instance Contravariant Predicate where
  contramap f g = Predicate $ getPredicate g . f

-- | Defines a total ordering on a type as per 'compare'
newtype Comparison a = Comparison { getComparison :: a -> a -> Ordering }
#ifdef LANGUAGE_DeriveDataTypeable
  deriving Typeable
#endif

-- | A 'Comparison' is a 'Contravariant' 'Functor', because 'contramap' can
-- apply its function argument to each input to each input to the
-- comparison function.
instance Contravariant Comparison where
  contramap f g = Comparison $ \a b -> getComparison g (f a) (f b)

instance Semigroup (Comparison a) where
  Comparison p <> Comparison q = Comparison $ mappend p q

instance Monoid (Comparison a) where
  mempty = Comparison (\_ _ -> EQ)
  mappend (Comparison p) (Comparison q) = Comparison $ mappend p q

-- | Compare using 'compare'
defaultComparison :: Ord a => Comparison a
defaultComparison = Comparison compare

-- | Define an equivalence relation
newtype Equivalence a = Equivalence { getEquivalence :: a -> a -> Bool }
#ifdef LANGUAGE_DeriveDataTypeable
  deriving Typeable
#endif

-- | Equivalence relations are 'Contravariant', because you can
-- apply the contramapped function to each input to the equivalence
-- relation.
instance Contravariant Equivalence where
  contramap f g = Equivalence $ \a b -> getEquivalence g (f a) (f b)

instance Semigroup (Equivalence a) where
  Equivalence p <> Equivalence q = Equivalence $ \a b -> p a b && q a b

instance Monoid (Equivalence a) where
  mempty = Equivalence (\_ _ -> True)
  mappend (Equivalence p) (Equivalence q) = Equivalence $ \a b -> p a b && q a b

-- | Check for equivalence with '=='
defaultEquivalence :: Eq a => Equivalence a
defaultEquivalence = Equivalence (==)

comparisonEquivalence :: Comparison a -> Equivalence a
comparisonEquivalence (Comparison p) = Equivalence $ \a b -> p a b == EQ

-- | Dual function arrows.
newtype Op a b = Op { getOp :: b -> a }
#ifdef LANGUAGE_DeriveDataTypeable
  deriving Typeable
#endif

instance Category Op where
  id = Op id
  Op f . Op g = Op (g . f)

instance Contravariant (Op a) where
  contramap f g = Op (getOp g . f)

instance Semigroup a => Semigroup (Op a b) where
  Op p <> Op q = Op $ \a -> p a <> q a

instance Monoid a => Monoid (Op a b) where
  mempty = Op (const mempty)
  mappend (Op p) (Op q) = Op $ \a -> mappend (p a) (q a)

instance Num a => Num (Op a b) where
  Op f + Op g = Op $ \a -> f a + g a
  Op f * Op g = Op $ \a -> f a * g a
  Op f - Op g = Op $ \a -> f a - g a
  abs (Op f) = Op $ abs . f
  signum (Op f) = Op $ signum . f
  fromInteger = Op . const . fromInteger

instance Fractional a => Fractional (Op a b) where
  Op f / Op g = Op $ \a -> f a / g a
  recip (Op f) = Op $ recip . f
  fromRational = Op . const . fromRational

instance Floating a => Floating (Op a b) where
  pi = Op $ const pi
  exp (Op f) = Op $ exp . f
  sqrt (Op f) = Op $ sqrt . f
  log (Op f) = Op $ log . f
  sin (Op f) = Op $ sin . f
  tan (Op f) = Op $ tan . f
  cos (Op f) = Op $ cos . f
  asin (Op f) = Op $ asin . f
  atan (Op f) = Op $ atan . f
  acos (Op f) = Op $ acos . f
  sinh (Op f) = Op $ sinh . f
  tanh (Op f) = Op $ tanh . f
  cosh (Op f) = Op $ cosh . f
  asinh (Op f) = Op $ asinh . f
  atanh (Op f) = Op $ atanh . f
  acosh (Op f) = Op $ acosh . f
  Op f ** Op g = Op $ \a -> f a ** g a
  logBase (Op f) (Op g) = Op $ \a -> logBase (f a) (g a)
