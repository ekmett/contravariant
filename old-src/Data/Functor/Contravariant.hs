{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}

#ifdef __GLASGOW_HASKELL__
#define LANGUAGE_DeriveDataTypeable
{-# LANGUAGE DeriveDataTypeable #-}
#endif

#ifndef MIN_VERSION_tagged
#define MIN_VERSION_tagged(x,y,z) 1
#endif

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(x,y,z) 1
#endif

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#elif __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif

#if !(MIN_VERSION_transformers(0,6,0))
{-# OPTIONS_GHC -fno-warn-deprecations #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Contravariant
-- Copyright   :  (C) 2007-2015 Edward Kmett
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
  , phantom

  -- * Operators
  , (>$<), (>$$<), ($<)

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

import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.RWS.Lazy as Lazy
import qualified Control.Monad.Trans.RWS.Strict as Strict
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import qualified Control.Monad.Trans.Writer.Strict as Strict

import Data.Function (on)

import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Constant
import Data.Functor.Compose
import Data.Functor.Reverse

#if !(MIN_VERSION_transformers(0,6,0))
import Control.Monad.Trans.Error
import Control.Monad.Trans.List
#endif

#if MIN_VERSION_base(4,8,0)
import Data.Monoid (Alt(..))
#else
import Data.Monoid (Monoid(..))
#endif

#if defined(MIN_VERSION_semigroups) || __GLASGOW_HASKELL__ >= 711
import Data.Semigroup (Semigroup(..))
#endif

#ifdef LANGUAGE_DeriveDataTypeable
import Data.Typeable
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 707 && defined(VERSION_tagged)
import Data.Proxy
#endif

#ifdef MIN_VERSION_StateVar
import Data.StateVar
#endif

#if __GLASGOW_HASKELL__ >= 702
#define GHC_GENERICS
import GHC.Generics
#endif

import Prelude hiding ((.),id)

-- | The class of contravariant functors.
--
-- Whereas in Haskell, one can think of a 'Functor' as containing or producing
-- values, a contravariant functor is a functor that can be thought of as
-- /consuming/ values.
--
-- As an example, consider the type of predicate functions  @a -> Bool@. One
-- such predicate might be @negative x = x < 0@, which
-- classifies integers as to whether they are negative. However, given this
-- predicate, we can re-use it in other situations, providing we have a way to
-- map values /to/ integers. For instance, we can use the @negative@ predicate
-- on a person's bank balance to work out if they are currently overdrawn:
--
-- @
-- newtype Predicate a = Predicate { getPredicate :: a -> Bool }
--
-- instance Contravariant Predicate where
--   contramap f (Predicate p) = Predicate (p . f)
--                                          |   `- First, map the input...
--                                          `----- then apply the predicate.
--
-- overdrawn :: Predicate Person
-- overdrawn = contramap personBankBalance negative
-- @
--
-- Any instance should be subject to the following laws:
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

-- | If 'f' is both 'Functor' and 'Contravariant' then by the time you factor in the laws
-- of each of those classes, it can't actually use its argument in any meaningful capacity.
--
-- This method is surprisingly useful. Where both instances exist and are lawful we have
-- the following laws:
--
-- @
-- 'fmap' f ≡ 'phantom'
-- 'contramap' f ≡ 'phantom'
-- @
phantom :: (Functor f, Contravariant f) => f a -> f b
phantom x = () <$ x $< ()

infixl 4 >$, $<, >$<, >$$<

-- | This is '>$' with its arguments flipped.
($<) :: Contravariant f => f b -> b -> f a
($<) = flip (>$)
{-# INLINE ($<) #-}

-- | This is an infix alias for 'contramap'.
(>$<) :: Contravariant f => (a -> b) -> f b -> f a
(>$<) = contramap
{-# INLINE (>$<) #-}

-- | This is an infix version of 'contramap' with the arguments flipped.
(>$$<) :: Contravariant f => f b -> (a -> b) -> f a
(>$$<) = flip contramap
{-# INLINE (>$$<) #-}

#if MIN_VERSION_base(4,8,0)
instance Contravariant f => Contravariant (Alt f) where
  contramap f = Alt . contramap f . getAlt
#endif

#ifdef GHC_GENERICS
instance Contravariant V1 where
  contramap _ x = x `seq` undefined

instance Contravariant U1 where
  contramap _ _ = U1

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

instance Contravariant m => Contravariant (ExceptT e m) where
  contramap f = ExceptT . contramap (fmap f) . runExceptT

instance Contravariant f => Contravariant (IdentityT f) where
  contramap f = IdentityT . contramap f . runIdentityT

instance Contravariant m => Contravariant (MaybeT m) where
  contramap f = MaybeT . contramap (fmap f) . runMaybeT

instance Contravariant m => Contravariant (Lazy.RWST r w s m) where
  contramap f m = Lazy.RWST $ \r s ->
    contramap (\ ~(a, s', w) -> (f a, s', w)) $ Lazy.runRWST m r s

instance Contravariant m => Contravariant (Strict.RWST r w s m) where
  contramap f m = Strict.RWST $ \r s ->
    contramap (\ (a, s', w) -> (f a, s', w)) $ Strict.runRWST m r s

instance Contravariant m => Contravariant (ReaderT r m) where
  contramap f = ReaderT . fmap (contramap f) . runReaderT

instance Contravariant m => Contravariant (Lazy.StateT s m) where
  contramap f m = Lazy.StateT $ \s ->
    contramap (\ ~(a, s') -> (f a, s')) $ Lazy.runStateT m s

instance Contravariant m => Contravariant (Strict.StateT s m) where
  contramap f m = Strict.StateT $ \s ->
    contramap (\ (a, s') -> (f a, s')) $ Strict.runStateT m s

instance Contravariant m => Contravariant (Lazy.WriterT w m) where
  contramap f = Lazy.mapWriterT $ contramap $ \ ~(a, w) -> (f a, w)

instance Contravariant m => Contravariant (Strict.WriterT w m) where
  contramap f = Strict.mapWriterT $ contramap $ \ (a, w) -> (f a, w)

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

#if !(MIN_VERSION_transformers(0,6,0))
instance Contravariant m => Contravariant (ErrorT e m) where
  contramap f = ErrorT . contramap (fmap f) . runErrorT

instance Contravariant m => Contravariant (ListT m) where
  contramap f = ListT . contramap (fmap f) . runListT
#endif

#ifdef MIN_VERSION_StateVar
instance Contravariant SettableStateVar where
  contramap f (SettableStateVar k) = SettableStateVar (k . f)
  {-# INLINE contramap #-}
#endif

#if (__GLASGOW_HASKELL__ >= 707) || defined(VERSION_tagged)
instance Contravariant Proxy where
  contramap _ _ = Proxy
#endif

newtype Predicate a = Predicate { getPredicate :: a -> Bool }
#ifdef LANGUAGE_DeriveDataTypeable
  deriving Typeable
#endif

-- | A 'Predicate' is a 'Contravariant' 'Functor', because 'contramap' can
-- apply its function argument to the input of the predicate.
instance Contravariant Predicate where
  contramap f g = Predicate $ getPredicate g . f

#if defined(MIN_VERSION_semigroups) || __GLASGOW_HASKELL__ >= 711
instance Semigroup (Predicate a) where
  Predicate p <> Predicate q = Predicate $ \a -> p a && q a
#endif

instance Monoid (Predicate a) where
  mempty = Predicate $ const True
#if defined(MIN_VERSION_semigroups) || __GLASGOW_HASKELL__ >= 711
  mappend = (<>)
#else
  mappend (Predicate p) (Predicate q) = Predicate $ \a -> p a && q a
#endif

-- | Defines a total ordering on a type as per 'compare'.
--
-- This condition is not checked by the types. You must ensure that the supplied
-- values are valid total orderings yourself.
newtype Comparison a = Comparison { getComparison :: a -> a -> Ordering }
#ifdef LANGUAGE_DeriveDataTypeable
  deriving Typeable
#endif

-- | A 'Comparison' is a 'Contravariant' 'Functor', because 'contramap' can
-- apply its function argument to each input of the comparison function.
instance Contravariant Comparison where
  contramap f g = Comparison $ on (getComparison g) f

#if defined(MIN_VERSION_semigroups) || __GLASGOW_HASKELL__ >= 711
instance Semigroup (Comparison a) where
  Comparison p <> Comparison q = Comparison $ mappend p q
#endif

instance Monoid (Comparison a) where
  mempty = Comparison (\_ _ -> EQ)
  mappend (Comparison p) (Comparison q) = Comparison $ mappend p q

-- | Compare using 'compare'.
defaultComparison :: Ord a => Comparison a
defaultComparison = Comparison compare

-- | This data type represents an equivalence relation.
--
-- Equivalence relations are expected to satisfy three laws:
--
-- __Reflexivity__:
--
-- @
-- 'getEquivalence' f a a = True
-- @
--
-- __Symmetry__:
--
-- @
-- 'getEquivalence' f a b = 'getEquivalence' f b a
-- @
--
-- __Transitivity__:
--
-- If @'getEquivalence' f a b@ and @'getEquivalence' f b c@ are both 'True' then so is @'getEquivalence' f a c@
--
-- The types alone do not enforce these laws, so you'll have to check them yourself.
newtype Equivalence a = Equivalence { getEquivalence :: a -> a -> Bool }
#ifdef LANGUAGE_DeriveDataTypeable
  deriving Typeable
#endif

-- | Equivalence relations are 'Contravariant', because you can
-- apply the contramapped function to each input to the equivalence
-- relation.
instance Contravariant Equivalence where
  contramap f g = Equivalence $ on (getEquivalence g) f

#if defined(MIN_VERSION_semigroups) || __GLASGOW_HASKELL__ >= 711
instance Semigroup (Equivalence a) where
  Equivalence p <> Equivalence q = Equivalence $ \a b -> p a b && q a b
#endif

instance Monoid (Equivalence a) where
  mempty = Equivalence (\_ _ -> True)
  mappend (Equivalence p) (Equivalence q) = Equivalence $ \a b -> p a b && q a b

-- | Check for equivalence with '=='.
--
-- Note: The instances for 'Double' and 'Float' violate reflexivity for @NaN@.
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

#if defined(MIN_VERSION_semigroups) || __GLASGOW_HASKELL__ >= 711
instance Semigroup a => Semigroup (Op a b) where
  Op p <> Op q = Op $ \a -> p a <> q a
#endif

instance Monoid a => Monoid (Op a b) where
  mempty = Op (const mempty)
  mappend (Op p) (Op q) = Op $ \a -> mappend (p a) (q a)

#if MIN_VERSION_base(4,5,0)
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
#endif
