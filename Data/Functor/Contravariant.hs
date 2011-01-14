-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Contravariant
-- Copyright   :  (C) 2007-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
----------------------------------------------------------------------------

module Data.Functor.Contravariant ( 
  -- * Contravariant Functors
    Contravariant(..)
  
  -- * Predicates are contravariant
  , Predicate(..)

  -- * Orderings are contravariant
  , Comparison(..)
  , defaultComparison
  -- * Equality quotients are contravariant
  , Equality(..)
  , defaultEquality
  ) where

class Contravariant f where
  contramap :: (a -> b) -> f b -> f a 

-- | Predicates are contravariant functors, because you can apply the contramapped function
-- to the input of the predicate.
newtype Predicate a = Predicate { getPredicate :: a -> Bool } 
instance Contravariant Predicate where
  contramap f g = Predicate $ getPredicate g . f

-- | Comparisons are contravariant functors, because you can apply the contramapped function
-- to each input to the comparison function.
newtype Comparison a = Comparison { getComparison :: a -> a -> Ordering } 
instance Contravariant Comparison where
  contramap f g = Comparison $ \a b -> getComparison g (f a) (f b)

-- | Compare using 'compare'
defaultComparison :: Ord a => Comparison a
defaultComparison = Comparison compare

-- | Comparisons are contravariant functors, because you can apply the contramapped function
-- to each input to the equality comparison function.
newtype Equality a = Equality { getEquality :: a -> a -> Bool } 
instance Contravariant Equality where
  contramap f g = Equality $ \a b -> getEquality g (f a) (f b)

-- | Check for equality with '=='
defaultEquality :: Eq a => Equality a
defaultEquality = Equality (==)
