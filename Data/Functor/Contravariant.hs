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
-- 'Contravariant' functors, sometimes referred to colloquially as @Cofunctor@,
-- even though the dual of a 'Functor' is just a 'Functor'. As with 'Functor'
-- the definition of 'Contravariant' for a given ADT is unambiguous.
----------------------------------------------------------------------------

module Data.Functor.Contravariant ( 
  -- * Contravariant Functors
    Contravariant(..)
  
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



newtype Predicate a = Predicate { getPredicate :: a -> Bool } 
-- | A 'Predicate' is a 'Contravariant' 'Functor', because 'contramap' can 
-- apply its function argument to the input of the predicate.
instance Contravariant Predicate where
  contramap f g = Predicate $ getPredicate g . f



-- | Defines a total ordering on a type as per 'compare'
newtype Comparison a = Comparison { getComparison :: a -> a -> Ordering } 

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

instance Contravariant (Op a) where
  contramap f g = Op (getOp g . f)
