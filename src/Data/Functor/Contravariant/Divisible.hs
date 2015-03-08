{-# LANGUAGE CPP #-}
module Data.Functor.Contravariant.Divisible
  (
  -- * Contravariant Applicative
    Divisible(..), divided, conquered, liftD
  -- * Contravariant Alternative
  , Decidable(..), chosen, lost
  ) where

import Data.Functor.Contravariant

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid
#endif

import Data.Void

#if MIN_VERSION_foreign_var
import Foreign.Var
#endif

--------------------------------------------------------------------------------
-- * Contravariant Applicative
--------------------------------------------------------------------------------

-- |
--
-- A 'Divisible' contravariant functor is the contravariant analogue of 'Applicative'.
--
-- In denser jargon, a 'Divisible' contravariant functor is a monoid object in the category
-- of presheaves from Hask to Hask, equipped with Day convolution mapping the Cartesian
-- product of the source to the Cartesian product of the target.
--
-- By way of contrast, an 'Applicative' functor can be viewed as a monoid object in the
-- category of copresheaves from Hask to Hask, equipped with Day convolution mapping the
-- Cartesian product of the source to the Cartesian product of the target.
--
-- Given the canonical diagonal morphism:
--
-- @
-- delta a = (a,a)
-- @
-- 
-- @'divide' 'delta'@ should be associative with 'conquer' as a unit
--
-- @
-- 'divide' 'delta' m 'conquer' = m
-- 'divide' 'delta' 'conquer' m = m
-- 'divide' 'delta' ('divide' 'delta' m n) o = 'divide' 'delta' m ('divide' 'delta' n o)
-- @
--
-- With more general arguments you'll need to reassociate and project using the monoidal
-- structure of the source category. (Here fst and snd are used in lieu of the more restricted
-- lambda and rho, but this construction works with just a monoidal category.)
--
-- @
-- 'divide' f m 'conquer' = 'contramap' ('fst' . f) m
-- 'divide' f 'conquer' m = 'contramap' ('snd' . f) m
-- 'divide' f ('divide' g m n) o = 'divide' f' m ('divide' 'id' n o) where
--   f' a = case f a of (bc,d) -> case g bc of (b,c) -> (a,(b,c))
-- @
class Contravariant f => Divisible f where
  divide  :: (a -> (b, c)) -> f b -> f c -> f a
  -- | The underlying theory would suggest that this should be:
  --
  -- @
  -- conquer :: (a -> ()) -> f a
  -- @
  --
  -- However, as we are working over a Cartesian category (Hask) and the Cartesian product, such an input
  -- morphism is uniquely determined to be @'const' 'mempty'@, so we elide it.
  conquer :: f a

-- |
-- @
-- 'divided' = 'divide' 'id'
-- @
divided :: Divisible f => f a -> f b -> f (a, b)
divided = divide id

-- | Redundant, but provided for symmetry.
--
-- @
-- 'conquered' = 'conquer
-- @
conquered :: Divisible f => f ()
conquered = conquer

-- |
-- This is the divisible analogue of 'liftA'. It gives a viable default definition for 'contramap' in terms
-- of the members of 'Divisible'.
--
-- @
-- 'liftD' f = 'divide' ((,) () . f) 'conquer'
-- @
liftD :: Divisible f => (a -> b) -> f b -> f a
liftD f = divide ((,) () . f) conquer
  
instance Monoid r => Divisible (Op r) where
  divide f (Op g) (Op h) = Op $ \a -> case f a of
    (b, c) -> g b `mappend` h c
  conquer = Op $ const mempty

instance Divisible Comparison where
  divide f (Comparison g) (Comparison h) = Comparison $ \a b -> case f a of
    (a',a'') -> case f b of
      (b',b'') -> g a' b' `mappend` h a'' b''
  conquer = Comparison $ \_ _ -> EQ

instance Divisible Equivalence where
  divide f (Equivalence g) (Equivalence h) = Equivalence $ \a b -> case f a of
    (a',a'') -> case f b of
      (b',b'') -> g a' b' && h a'' b''
  conquer = Equivalence $ \_ _ -> True

instance Divisible Predicate where
  divide f (Predicate g) (Predicate h) = Predicate $ \a -> case f a of
    (b, c) -> g b && h c
  conquer = Predicate $ const True

#if MIN_VERSION_foreign_var
instance Divisible SettableVar where
  divide k (SettableVar l) (SettableVar r) = SettableVar $ \ a -> case k a of
    (b, c) -> l b >> r c
  conquer = SettableVar $ \_ -> return ()
#endif

--------------------------------------------------------------------------------
-- * Contravariant Alternative
--------------------------------------------------------------------------------

-- |
--
-- A 'Divisible' contravariant functor is a monoid object in the category of presheaves 
-- from Hask to Hask, equipped with Day convolution mapping the cartesian product of the
-- source to the Cartesian product of the target.
--
-- @
-- 'choose' Left m ('lose' f)  = m
-- 'choose' Right ('lose' f) m = m
-- 'choose' f ('choose' g m n) o = 'divide' f' m ('divide' 'id' n o) where
--   f' bcd = 'either' ('either' 'id' ('Right' . 'Left') . g) ('Right' . 'Right') . f
-- @
--
-- In addition, we expect the same kind of distributive law as is satisfied by the usual
-- covariant 'Alternative', w.r.t 'Applicative', which should be fully formulated and
-- added here at some point!

class Divisible f => Decidable f where
  -- | The only way to win is not to play.
  lose :: (a -> Void) -> f a
  choose :: (a -> Either b c) -> f b -> f c -> f a

-- |
-- @
-- 'lost' = 'lose' 'id'
-- @
lost :: Decidable f => f Void
lost = lose id

-- |
-- @
-- 'chosen' = 'choose' 'id'
-- @
chosen :: Decidable f => f b -> f c -> f (Either b c)
chosen = choose id

instance Decidable Comparison where
  lose f = Comparison $ \a _ -> absurd (f a)
  choose f (Comparison g) (Comparison h) = Comparison $ \a b -> case f a of
    Left c -> case f b of
      Left d -> g c d
      Right{} -> LT
    Right c -> case f b of
      Left{} -> GT
      Right d -> h c d

instance Decidable Equivalence where
  lose f = Equivalence $ \a -> absurd (f a)
  choose f (Equivalence g) (Equivalence h) = Equivalence $ \a b -> case f a of
    Left c -> case f b of
      Left d -> g c d
      Right{} -> False
    Right c -> case f b of
      Left{} -> False
      Right d -> h c d

instance Decidable Predicate where
  lose f = Predicate $ \a -> absurd (f a)
  choose f (Predicate g) (Predicate h) = Predicate $ either g h . f

instance Monoid r => Decidable (Op r) where
  lose f = Op $ absurd . f
  choose f (Op g) (Op h) = Op $ either g h . f

#if MIN_VERSION_foreign_var
instance Decidable SettableVar where
  lose k = SettableVar (absurd . k)
  choose k (SettableVar l) (SettableVar r) = SettableVar $ \ a -> case k a of
    Left b -> l b
    Right c -> r c
#endif
