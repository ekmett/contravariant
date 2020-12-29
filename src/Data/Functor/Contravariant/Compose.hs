{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#elif __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-- |
-- Module      :  Data.Functor.Contravariant.Compose
-- Copyright   :  (c) Edward Kmett 2010
-- License     :  BSD3
--
-- Maintainer  :  ekmett@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Composition of contravariant functors.

module Data.Functor.Contravariant.Compose
  ( Compose(..)
  , ComposeFC(..)
  , ComposeCF(..)
  ) where

import Control.Arrow

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

-- | Composition of two contravariant functors
newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Contravariant f, Contravariant g) => Functor (Compose f g) where
   fmap f (Compose x) = Compose (contramap (contramap f) x)

-- | Composition of covariant and contravariant functors
newtype ComposeFC f g a = ComposeFC { getComposeFC :: f (g a) }

instance (Functor f, Contravariant g) => Contravariant (ComposeFC f g) where
    contramap f (ComposeFC x) = ComposeFC (fmap (contramap f) x)

instance (Functor f, Functor g) => Functor (ComposeFC f g) where
    fmap f (ComposeFC x) = ComposeFC (fmap (fmap f) x)

instance (Applicative f, Divisible g) => Divisible (ComposeFC f g) where
  conquer = ComposeFC $ pure conquer
  divide abc (ComposeFC fb) (ComposeFC fc) = ComposeFC $ divide abc <$> fb <*> fc

instance (Applicative f, Decidable g) => Decidable (ComposeFC f g) where
  lose f = ComposeFC $ pure (lose f)
  choose abc (ComposeFC fb) (ComposeFC fc) = ComposeFC $ choose abc <$> fb <*> fc

-- | Composition of contravariant and covariant functors
newtype ComposeCF f g a = ComposeCF { getComposeCF :: f (g a) }

instance (Contravariant f, Functor g) => Contravariant (ComposeCF f g) where
    contramap f (ComposeCF x) = ComposeCF (contramap (fmap f) x)

instance (Functor f, Functor g) => Functor (ComposeCF f g) where
    fmap f (ComposeCF x) = ComposeCF (fmap (fmap f) x)

instance (Divisible f, Applicative g) => Divisible (ComposeCF f g) where
  conquer = ComposeCF conquer
  divide abc (ComposeCF fb) (ComposeCF fc) = ComposeCF $ divide (funzip . fmap abc) fb fc

funzip :: Functor f => f (a, b) -> (f a, f b)
funzip = fmap fst &&& fmap snd
