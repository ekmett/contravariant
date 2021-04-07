{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE RankNTypes #-}

module Data.Functor.Contravariant.Strategy where

import Control.Arrow
import Control.DeepSeq
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

data Strategy a where
  Strategy :: (a -> b) -> Strategy a

instance Contravariant Strategy where
  contramap f (Strategy g) = Strategy (g.f)
  {-# inline contramap #-}

-- r0 = conquer
instance Divisible Strategy where
  conquer = Strategy \_ -> ()
  {-# inline conquer #-}
  divide f (Strategy g) (Strategy h) = Strategy \a -> case f a of
    (b, c) -> gb `pseq` hc `pseq` (gb, hc) -- hold onto the sparks
       where gb = g b
             hc = h c
  {-# inline divide #-}

instance Decidable Strategy where
  lose = Strategy
  {-# inline lose #-}
  choose f (Strategy g) (Strategy h) = Strategy ((g +++ h) . f)
  {-# inline choose #-}

rdeepseq :: NFData a => Strategy a
rdeepseq = Strategy rnf
{-# inline rdeepseq #-}

rseq :: Strategy a
rseq = Strategy id
{-# inline rseq #-}

using :: a -> Strategy a -> a
using a (Strategy f) = f a `pseq` a
{-# inline using #-}

-- newtype Eval a = Search { runSearch :: forall b. (a -> b) -> a }
