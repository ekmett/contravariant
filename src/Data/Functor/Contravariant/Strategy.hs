
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

data Strategy a where
  Strategy :: (a -> b) -> Strategy a

instance Contravariant Strategy where
  contramap f (Strategy g) = Strategy (g.f)

-- r0 = conquer
instance Divisible Strategy where
  conquer = Strategy (\_ -> ())
  divide f (Strategy g) (Strategy h) = Strategy $ \a -> case f a of
    (b, c) -> gb `pseq` hc `pseq` (gb, hc) -- hold onto the sparks
       where gb = g b
             hc = h c

instance Decidable Strategy where
  lose = Strategy
  decide f (Strategy g) (Strategy h) = Strategy (bimap g h . f)

rdeepseq :: NFData a => Strategy a
rdeepseq = Strategy rnf

rseq :: Strategy a
rseq = Strategy $ \a -> seq a a

using :: a -> Strategy a -> a
using a (Strategy f) = f a `pseq` a

newtype Eval a = Search { runSearch :: forall b. (a -> b) -> a }
