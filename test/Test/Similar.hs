{-# LANGUAGE DefaultSignatures #-}

module Test.Similar where

import Hedgehog
import GHC.Stack


-- | Fails the test if the two arguments are not equal, allowing for a small
-- amount of floating point inaccuracy.
--
infix 4 ~~~
(~~~) :: (MonadTest m, Similar a, Show a, HasCallStack) => a -> a -> m ()
a ~~~ b = withFrozenCallStack $ Sim a === Sim b

newtype Sim a = Sim a

instance Similar a => Eq (Sim a) where
  Sim a == Sim b = a ~= b

instance Show a => Show (Sim a) where
  show (Sim a) = show a


-- | A class of things that support almost-equality, so that we can disregard
-- small amounts of floating-point round-off error.
--
class Similar a where
  {-# INLINE (~=) #-}
  (~=) :: a -> a -> Bool
  default (~=) :: Eq a => a -> a -> Bool
  (~=) = (==)

infix 4 ~=

instance Similar Float where
  (~=) = absRelTol 0.00005 0.005

instance Similar a => Similar (Maybe a) where
  Nothing ~= Nothing = True
  Just x  ~= Just y  = x ~= y
  _       ~= _       = False

instance Similar a => Similar [a] where
  []     ~= []     = True
  (x:xs) ~= (y:ys) = x ~= y && xs ~= ys
  _      ~= _      = False

{-# INLINEABLE absRelTol #-}
absRelTol :: RealFloat a => a -> a -> a -> a -> Bool
absRelTol epsilonAbs epsilonRel u v
  |  isInfinite u
  && isInfinite v          = True
  |  isNaN u
  && isNaN v               = True
  | abs (u-v) < epsilonAbs = True
  | abs u > abs v          = abs ((u-v) / u) < epsilonRel
  | otherwise              = abs ((v-u) / v) < epsilonRel

