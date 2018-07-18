module Data.Functor.Coproduct

import Data.Functor.NatTrans

%access public export
%default total

data Coproduct : (f : a -> b) -> (g : a -> b) -> (x : a) -> Type where
  LeftF  : f a -> Coproduct f g a
  RightF : g a -> Coproduct f g a

coproduct : (f a -> b) -> (g a -> b) -> Coproduct f g a -> b
coproduct f _ (LeftF fa) = f fa
coproduct _ g (RightF ga) = g ga
  
bihoistCoproduct : (f ~> h) -> (g ~> i) -> Coproduct f g ~> Coproduct h i
bihoistCoproduct natF natG (LeftF fa)  = LeftF (natF fa)
bihoistCoproduct natF natG (RightF ga) = RightF (natG ga)

(Show (f a), Show (g a)) => Show (Coproduct f g a) where
  show (LeftF fa) = "(left " ++ show fa ++ ")"
  show (RightF ga) = "(right " ++ show ga ++ ")"

(Functor f, Functor g) => Functor (Coproduct f g) where
  map f (LeftF fa)  = LeftF (map f fa)
  map f (RightF ga) = RightF (map f ga)

(Foldable f, Foldable g) => Foldable (Coproduct f g) where
  foldr f z = coproduct (foldr f z) (foldr f z)  

(Traversable f, Traversable g) => Traversable (Coproduct f g) where
  traverse f = coproduct (map LeftF . traverse f) (map RightF . traverse f)  

-- TODO comonad