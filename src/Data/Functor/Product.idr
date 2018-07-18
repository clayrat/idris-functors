module Data.Functor.Product

import Data.Functor.NatTrans

%access public export
%default total

data Product : (f : a -> b) -> (g : a -> b) -> (x : a) -> Type where
  MkProduct : f a -> g a -> Product f g a

projFst : Product f g ~> f
projFst (MkProduct fa _) = fa

projSnd : Product f g ~> g
projSnd (MkProduct _ ga) = ga

bihoistProduct : (f ~> h) -> (g ~> i) -> Product f g ~> Product h i
bihoistProduct natF natG (MkProduct fa ga) = MkProduct (natF fa) (natG ga)

(Show (f a), Show (g a)) => Show (Product f g a) where
  show (MkProduct fa ga) = "(product " ++ show fa ++ " " ++ show ga ++ ")"

(Functor f, Functor g) => Functor (Product f g) where
  map f (MkProduct fa ga) = MkProduct (map f fa) (map f ga)

(Applicative f, Applicative g) => Applicative (Product f g) where
  pure a = MkProduct (pure a) (pure a)
  (MkProduct ff gf) <*> (MkProduct fa ga) = MkProduct (ff <*> fa) (gf <*> ga)

(Monad f, Monad g) => Monad (Product f g) where
  (MkProduct fa ga) >>= f =
    MkProduct (fa >>= projFst . f) (ga >>= projSnd . f)

(Foldable f, Foldable g) => Foldable (Product f g) where
  foldr f z (MkProduct fa ga) = foldr f (foldr f z ga) fa

(Traversable f, Traversable g) => Traversable (Product f g) where
  traverse f (MkProduct fa ga) = [| MkProduct (traverse f fa) (traverse f ga) |]
