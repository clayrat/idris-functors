module Data.Distributive

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Morphisms

%access public export
%default total

-- Categorical dual of `Traversable`
interface Functor f => Distributive (f : Type -> Type) where
  collect : Functor g => (a -> f b) -> g a -> f (g b)
  collect f = distribute . map f
  distribute : Functor g => g (f a) -> f (g a)
  distribute = collect id

cotraverse : (Distributive f, Functor g) => (g a -> b) -> g (f a) -> f b
cotraverse f = map f . distribute

Distributive Identity where
  collect f = Id . map (runIdentity . f)
  distribute = Id . map runIdentity

Distributive (Morphism c) where
  collect f ga = Mor $ \c => map (flip apply c . applyMor . f) ga 
  distribute ga = Mor $ \c => map (flip apply c . applyMor) ga

Distributive f => Distributive (ReaderT r f) where
  collect f ga = RD $ \a => collect (\x => runReaderT (f x) a) ga
  distribute ga = RD $ \a => collect (flip runReaderT a) ga

