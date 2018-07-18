module Data.Functor.Coproduct

import Data.Functor.NatTrans

%access public export
%default total

data Compose : (f : b -> c) -> (g : a -> b) -> (x : a) -> Type where
  MkCompose : f (g a) -> Compose f g a

bihoistCompose : Functor f => (f ~> h) -> (g ~> i) -> Compose f g ~> Compose h i
bihoistCompose natF natG (MkCompose fga) = MkCompose (natF (map natG fga))  

Show (f (g a)) => Show (Compose f g a) where
  show (MkCompose fga) = "(compose " ++ show fga ++ ")"

(Functor f, Functor g) => Functor (Compose f g) where
  map f (MkCompose fga) = MkCompose $ map (map f) fga  

(Applicative f, Applicative g) => Applicative (Compose f g) where
  pure = MkCompose . pure . pure  
  (MkCompose f) <*> (MkCompose x) = MkCompose $ [| f <*> x |]

(Alternative f, Applicative g) => Alternative (Compose f g) where  
  empty = MkCompose empty
  (MkCompose a) <|> (MkCompose b) = MkCompose $ a <|> b

(Foldable f, Foldable g) => Foldable (Compose f g) where
    foldr f i (MkCompose fga) = foldr (flip (foldr f)) i fga  

(Traversable f, Traversable g) => Traversable (Compose f g) where
    traverse f (MkCompose fga) = map MkCompose $ traverse (traverse f) fga

-- rightfolded composition
 
data ComposeRF : (f : Type -> Type) -> Nat -> (Type -> Type) where
  CRFZ : a -> ComposeRF f Z a
  CRFS : Compose f (ComposeRF f n) a -> ComposeRF f (S n) a

Functor f => Functor (ComposeRF f n) where
  map h (CRFZ a) = CRFZ $ h a
  map h (CRFS as) = CRFS $ map h as

Applicative f => Applicative (ComposeRF f n) where
  pure {n=Z}   a = CRFZ a
  pure {n=S _} a = CRFS $ pure a
  (CRFZ f) <*> (CRFZ x) = CRFZ $ f x
  (CRFS fs) <*> (CRFS xs) = CRFS $ fs <*> xs
  
-- leftfolded composition

data ComposeLF : (f : Type -> Type) -> Nat -> (Type -> Type) where
  CLFZ : a -> ComposeLF f Z a
  CLFS : ComposeLF f n (f a) -> ComposeLF f (S n) a

Functor f => Functor (ComposeLF f n) where
  map h (CLFZ a) = CLFZ (h a)
  map h (CLFS r) = CLFS (map (map h) r)

Applicative f => Applicative (ComposeLF f n) where
  pure {n=Z}   a = CLFZ a
  pure {n=S k} a = CLFS (pure (pure a))
  (CLFZ f) <*> (CLFZ x) = CLFZ (f x)
  (CLFS fs) <*> (CLFS xs) = CLFS (liftA2 (<*>) fs xs)
  