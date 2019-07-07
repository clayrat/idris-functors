module Data.Functor.Yoneda

%access public export
%default total

record Yoneda (f : Type -> Type) (a : Type) where
  constructor MkYoneda 
  runYoneda : {b : Type} -> (a -> b) -> f b

liftYoneda : Functor f => f a -> Yoneda f a
liftYoneda a = MkYoneda $ \f => map f a

lowerYoneda : Yoneda f a -> f a
lowerYoneda (MkYoneda f) = f id

Functor f => Functor (Yoneda f) where
  map h (MkYoneda k) = MkYoneda $ flip map (k h)

Applicative f => Applicative (Yoneda f) where
  pure a = MkYoneda $ \f => pure (f a)
  (MkYoneda m) <*> (MkYoneda n) = MkYoneda $ \f => m (f .) <*> n id
