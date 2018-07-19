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