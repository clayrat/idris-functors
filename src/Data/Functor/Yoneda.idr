module Data.Functor.Yoneda

import Interfaces.Verified
import Control.Isomorphism

%access public export
%default total

record Yoneda (f : Type -> Type) (a : Type) where
  constructor MkYoneda 
  runYoneda : {b : Type} -> (a -> b) -> f b

liftYoneda : Functor f => f a -> Yoneda f a
liftYoneda fa = MkYoneda $ \f => map f fa

lowerYoneda : Yoneda f a -> f a
lowerYoneda (MkYoneda f) = f id

Functor f => Functor (Yoneda f) where
  map h (MkYoneda k) = MkYoneda $ flip map (k h)

Applicative f => Applicative (Yoneda f) where
  pure a = MkYoneda $ \f => pure (f a)
  (MkYoneda m) <*> (MkYoneda n) = MkYoneda $ \f => m (f .) <*> n id

{-
postulate
funext' : {a,b : t -> Type} -> {f, g : {x : t} -> a x -> b x} -> ({x : t} -> (y : a x) -> f y = g y) -> f = g

-- Yoneda lemma
isoYo : VerifiedFunctor f => Iso (Yoneda f a) (f a)
isoYo {a} = MkIso lowerYoneda liftYoneda (functorIdentity' {f}) froTo
  where 
  froTo : (x : Yoneda f a) -> MkYoneda (\f => map f (lowerYoneda x)) = x
  froTo (MkYoneda ry) = cong {f=MkYoneda} $ funext' {t=Type} {a=\x=>a->x} {b=f} {f=\h => map h (ry id)} {g=ry} ?wat 
-}