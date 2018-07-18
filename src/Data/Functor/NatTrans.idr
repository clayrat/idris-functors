module Data.Functor.NatTrans

%access public export
%default total

infixr 4 ~>

(~>) : (Type -> Type) -> (Type -> Type) -> Type
(~>) f g = {a : Type} -> f a -> g a
