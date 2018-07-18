module Data.Functor.Pairing

import Control.Monad.Identity
import Data.Functor.Product
import Data.Functor.Coproduct

%access public export
%default total

Pairing : (Type -> Type) -> (Type -> Type) -> Type
Pairing f g = {a, b, c : Type} -> (a -> b -> c) -> f a -> g b -> c

zap : Pairing f g -> f (a -> b) -> g a -> b
zap p = p apply

||| Pairing is symmetric
symPair : Pairing f g -> Pairing g f
symPair p f ga fb = p (flip f) fb ga
    
||| The identity functor pairs with itself
idPair : Pairing Identity Identity
idPair f (Id a) (Id b) = f a b

||| Functor products pair with functor coproducts
productCoproduct : Pairing f1 g1 -> Pairing f2 g2 -> Pairing (Product f1 f2) (Coproduct g1 g2)
productCoproduct p1 p2 f (MkProduct f1 f2) (LeftF g1) = p1 f f1 g1
productCoproduct p1 p2 f (MkProduct f1 f2) (RightF g2) = p2 f f2 g2

-- TODO stateStore 

-- TODO readerEnv 

-- TODO writerTraced 

-- TODO freeCofree 