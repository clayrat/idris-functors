module Data.Functor.FunDay

--import Control.Isomorphism
--import Control.Monad.Identity
--import Control.Comonad
--import Control.Comonad.Trans
--import Data.Functor.NatTrans
--import Data.Functor.Pairing

%access public export
%default total

record FunDay (f : Type -> Type) (g : Type -> Type) (a : Type) where
  constructor MkFunDay
  runFunDay : {x, y : Type} -> (a -> x -> y) -> f x -> g y

runFunDay : Applicative f => FunDay f g a -> g a
runFunDay funday = runFunDay funday const $ pure ()