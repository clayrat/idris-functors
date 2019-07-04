module KleisliArr.Freer

import Control.Catchable
import Control.IOExcept
import KleisliArr.Basic

%access public export

data IFreer : ((j -> Type) -> j -> Type) -> (j -> Type) -> j -> Type where
  Ret : s i -> IFreer m s i
  Do : ({t : j -> Type} -> (s :-> IFreer m t) -> m (IFreer m t) i) -> IFreer m s i

infixr 3 :^

(:^) : ((i -> Type) -> i -> Type) -> (i -> Type) -> i -> Type 
(:^) = IFreer

IFunctor (IFreer f) where
  imap h (Ret pi) = Ret $ h pi
  imap h (Do fpi) = Do $ \k => fpi (k . h) 

IMonad (IFreer f) where
  iskip = Ret 
  iextend h (Ret pi) = h pi
  iextend h (Do fpi) = Do $ \k => fpi (iextend k . h)
