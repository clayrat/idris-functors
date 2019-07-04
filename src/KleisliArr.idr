-- https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf

module KleisliArr

import Control.Catchable
import Control.IOExcept
import Data.Vect

%access public export

infixr 1 :->

(:->) : (a, b : t -> Type) -> Type
(:->) {t} a b = {i : t} -> a i -> b i

Vec : Type -> Nat -> Type
Vec = flip Vect

vmap : (a -> b) -> (Vec a :-> Vec b)
vmap f = map f 

interface IFunctor (f : (i -> Type) -> o -> Type) where
  imap : (s :-> t) -> (f s :-> f t)

data Path : ((i,i) -> Type) -> (i,i) -> Type where
  Nil : Path e (i,i)
  (::) : e (i,j) -> Path e (j,k) -> Path e (i,k)

IFunctor Path where
  imap     f  Nil     = Nil
  imap {i} f (eij::p) = f eij :: imap {i=(i,i)} {o=(i,i)} f p

data AtKey : Type -> x -> x -> Type where
  V : a -> AtKey a i i

infixr 2 :=

(:=) : Type -> x -> x -> Type
(:=) = AtKey

List' : Type -> Type 
List' a = Path (a := ((),())) ((),()) 

interface IFunctor m => IMonad (m : (t -> Type) -> t -> Type) where
  iskip : p :-> m p
  iextend : (p :-> m q) -> (m p :-> m q)

iseq : IMonad m => (p :-> m q) -> (q :-> m r) -> (p :-> m r)
iseq f g = iextend g . f  

infixr 2 ?>=

(?>=) : IMonad m => m p i -> (p :-> m q) -> m q i 
c ?>= f = iextend f c

infixr 2 =>=

(=>=) : IMonad m => m (a := j) i -> (a -> m q j) -> m q i
c =>= f = c ?>= \(V a) => f a

interface IxMonad (m : t -> t -> Type -> Type) where 
  ixpure : x -> m i i x
  ixbind : m i j a -> (a -> m j k b) -> m i k b

Atkey : ((t -> Type) -> t -> Type) -> t -> t -> Type -> Type 
Atkey m i j a = m (a := j) i

ireturn : IMonad m => a -> Atkey m i i a
ireturn = iskip . V

[atk] IMonad m => IxMonad (Atkey m) where
  ixpure = ireturn
  ixbind = (=>=)

data State = Open | Closed

data IState : State -> Type where
  IOpen : IState Open
  IClosed : IState Closed

data Reach : (p, q, r : t -> Type) -> t -> Type where
  R : p i -> (q :-> r) -> Reach p q r i

infixr 2 :>>:

(:>>:) : (p, q, r : t -> Type) -> t -> Type
(:>>:) = Reach

IFunctor (Reach p q) where
  imap f (R pi g) = R pi (f . g)

data ISum : (f, g : (i -> Type) -> o -> Type) -> (i -> Type) -> o -> Type where 
  InL : f p i -> ISum f g p i
  InR : g p i -> ISum f g p i

infixr 3 :+:

(:+:) : (f, g : (i -> Type) -> o -> Type) -> (i -> Type) -> o -> Type
(:+:) = ISum

(IFunctor f, IFunctor g) => IFunctor (ISum f g) where
  imap h (InL fpi) = InL $ imap h fpi
  imap h (InR gpi) = InR $ imap h gpi

FilePath : Type
FilePath = String

FH : (State -> Type) -> State -> Type
FH =     ((FilePath := Closed) :>>: IState)         --fOpen
     :+: ((() := Open) :>>: ((Maybe Char) := Open)) --fGetC
     :+: ((() := Open) :>>: (() := Closed))         --fClose

data IFree : ((i -> Type) -> i -> Type) -> (i -> Type) -> i -> Type where
  Ret : p i -> IFree f p i
  Do : f (IFree f p) i -> IFree f p i

infixr 3 :*

(:*) : ((i -> Type) -> i -> Type) -> (i -> Type) -> i -> Type 
(:*) = IFree

IFunctor f => IFunctor (IFree f) where
  imap     h (Ret pi)     = Ret $ h pi
  imap {t} h (Do {p} fpi) = Do $ imap {s=IFree f p} {t=IFree f t} (imap h) fpi

IFunctor f => IMonad (IFree f) where
  iskip = Ret 
  iextend     h (Ret pi)     = h pi
  iextend {q} h (Do {p} fpi) = Do $ imap {s=IFree f p} {t=IFree f q} (iextend h) fpi

syntax FOpen [p] [k] = Do (InL (R (V p) k))
syntax FGetC [k] = Do (InR (InL (R (V ()) k)))
syntax FClose [k] = Do (InR (InR (R (V ()) k)))

fOpen : FilePath -> (FH :* IState) Closed
fOpen p = FOpen p Ret

fGetC : (FH :* ((Maybe Char) := Open)) Open
fGetC = FGetC Ret 

fClose : (FH :* (() := Closed)) Open
fClose = FClose Ret

runFH : (FH :* (a := Closed)) Closed -> IOExcept FileError a 
runFH (Ret (V a)) = pure a
runFH (FOpen s k) = catch
  (IOM (openFile s Read) >>= openFH (k IOpen)) 
  (\_ => runFH (k IClosed))
  where
  openFH : (FH :* (a := Closed)) Open -> File -> IOExcept FileError a
  openFH (FClose k) h = ioe_lift (closeFile h) *> runFH (k $ V ())
  openFH (FGetC k) h = catch
    (IOM (fgetc h) >>= \c => openFH (k $ V $ Just c) h)
    (\_ => openFH (k $ V Nothing) h)

interface IFunctor m => IApplicative (m : (t -> Type) -> t -> Type) where
  pure : x -> Atkey m i i x
  (<*>) : Atkey m i j (s -> t) -> Atkey m j k s -> Atkey m i k t

IFunctor f => IApplicative ((:*) f) where
  pure = ireturn
  mf <*> ms = mf =>= \f => ms =>= \s => ireturn $ f s
