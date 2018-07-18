module Data.Functor.Day

import Control.Monad.Identity
import Control.Comonad
import Control.Comonad.Trans
import Data.Functor.NatTrans
import Data.Functor.Pairing

%access public export
%default total

data Day : (Type -> Type) -> (Type -> Type) -> Type -> Type where
  MkDay : (x -> y -> a) -> f x -> g y -> Day f g a

runDay : ({x, y : Type} -> (x -> y -> a) -> f x -> g y -> r) -> Day f g a -> r  
runDay f (MkDay get fx gy) = f get fx gy

day : (x -> y -> a) -> f x -> g y -> Day f g a
day get fx gy = MkDay get fx gy

dap : Applicative f => Day f f ~> f
dap (MkDay get fx gy) = [| get fx gy |]

||| Pair two `Day` convolutions when their components pair.
pairDay : Pairing f1 f2 -> Pairing g1 g2 -> Pairing (Day f1 g1) (Day f2 g2)
pairDay p1 p2 f (MkDay get1 fx1 gy1) (MkDay get2 fx2 gy2) = 
  let 
    (x1, x2) = p1 MkPair fx1 fx2
    (y1, y2) = p2 MkPair gy1 gy2
    in
  f (get1 x1 y1) (get2 x2 y2)

||| Hoist a natural transformation over the left hand side of a 'Day' convolution.
hoistDayL : (f ~> g) -> Day f h ~> Day g h
hoistDayL n (MkDay get fx gy) = day get (n fx) gy

||| Hoist a natural transformation over the right hand side of a 'Day' convolution.
hoistDayR : (f ~> g) -> Day h f ~> Day h g
hoistDayR n (MkDay get fx gy) = day get fx (n gy)

introDayL : f ~> Day Identity f
introDayL = day id (Id id)

introDayR : f ~> Day f Identity
introDayR f = day (flip apply) f (Id id)

elimDayL : Functor f => Day Identity f ~> f
elimDayL (MkDay get (Id x) fy) = get x <$> fy

elimDayR : Functor f => Day f Identity ~> f
elimDayR (MkDay get fx (Id y)) = flip get y <$> fx

symDay : Day f g ~> Day g f
symDay (MkDay get fx gy) = day (flip get) gy fx

assocDayL : Day f (Day g h) ~> Day (Day f g) h
assocDayL (MkDay phi fx (MkDay psi gy hz)) = 
  day id (day (\a, b, c => phi a (psi b c)) fx gy) hz

assocDayR : Day (Day f g) h ~> Day f (Day g h)
assocDayR (MkDay phi (MkDay psi fx gy) hz) = 
  day (flip apply) fx (day (\a, b, c => phi (psi c a) b) gy hz)

Functor (Day f g) where
  map f (MkDay get fx gy) = day (\x, y => f (get x y)) fx gy

(Applicative f, Applicative g) => Applicative (Day f g) where
  pure a = day (\_, _ => a) (pure ()) (pure ())
  (MkDay get1 f1 g1) <*> (MkDay get2 f2 g2) = 
    day (\(a1,a2),(b1,b2) => (get1 a1 b1) (get2 a2 b2)) 
        [| MkPair f1 f2 |] 
        [| MkPair g1 g2 |]

(Comonad f, Comonad g) => Comonad (Day f g) where
  extract (MkDay get fx gy) = 
    get (extract fx) (extract gy)
  extend f (MkDay get fx gy) = 
    map f $ day (day get) (duplicate fx) (duplicate gy)

Comonad f => ComonadTrans (Day f) where
  lower (MkDay get fx gy) = get (extract fx) <$> gy
