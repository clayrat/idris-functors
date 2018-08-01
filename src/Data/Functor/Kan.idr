module Data.Functor.Kan

import Control.Monad.Identity
import Control.Isomorphism
import Data.Functor.Day

%access public export
%default total

-- generalised continuation type 
-- often, but not always, the type constructors j and g are identical
record Ran (j : Type -> Type) (g : Type -> Type) (x : Type) where 
  constructor MkRan 
  runRan : {a : Type} -> (x -> j a) -> g a
  
Functor (Ran j g) where
  map f (MkRan h) = MkRan $ \k => h (k . f)
  
-- generalised abstract data type: `g a` is the internal state and `j a -> x` the observer function
-- again, the type constructors g and f are likely to be identical  
data Lan : (j : Type -> Type) -> (g : Type -> Type) -> (x : Type) -> Type where 
  MkLan : {a : Type} -> (j a -> x) -> g a -> Lan j g x   
  
Functor (Lan j g) where 
  map f (MkLan k s) = MkLan (f . k) s
  
-- Codensity and Yoneda are right Kan extensions

--record Yoneda (f : Type -> Type) (a : Type) where
--  constructor MkYoneda 
--  runYoneda : {b : Type} -> (a -> b) -> f b

Yoneda' : (f : Type -> Type) -> (a : Type) -> Type
Yoneda' = Ran Identity

--record Codensity (m : Type -> Type) (a : Type) where
--  constructor Codense
--  runCodensity : {b : Type} -> (a -> m b) -> m b
  
Codensity' : (f : Type -> Type) -> (a : Type) -> Type
Codensity' f = Ran f f

-- Coyoneda and density are left Kan extensions 

-- data Coyoneda : (f : Type -> Type) -> (a : Type) -> Type where
--   Coyo : {b : Type} -> (b -> a) -> f b -> Coyoneda f a

Coyoneda' : (f : Type -> Type) -> (a : Type) -> Type
Coyoneda' = Lan Identity

Density' : (f : Type -> Type) -> (a : Type) -> Type
Density' f = Lan f f

-- Dijkstra monad

record Dijkstra (s : Type) (x : Type) where
  constructor MkDijkstra 
  runDijkstra : {a : Type} -> (x -> s -> a) -> s -> a

Functor (Dijkstra s) where
  map f (MkDijkstra r) = MkDijkstra $ \bsa => r (bsa . f) 

Applicative (Dijkstra s) where
  pure a = MkDijkstra (\f => f a)
  (MkDijkstra rf) <*> (MkDijkstra ra) = MkDijkstra $ \bsa => rf (\ab => ra (bsa . ab)) 

Monad (Dijkstra s) where
  (MkDijkstra r) >>= f = MkDijkstra $ \bsa => r (\a => runDijkstra (f a) bsa)
    
Dijkstra' : (s : Type) -> (x : Type) -> Type
Dijkstra' s = Ran (\a => s -> a) (\a => s -> a)

-- TODO
{-  
record CrossProduct (f : Type -> Type) (g : Type -> Type) (a : Type) (b : Type) where
  constructor MkCrossProd
  runCrossProduct : (f a, g b)

record CrossCoproduct (f : Type -> Type) (g : Type -> Type) (a : Type) (b : Type) where
  constructor MkCrossCoprod
  runCrossProduct : Either (f a) (g b)

daylan : Iso (Day f g a) (Lan (Pair x) (CrossProduct f g x) a)
daylan = MkIso to fro toFro froTo 
  where
  to : Day f g a -> Lan (Pair x) (CrossProduct f g x) a
  to (MkDay {x} {y} h fx gy) = MkLan ?wat ?wat2 --(MkCrossProd (fx, gy))
  fro : Lan (Pair x) (CrossProduct f g x) a -> Day f g a
  toFro : (z : Lan (Pair x) (CrossProduct f g x) a) -> to (fro z) = z
  froTo : (z : Day f g a) -> fro (to z) = z
  
  Day f g       ~ Lan Tuple  (CrossProduct f g)
  Product f g   ~ Lan Either (CrossProduct f g)
  Coproduct f g ~ Lan Either (CrossCoproduct f g)
  
  Lan Tuple (CrossProduct f g) a
  ~ exists x y. (Tuple x y -> a, CrossProduct f g x y)
  ~ exists x y. (x -> y -> a, f x, g y)
  ~ Day f g a
  
  Lan Either (CrossProduct f g) a
  ~ exists x y. (Either x y -> a, CrossProduct f g x y)
  ~ exists x y. (x -> a, y -> a, f x, g y)
  ~ (f a, g a)
  ~ Product f g a
  
  Lan Either (CrossCoproduct f g) a
  ~ exists x y. (Either x y -> a, CrossCoproduct f g x y)
  ~ exists x y (x -> a, y -> a, Either (f x) (g y))
  ~ Either (f a) (g a)
  ~ Coproduct f g a
-}  
