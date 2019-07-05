module Data.Functor.Adjunction

import Data.Morphisms
import Interfaces.Verified 
import Control.Comonad
import Data.Functor.Compose

%access public export
%default total

interface (Functor f, Functor g) => Adjunction (f : Type -> Type) (g : Type -> Type) where
  unit : a -> g (f a)
  counit : f (g a) -> a
  left : (f a -> b) -> a -> g b
  right : (a -> g b) -> f a -> b

  unit = left id
  counit = right id
  left f = map f . unit
  right f = counit . map f

(Adjunction f1 g1, Adjunction f2 g2) => Adjunction (Compose f2 f1) (Compose g1 g2) where
  unit = MkCompose . map (map MkCompose . unit) . unit {f=f1} {g=g1}
  counit = counit {f=f2} {g=g2} . map (counit . map runCompose) . runCompose

[adjapp] Adjunction f g => Applicative (Compose g f) where
  pure = MkCompose . unit
  (MkCompose h) <*> (MkCompose x) = MkCompose $ map (right (\ab => map (map ab) x)) h

using implementation adjapp
  Adjunction f g => Monad (Compose g f) where
    (MkCompose a) >>= f = MkCompose $ map counit $ map (map (runCompose . f)) a

Adjunction f g => Comonad (Compose f g) where
  extract (MkCompose x) = counit x
  duplicate (MkCompose x) = MkCompose $ map (map MkCompose . unit) x

-- state monad / store comonad
Adjunction (Pair s) (Morphism s) where
  unit a = Mor $ \s => (s, a)
  counit (s, Mor sa) = sa s

interface (VerifiedFunctor f, VerifiedFunctor g, Adjunction f g) => VerifiedAdjunction (f : Type -> Type) (g : Type -> Type) where
  counitUnit : (x : f a) -> counit {f} {g} (map Adjunction.unit x) = x
  unitCounit : (x : g a) -> map (counit {f} {g}) (unit x) = x    

-- TODO next 2 already exist in latest stdlib  
-- interface Functor f => VerifiedFunctor' (f : Type -> Type) where
--   functorIdentity' : {a : Type} -> (g : a -> a) -> ((v : a) -> g v = v) -> (x : f a) -> map g x = x
-- 
-- VerifiedFunctor (Pair a) where
--   functorIdentity (a,b) = Refl
--   functorComposition (a,b) g1 g2 = Refl  

postulate
funext : {a,b : Type} -> {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

VerifiedFunctor (Morphism r) where
--  functorIdentity (Mor ra) = cong $ funext {f=\x => ra x} {g=ra} $ \x => Refl
  functorIdentity g p (Mor ra) = cong $ funext {f=\x =>g (ra x)} {g=ra} $ \x => p (ra x)
  functorComposition (Mor ra) g1 g2 = Refl

VerifiedAdjunction (Pair s) (Morphism s) where
  counitUnit (_, _) = Refl
  unitCounit x@(Mor _) = functorIdentity' x
