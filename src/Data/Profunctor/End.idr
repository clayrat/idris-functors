module Data.Profunctor.End

import Control.Category
import Data.Morphisms
import Data.Profunctor

%access public export
%default partial

data End : (hom : a -> a -> Type) -> Type where 
  MkEnd : ({a : Type} -> hom a a) -> End hom

intoEnd : Profunctor hom => ({a : Type} -> hom a a) -> End hom
intoEnd hom = MkEnd hom

fromEnd : Profunctor hom => End hom -> hom a a
fromEnd (MkEnd hom) = hom

data NatF : (hom : a -> a -> Type) -> (f, g : a -> a) -> (x, y : a) -> Type where
  MkNatF : hom (f x) (g y) -> NatF hom f g x y

(Profunctor hom, Functor f, Functor g) => Profunctor (NatF hom f g) where
  dimap fl fr (MkNatF h) = MkNatF (dimap (map fl) (map fr) h)

NatPro : (hom : a -> a -> Type) -> (f, g : a -> a) -> Type
NatPro hom f g = End (NatF hom f g)

intoNatPro : (Profunctor hom, Functor f, Functor g) => ({a : Type} -> hom (f a) (g a)) -> NatPro hom f g
intoNatPro hom = intoEnd (MkNatF hom)

fromNatPro : (Profunctor hom, Functor f, Functor g) => NatPro hom f g -> hom (f a) (g a)
fromNatPro {a} e with (fromEnd {a} e)
  | MkNatF h = h

idnNatPro : (Profunctor hom, Category hom, Functor f) => NatPro hom f f
idnNatPro = intoNatPro id

cmpNatPro : (Profunctor hom, Category hom, Functor f, Functor g, Functor h) => NatPro hom g h -> NatPro hom f g -> NatPro hom f h
cmpNatPro g f = intoNatPro (fromNatPro g . fromNatPro f)

NatT : (f, g : Type -> Type) -> Type
NatT f g = NatPro Morphism f g

intoNat : (Functor f, Functor g) => ({a : Type} -> f a -> g a) -> NatT f g
intoNat fg = intoNatPro $ Mor fg

fromNat : (Functor f, Functor g) => NatT f g -> (f a -> g a)
fromNat nfg = applyMor $ fromNatPro nfg

idnNat : Functor f => NatT f f
idnNat = idnNatPro 

cmpNat : (Functor f, Functor g, Functor h) => NatT g h -> NatT f g -> NatT f h
cmpNat = cmpNatPro