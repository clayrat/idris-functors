module Data.Profunctor.Coend

import Data.Profunctor
import Data.Bifunctor.Join

%access public export
%default partial

data Coend : (hom : a -> a -> Type) -> Type where 
    MkCoend : {a : Type} -> Joined hom a -> Coend hom

intoCoend : Profunctor hom => hom a a -> Coend hom
intoCoend hom = MkCoend $ Join hom 

fromCoend : Profunctor hom => Coend hom -> ({a : Type} -> hom a a -> r) -> r
fromCoend (MkCoend (Join hom)) k = k hom