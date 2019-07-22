module Data.Profunctor.Optic

import Data.Morphisms
import Data.Distributive
import Data.Profunctor
import Data.Profunctor.Closed
import Data.Profunctor.Grate

%access public export
%default total

Distributive f => Closed (UpStarred f) where
  closed (UpStar afb) = UpStar $ \xa => map applyMor $ distribute (Mor $ afb . xa)

collectOf : Distributive f => Grate {p=UpStarred f} s t a b -> (a -> f b) -> s -> f t
collectOf gr = runUpStar . gr . UpStar