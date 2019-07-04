module FSMCat

import Control.Category
import Data.Morphisms
import Data.Vect
import Interfaces.Verified

%access public export
%default total

-- from https://marcinszamotulski.me/posts/finite-state-machines.html

infixr 4 :.:

data Cat : (k -> k -> k) -> k -> k -> Type where
  Id : Cat f a a
  (:.:) : f b c -> Cat f a b -> Cat f a c

Category (Cat f) where
  id = Id
  Id . ys = ys
  (x :.: xs) . ys = x :.: (xs . ys)  

interface Category cat => VerifiedCategory (cat : k -> k -> Type) where
  leftUnit : {x : cat a b} -> Category.id . x = x
  rightUnit : {x : cat a b} -> x . Category.id = x
  assoc : {x : cat c d} -> {y : cat b c} -> {z : cat a b} -> (x . y) . z = x . (y . z)

VerifiedCategory (Cat f) where  
  leftUnit = Refl
  rightUnit {x=Id}      = Refl
  rightUnit {x=x :.: y} = cong $ rightUnit {x=y}
  assoc {x=Id}      = Refl
  assoc {x=x :.: y} = cong $ assoc {x=y}

endo : List (f a a) -> Cat f a a
endo [] = Id
endo (x :: xs) = x :.: endo xs  

liftCat : f a b -> Cat f a b
liftCat fab = fab :.: Id

foldFunCat : Category g => ({x, y: Type} -> f x y -> g x y) 
                        -- ^ a map of graphs
                        -> Cat f a b -> g a b
                        -- ^ a functor from 'Cat f' to 'g'
foldFunCat fun Id = id
foldFunCat fun (bc :.: ab) = fun bc . foldFunCat fun ab 

-- this boils down to rewriting with `monadLeftIdentity`, `monadRightIdentity` and `monadAssociativity`, but gets tricky due to funext 
{-
postulate 
funext : {a,b : Type} -> {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

VerifiedMonad m => VerifiedCategory (Kleislimorphism m) where
  leftUnit {x=Kleisli amb} = ?wat
  rightUnit {x=Kleisli amb} = ?wat2
  assoc {x=Kleisli cmd} {y=Kleisli bmc} {z=Kleisli amb} = ?wat3
-}  

-- TODO add to Data.Morphisms
arr : Monad m => (a -> b) -> Kleislimorphism m a b
arr f = Kleisli $ pure . f

foldFunKleisli : Monad m => ({x, y : Type} -> f x y -> Kleislimorphism m x y) -> Cat f a b -> Kleislimorphism m a b
foldFunKleisli = foldFunCat

data EndoCat : (c : k -> k -> Type) -> k -> Type where
  MkEndo : Category c => c a a -> EndoCat c a
  
Semigroup (EndoCat c a) where
  (MkEndo f) <+> (MkEndo g) = MkEndo (f . g)
  
Category c => Monoid (EndoCat c a) where
  neutral = MkEndo id

data Single : Type -> Type -> Type -> Type -> Type where
  MkSingle     : e    -> Single e v v v
  VoidSingle : Void -> Single e v a b

toList : Cat (Single e v) v v -> List e
toList Id                   = []
toList (MkSingle e :.: es)  = e :: toList es
toList (VoidSingle e :.: _) = absurd e

idSingle : Monoid e => Single e v v v
idSingle = MkSingle neutral

composeSingle : Monoid e => Single e v b c -> Single e v a b -> Single e v a c
composeSingle (MkSingle a)   (MkSingle b)   = MkSingle (a <+> b)
composeSingle (VoidSingle e)  _             = absurd e
composeSingle _              (VoidSingle e) = absurd e

Monoid e => Category (Single e v) where
  id {v} = really_believe_me $ idSingle {e} {v}
  (.) = composeSingle

-- FSM

CartItem : Type
CartItem = ()

Card : Type
Card = String

record NoItems where
  constructor MkNoItems

record HasItems where
  constructor MkHasItems 
  hasItems : Vect (S n) CartItem

record NoCard where
  constructor MkNoCard 
  noCard : Vect (S n) CartItem

record CardSelected where 
  constructor MkCardSelected 
  cardSel : (Card, Vect (S n) CartItem)

record CardConfirmed where
  constructor MkCardConfirmed 
  cardConf : (Card, Vect (S n) CartItem)

record OrderPlaced where 
  constructor MkOrderPlaced

data Tr : Type -> Type -> Type where
  SelectFirst : CartItem -> Tr NoItems HasItems
  Select      : CartItem -> Tr HasItems HasItems
  SelectCard  : Card -> Tr HasItems CardSelected
  Confirm     : Tr CardSelected CardConfirmed
  PlaceOrder  : Tr CardConfirmed OrderPlaced
  Cancel      : Tr s NoItems  

ShoppingCat : Type -> Type -> Type 
ShoppingCat a b = Cat Tr a b  

natPure : Tr a b -> (a ~> b)
natPure (SelectFirst i) = Mor $ \_                        => MkHasItems [i]
natPure (Select i)      = Mor $ \(MkHasItems is)          => MkHasItems (i :: is)
natPure (SelectCard c)  = Mor $ \(MkHasItems is)          => MkCardSelected (c, is)
natPure  Confirm        = Mor $ \(MkCardSelected (c, is)) => MkCardConfirmed (c, is)
natPure  PlaceOrder     = Mor $ \_                        => MkOrderPlaced
natPure  Cancel         = Mor $ \_                        => MkNoItems

checkoutPure : ShoppingCat a b -> a -> b
checkoutPure = applyMor . foldFunCat natPure

natKl : Monad m => Tr x y -> Kleislimorphism m x y
natKl xy = arr $ applyMor $ natPure xy

checkoutM : Monad m => ShoppingCat a b -> a -> m b
checkoutM = applyKleisli . foldFunCat natKl

interface Category c => ShoppingCatT (c : Type -> Type -> Type) where
  selectFirst : CartItem -> c NoItems HasItems
  select      : CartItem -> c HasItems HasItems
  selectCard  : Card -> c HasItems CardSelected
  confirm     : c CardSelected CardConfirmed
  placeOrder  : c CardConfirmed OrderPlaced
  cancel      : c s NoItems

ShoppingCatT (Cat Tr) where
  selectFirst = liftCat . SelectFirst
  select      = liftCat . Select
  selectCard  = liftCat . SelectCard
  confirm     = liftCat Confirm
  placeOrder  = liftCat PlaceOrder
  cancel      = liftCat Cancel  

natSC : ShoppingCatT c => Tr x y -> c x y
natSC (SelectFirst i) = selectFirst i 
natSC (Select i)      = select i
natSC (SelectCard v)  = selectCard v
natSC Confirm         = confirm
natSC PlaceOrder      = placeOrder
natSC Cancel          = cancel  

embed : ShoppingCatT c => ShoppingCat a b -> c a b
embed = foldFunCat natSC