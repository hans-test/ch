{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, GADTs, FlexibleContexts,
MultiParamTypeClasses, RankNTypes, ConstraintKinds, StandaloneDeriving, ScopedTypeVariables,

UndecidableInstances #-}

import Prelude hiding ((.), id, take, drop, head, (++))
import qualified Prelude                    as P
-- import Data.Vector.Sized ((++))
import qualified Data.Vector as V
-- import Data.Vector.Sized
import GHC.TypeLits
import Data.Singletons hiding ((~~>))
import Data.Word
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Proxy
import Control.Lens
import CCC (CCC(..))
import Data.Coerce
import Control.Category
import Data.Sized


-- import           Data.Type.Natural          (Nat (..), One, SNat, Sing (..), Two)
-- import           Data.Type.Natural          (plusComm, plusSuccR, plusZR)
-- import           Data.Type.Natural          (sNatToInt, (%:*))

-- Goal: provide a ZKP of "(The byte sequence S applied to T yields R) and hashing s yields H" (S being the hidden quantity)

type Vec (n :: Nat) a = Sized [] n a

-- | A function, represented as a boolean matrix.
data (~~>) :: * -> * -> *
--newtype (~~>) a b = F { runF :: (Vec (Card a * Size b) BoolExp) }

instance (HasBoolRep a, HasBoolRep b) => HasBoolRep (a ~~> b) where
  type Size (a ~~> b) = Card a * Size b
  type Card (a ~~> b) = Card b ^ Card a
  {- rep = iso coerce coerce -}

data E :: * -> * -> * where
  Id    :: E a a
  Comp  :: E b c -> E a b -> E a c
  Eval  :: (HasBoolRep a, HasBoolRep b) => E (a ~~> b, a) b
    -- R ^esult waits for a and a table, then treats as a number in table lookup
  Curry :: (HasBoolRep a, HasBoolRep b, HasBoolRep c) => E (a, b) c -> E a (b ~~> c)
    -- result waits for a, then makes a table with all poss b, using an evaluated form of the given expr
    -- which is (Vec (Size a + Size b) BoolExp -> Vec Size c BoolExp)
  Uncurry :: (HasBoolRep a, HasBoolRep b, HasBoolRep c) => E a (b ~~> c) -> E (a, b) c
    -- Given a and b, runs the given for a and looks up b in table (specialized version of Eval?)
  Fst   :: (HasBoolRep a, HasBoolRep b) => E (a, b) a
  Snd   :: (HasBoolRep a, HasBoolRep b) => E (a, b) b
  Pair  :: (HasBoolRep a, HasBoolRep b, HasBoolRep c) => E a b -> E a c -> E a (b,c)
  Unit  :: HasBoolRep a => E a ()

instance Category E where
  id  = Id
  (.) = Comp

instance CCC E (~~>) (,) () where
  type Ct E = HasBoolRep2
  eval = Eval
  curry = Curry
  uncurry = Uncurry
  fork = Pair
  exl = Fst
  exr = Snd
  unit = Unit

class (HasBoolRep a, HasBoolRep b) => HasBoolRep2 a b
class () => HasBoolRep a where
  type Size a :: Nat -- how many bits need to rep it
  type Card a :: Nat --how many elements in the set
  size :: Sing (Size a)
  -- card :: p a -> Sing (Card a)
instance HasBoolRep () where
  type Size () = 1
  type Card () = 1
instance HasBoolRep Bool where
  type Size Bool = 1
  type Card Bool = 2^1
instance HasBoolRep Word8 where
  type Size Word8 = 8
  type Card Word8 = 2^8
instance (HasBoolRep a, HasBoolRep b) => HasBoolRep (a, b) where
  type Size (a, b) = Size a + Size b
  type Card (a, b) = Card a * Card b

-- type instance Size Void = 0
-- type instance Size (a -> b) = Size b * Elem a -- effectively, a table
--
type Name = String
data BoolExp = Var Name | And BoolExp BoolExp | Or BoolExp BoolExp | Not BoolExp | Bool Bool

type TotalMap k a = (a, Map k a)

totalMapLookup :: Ord k => TotalMap k v -> k -> v
totalMapLookup (z, m) k = maybe z id $ Map.lookup k m

evalBoolExp :: TotalMap Name Bool -> BoolExp -> Bool
evalBoolExp env = go
  where
    go (Bool x)  = x
    go (Var n)   = totalMapLookup env n
    go (Not a)   = not $ go a
    go (And a b) = go a && go b
    go (Or a b)  = go a || go b

--
compile ::
  (HasBoolRep a, HasBoolRep b)
  =>
  E a b -> V (Size a) -> V (Size b)
compile Id = id
{- compile (Comp f g) = compile f . compile g -}
compile e@Eval = \xs -> ev e xs
compile e@(Curry f) = \xs -> cur e (compile f) xs
compile e@(Uncurry f) = \xs -> uncur e (compile f) xs
compile e@Fst = \x -> tak e x
compile e@Snd = \x -> drp e x
compile (Pair f g) = \x -> compile f x ++ compile g x
compile Unit = const $ pure $ Bool True

type V (s :: Nat) = Vec s BoolExp
-- type VS a = Vec (Size a) BoolExp

ev
  :: p (a ~~> b, a) b
  -> V (Size (a ~~> b) + Size a)
  -> V (Size b)
ev = undefined

cur :: () => p a (b ~~> c)
  -> (V (Size a + Size b) -> V (Size c))
  -> V (Size a)
  -> V (Size (b ~~> c))
cur = undefined
uncur :: () => p (a, b) c
  -> (V (Size a) -> V (Size (b ~~> c)))
  -> V (Size a + Size b)
  -> V (Size c)
uncur = undefined

tak :: forall p a b c x. p (a,b) c -> Vec (Size a + Size b) x -> Vec (Size a) x
tak w xs = take fstParam xs
  where
    fstParam :: Sing (Size a)
    fstParam = size

drp :: (sa ~ Size a, sb ~ Size b) => p (a,b) c -> Vec (sa + sb) x -> Vec sb x
drp _ = undefined




compile' :: E () Bool -> BoolExp
compile' x = {-index 0-}undefined $ compile x undefined{-[Bool True]-}


main = error "TODO"









-- ----
-- -- type Z = 0
-- -- type S a = a + 1
-- data Vector (n :: Nat) (a :: *)   where
--   Nil  :: Vector 0 a
--   (:-) :: a -> Vector n a -> Vector (n + 1) a
--
-- -- | 'replicate' @n x@ is a vector of length @n@ with @x@ the value of every element.
-- replicate :: SNat n -> a -> Vector n a
-- replicate SZ _ = Nil
-- replicate (SS n) a = a :- replicate n a
--
-- -- | 'replicate', with the length inferred.
-- replicate' :: forall n a. SingI n => a -> Vector n a
-- replicate' = replicate (sing :: SNat n)
--
-- (++) :: Vector n a -> Vector m a -> Vector (n + m) a
-- (++) (x :- xs) ys = x :- append xs ys
-- (++) Nil       ys = ys
--
-- infixr 5 :-
-- deriving instance Show a => Show (Vector n a)
-- deriving instance P.Ord a => P.Ord (Vector n a)
-- instance (Eq a) => Eq (Vector n a) where
--   Nil == Nil = True
--   (x :- xs) == (y :- ys) = x == y && xs == ys
