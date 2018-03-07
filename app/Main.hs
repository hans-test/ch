{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, GADTs, FlexibleContexts,
MultiParamTypeClasses, RankNTypes,


UndecidableInstances #-}

import Prelude hiding ((.), id, take, drop, head, (++))
import Data.Vector.Sized
import qualified Data.Vector as V
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
-- Goal: provide a ZKP of "(The byte sequence S applied to T yields R) and hashing s yields H" (S being the hidden quantity)

type Vec = Vector

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
  Eval  :: E (a ~~> b, a) b
    -- R ^esult waits for a and a table, then treats as a number in table lookup
  Curry :: E (a, b) c -> E a (b ~~> c)
    -- result waits for a, then makes a table with all poss b, using an evaluated form of the given expr
    -- which is (Vec (Size a + Size b) BoolExp -> Vec Size c BoolExp)
  Uncurry :: E a (b ~~> c) -> E (a, b) c
    -- Given a and b, runs the given for a and looks up b in table (specialized version of Eval?)
  Fst   :: E (a, b) a
  Snd   :: E (a, b) b
  Pair  :: E a b -> E a c -> E a (b,c)
  Unit  :: E a ()

instance Category E where
  id  = Id
  (.) = Comp

instance CCC E (~~>) (,) () where
  eval = Eval
  curry = Curry
  uncurry = Uncurry
  fork = Pair
  exl = Fst
  exr = Snd
  unit = Unit

-- inSize :: HasBoolRep a => e a b -> Int
-- inSizeFst :: HasBoolRep a => e (a, x) b -> Int
-- inSizeSnd :: HasBoolRep a => e (x, a) b -> Int
-- outize :: HasBoolRep b => e a b -> Int
--
class HasBoolRep a where
  type Size a :: Nat -- how many bits need to rep it
  type Card a :: Nat --how many elements in the set
--   type Elem a :: * -- cardinality
--
  {- rep :: Iso' a (Vec (Size a) BoolExp) -}

instance HasBoolRep () where
  type Size () = 1
  type Card () = 1
  {- rep = iso (pure True) (const ()) -}
instance HasBoolRep Bool where
  type Size Bool = 1
  type Card Bool = 2^1
  {- rep = iso pure head -}
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
  {- (HasBoolRep a, HasBoolRep b) -}
  {- => -}
  E a b -> Vec (Size a) BoolExp -> Vec (Size b) BoolExp
compile Id = id
compile (Comp f g) = compile f . compile g
-- compile e@Eval inp = _ f x -- TODO generate an list of booleans based on matrix mult
--   where
--     x = take (inSizeFst e) inp
--     f = drop (inSizeSnd e) inp
-- compile e@Fst = take' (Proxy::Size a)
compile e@Fst = \x -> tak e x
compile e@Snd = \x -> drp e x
compile (Pair f g) = \x -> compile f x ++ compile g x
compile Unit = const $ pure $ Bool True

tak :: (sa ~ Size a, sb ~ Size b) => p (a,b) c -> Vec (sa + sb) x -> Vec sa x
tak _ = undefined
drp :: (sa ~ Size a, sb ~ Size b) => p (a,b) c -> Vec (sa + sb) x -> Vec sb x
drp _ = undefined



compile' :: E () Bool -> BoolExp
compile' x = {-index 0-}undefined $ compile x undefined{-[Bool True]-}


main = error "TODO"
