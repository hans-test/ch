{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, GADTs, FlexibleContexts,


UndecidableInstances #-}

import Prelude hiding (take, drop, (++))
import Data.Vector.Generic.Sized
import qualified Data.Vector as V
import GHC.TypeLits
import Data.Word
import Data.Proxy
-- Goal: provide a ZKP of "(The byte sequence S applied to T yields R) and hashing s yields H" (S being the hidden quantity)

type Vec = Vector V.Vector
-- | A function, represented as a boolean matrix.
newtype (~>) a b = F { runF :: Vec (Card a) (Vec (Size b) BoolExp) }

instance (HasBoolRep a, HasBoolRep b) => HasBoolRep (a ~> b) where
  type Size (a ~> b) = Card a * Size b
  type Card (a ~> b) = Card b ^ Card a

data E :: * -> * -> * where
  Id    :: (KnownNat (Size a)) => E a a
  Comp  :: E b c -> E a b -> E a c
  Eval  :: E (a, a ~> b) b
    -- R ^esult waits for a and a table, then treats as a number in table lookup
  Curry :: E (a, b) c -> E a (b ~> c)
    -- result waits for a, then makes a table with all poss b, using an evaluated form of the given expr
    -- which is (Vec (Size a + Size b) BoolExp -> Vec Size c BoolExp)
  Uncurry :: E a (b ~> c) -> E (a, b) c
    -- Given a and b, runs the given for a and looks up b in table (specialized version of Eval?)
  Fst   :: (KnownNat (Size a), KnownNat (Size b)) => E (a, b) a
  Snd   :: (KnownNat (Size a), KnownNat (Size b)) => E (a, b) b
  Pair  :: (KnownNat (Size a), KnownNat (Size b)) => E a b -> E a c -> E a (b,c)
  Unit  :: E a ()

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
--
compile ::

  E a b -> Vec (Size a) BoolExp -> Vec (Size b) BoolExp
compile Id = id
compile (Comp f g) = compile f . compile g
-- compile e@Eval inp = _ f x -- TODO generate an list of booleans based on matrix mult
--   where
--     x = take (inSizeFst e) inp
--     f = drop (inSizeSnd e) inp
-- compile e@Fst = take' (Proxy::Size a)
compile Fst = take
compile Snd = drop
compile (Pair f g) = \x -> compile f x ++ compile g x
compile Unit = const $ pure $ Bool True


take_ :: (KnownNat m, KnownNat n) => Vec ((n :: Nat) + m) a -> Vec n a
take_ = take

argFstSize :: E (a,x) b -> Proxy (Size a)
argFstSize = const Proxy
-- argSize :: E a b -> Proxy (Size a)
-- argSize = const Proxy


compile' :: E () Bool -> BoolExp
compile' x = {-index 0-}undefined $ compile x undefined{-[Bool True]-}


main = error "TODO"
