{-# LANGUAGE TypeOperators, TypeFamilies, DataKinds, GADTs, FlexibleContexts, TypeApplications,
MultiParamTypeClasses, RankNTypes, ConstraintKinds, StandaloneDeriving, ScopedTypeVariables,FlexibleInstances,

UndecidableInstances #-}

import Prelude hiding ((.), id, take, drop, head, (++))
import qualified Prelude                    as P
-- import Data.Vector.Sized ((++))
import qualified Data.Vector as V
import Data.Vector.Sized
import GHC.TypeLits
import Data.Singletons hiding ((~~>))
import Data.Word
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Proxy
import Control.Lens
import Data.Monoid
import Numeric (showIntAtBase)
import CCC (CCC(..)
  , test1
  , test2
  , test3
  , test4
  , test5
  , test6
  , test7
  , test8
  , test9
  , test10
  )
import Data.Coerce
import Control.Category
{- import Data.Sized -}


-- import           Data.Type.Natural          (Nat (..), One, SNat, Sing (..), Two)
-- import           Data.Type.Natural          (plusComm, plusSuccR, plusZR)
-- import           Data.Type.Natural          (sNatToInt, (%:*))

-- Goal: provide a ZKP of "(The byte sequence S applied to T yields R) and hashing s yields H" (S being the hidden quantity)

type Vec (n :: Nat) a = Vector n a

-- | A function, represented as a boolean matrix.
data (~~>) :: * -> * -> *
--newtype (~~>) a b = F { runF :: (Vec (Card a * Size b) BoolExp) }

instance (HasBoolRep a, HasBoolRep b
  , KnownNat (Card a * Size b)
  , KnownNat (Card b ^ Card a)
  ) => HasBoolRep (a ~~> b) where
  type Size (a ~~> b) = Card a * Size b
  type Card (a ~~> b) = Card b ^ Card a
  {- rep = iso coerce coerce -}

data E :: * -> * -> * where
  Id    :: E a a
  Comp  :: (HasBoolRep a, HasBoolRep b, HasBoolRep c)
    => E b c -> E a b -> E a c
  Eval  :: (HasBoolRep a, HasBoolRep b, HasBoolRep (a ~~> b))
    => E (a ~~> b, a) b
    -- R ^esult waits for a and a table, then treats as a number in table lookup
  Curry :: (HasBoolRep a, HasBoolRep b, HasBoolRep c, HasBoolRep (a, b))
    => E (a, b) c -> E a (b ~~> c)
    -- result waits for a, then makes a table with all poss b, using an evaluated form of the given expr
    -- which is (Vec (Size a + Size b) BoolExp -> Vec Size c BoolExp)
  Uncurry :: (HasBoolRep a, HasBoolRep b, HasBoolRep c, HasBoolRep (b ~~> c))
    => E a (b ~~> c) -> E (a, b) c
    -- Given a and b, runs the given for a and looks up b in table (specialized version of Eval?)
  Fst   :: (HasBoolRep a, HasBoolRep b)
    => E (a, b) a
  Snd   :: (HasBoolRep a, HasBoolRep b)
    => E (a, b) b
  Pair  :: (HasBoolRep a, HasBoolRep b, HasBoolRep c)
    => E a b -> E a c -> E a (b,c)
  Unit  :: HasBoolRep a
    => E a ()

  -- E/CCC encoding
  -- 4 bits for the constructor, then 6 bits for length (for bracketting)

{- instance Category E where -}

instance CCC E (~~>) (,) () where
  type Ct E = HasBoolRep2
  id  = Id
  (.) = Comp
  eval = Eval
  curry = Curry
  uncurry = Uncurry
  fork = Pair
  exl = Fst
  exr = Snd
  unit = Unit

-- | A workarond for the 'Coercible as identity' hack in the CCC class.
class (HasBoolRep a, HasBoolRep b) => HasBoolRep2 a b
instance (HasBoolRep a, a ~ b) => HasBoolRep2 a b


class (KnownNat (Size a), KnownNat (Card a)) => HasBoolRep a where
  type Size a :: Nat -- how many bits need to rep it
  type Card a :: Nat --how many elements in the set
  {- size :: Sing (Size a) -}
  -- card :: p a -> Sing (Card a)
instance HasBoolRep () where
  type Size () = 1
  type Card () = 1
instance HasBoolRep Bool where
  type Size Bool = 1
  type Card Bool = 2^1


newtype Word2 = Word2 (Bool,Bool)
newtype Word4 = Word4 (Word2,Word2)

instance HasBoolRep Word2 where
  type Size Word2 = 2
  type Card Word2 = 2^2
instance HasBoolRep Word4 where
  type Size Word4 = 4
  type Card Word4 = 2^4
instance HasBoolRep Word8 where
  type Size Word8 = 8
  type Card Word8 = 2^8

instance (HasBoolRep a, HasBoolRep b, KnownNat (Size a + Size b), KnownNat (Card a * Card b)) => HasBoolRep (a, b) where
  type Size (a, b) = Size a + Size b
  type Card (a, b) = Card a * Card b

-- type instance Size Void = 0
-- type instance Size (a -> b) = Size b * Elem a -- effectively, a table
--
type Name = String
data BoolExp = Var Name | And BoolExp BoolExp | Or BoolExp BoolExp | Not BoolExp | Bool Bool
  {- deriving (Show) -}

instance Show BoolExp where
  showsPrec _ (Var n) = showParen False $ showString n
  showsPrec _ (Bool n) = showParen False $ showString (if n then "1" else "0")
  showsPrec d (And a b) = showParen True $ showsPrec d a P.. showString "" P.. showsPrec d b
  showsPrec d (Or a b) = showParen True $ showsPrec d a P.. showString "+" P.. showsPrec d b
  showsPrec d (Not b) = showParen True $ showString "~" P.. showsPrec d b

type TotalMap k a = (a, Map k a)

totalMapLookup :: Ord k => TotalMap k v -> k -> v
totalMapLookup (z, m) k = maybe z P.id $ Map.lookup k m

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
compile Id = P.id
compile (Comp f g) = compile f P.. compile g
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
  :: forall p a b. (HasBoolRep a, HasBoolRep b, HasBoolRep (a ~~> b))
  => p (a ~~> b, a) b
  -> V (Size (a ~~> b) + Size a)
  -> V (Size b)
ev wh funcArg = (error "undefined ev") func arg
  where
    func = tak wh funcArg :: V (Size (a ~~> b))
    arg  = drp wh funcArg :: V (Size a)
    fL = natVal (Proxy @(Size (a ~~> b)))
    aL = natVal (Proxy @(Size a))

cur :: forall p a b c. (HasBoolRep a, HasBoolRep b, HasBoolRep c, HasBoolRep (b ~~> c)) => p a (b ~~> c)
  -> (V (Size a + Size b) -> V (Size c))
  -> V (Size a)
  -> V (Size (b ~~> c))
cur wh uncurried arg = flatten entries
  where
    -- TODO for [1..Card b], generate function
    bL = natVal (Proxy @(Card b))
    -- TODO either use (concat) or (concat . transpose) for entries
    entries :: Vec (Card b) (V (Size c))
    entries = fmap mkEntry (enumFromN 0)
    -- each entry is constructed by applying our uncurried function to the given arg and the particular instance
    -- of the b
    mkEntry :: Integer -> V (Size c)
    mkEntry b = res
      where
        bStr = makeEntryOutOf b bL
        res = uncurried (arg ++ maybe (error "cur: wrong size") P.id (fromList $ fmap Bool bStr))



-- Create a bit string for a given element and cardinality
-- >>> makeEntryOutOf 1 8 == "001"
makeEntryOutOf :: Integer -> Integer -> [Bool]
makeEntryOutOf b bL = fmap charToBool $ padded
  where
    charToBool '1' = True
    charToBool _   = False
    bitString = (showIntAtBase 2 (toEnum P.. (+ 48)) b) ""
    req = (\x -> ceiling (logBase 2 (realToFrac x)) `max` 1) bL
    padded = padBeforeToLength req '0' bitString
    padBeforeToLength n c xs = P.replicate (n - P.length xs) c <> xs


uncur :: (HasBoolRep a, HasBoolRep b, HasBoolRep c) => p (a, b) c
  -> (V (Size a) -> V (Size (b ~~> c)))
  -> V (Size a + Size b)
  -> V (Size c)
uncur = undefined

tak :: forall p a b c x. (HasBoolRep a, HasBoolRep b) => p (a,b) c -> Vec (Size a + Size b) x -> Vec (Size a) x
tak wh = take

drp :: forall p a b c x. (HasBoolRep a, HasBoolRep b) => p (a,b) c -> Vec (Size a + Size b) x -> Vec (Size b) x
drp wh = drop

flatten :: (KnownNat (m * n)) => Vec m (Vec n a) -> Vec (m * n) a
flatten = maybe (error "impossible") P.id P.. fromList P.. concat P.. toList P.. fmap toList


compile' :: HasBoolRep a => E () a -> V (Size a)
compile' x = compile x (pure (Bool True))


main = error "TODO"


-- id
tb1  = compile' (test1 :: E () (Word2 ~~> Word2))
tb1a = compile' (test1 :: E () (Word8 ~~> Word8))

-- fst
tb2 = compile' (test2 :: E () ((Word2, Word8) ~~> Word2))






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
