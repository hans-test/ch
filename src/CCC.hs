{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LiberalTypeSynonyms      #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE InstanceSigs  #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module CCC where

import Prelude hiding ((*), (.), ($), id, fst, snd, curry, uncurry)
import qualified Prelude
import Data.Coerce
import Control.Applicative
import qualified Control.Category as C
import Data.String
import GHC.Exts(Constraint)

-- | A Cartesian-closed category is a Category k, together with...
class CCC
  k
  (exp :: * -> * -> *)
  (product :: * -> * -> *)
  (terminal :: *)
  | exp -> product
  , exp -> terminal
  , k -> exp
  where
  type Ct k :: * -> * -> Constraint
  {- data Product k :: * -> * -> * -}
  {- data Exp k :: * -> * -> * -}
  {- data Terminal k :: * -}
  id  :: () => k a a
  (.) :: (Ct k a a, Ct k b b, Ct k c c) => k b c -> k a b -> k a c

  eval :: (Ct k a a, Ct k b b, Ct' k (exp a b)) =>     k (product (exp a b) a) b
  curry :: (Ct k a a, Ct k b b, Ct k c c, Ct' k (product a b)) => k (product a b) c -> k a (exp b c)
  uncurry :: (Ct k a a, Ct k b b, Ct k c c, Ct' k (exp b c)) => k a (exp b c) -> k (product a b) c

  fork :: (Ct k a a, Ct k c c, Ct k d d) =>  k a c -> k a d -> k a (product c d)
  exl :: (Ct k a a, Ct k b b) => k (product a b) a
  exr :: (Ct k a a, Ct k b b) => k (product a b) b
  unit :: (Ct k a a, Ct k terminal terminal) => k a terminal


-- We're going to implement HOAS (higher-order abstract syntax) for any 'CCC'.
-- That is, we're going to provide a functional DSL for constructing terms in any
-- CCC, using the function type from Haskell itself to represent functions in the
-- CCC.
--
-- Our terms will be values of type 'k a b' where 'k' is a 'CCC'.
--
-- We will use the domain 'a' as a "context" to store terms brought into scope
-- by function binders. Our "function" terms will be curried morphisms of type
-- 'k a (Exp b c)'.

-- | An untyped representation of terms in a CCC formed from the above.
-- This is useful if we want to print out terms for debugging.
data UntypedAST
  = Eval
  | Curry UntypedAST
  | Uncurry UntypedAST
  | Fork UntypedAST UntypedAST
  | Exl
  | Exr
  | U
  | Id
  | Compose UntypedAST UntypedAST
  | Lit Lit
data Lit = Num Integer | Bool Bool | String String
  deriving (Show)

-- | A 'CCC' instance for our untyped terms.
newtype K a b = K UntypedAST

data (*)  :: * -> * -> *
data (~>) :: * -> * -> *
data Unit :: * where
  Unit :: Unit

-- type NoCt a = Coercible a a
-- class NoCt


{- instance Category K where -}

instance CCC K (~>) (*) Unit where
  type Ct K = Coercible
  id = K Id
  K f . K g = K (Compose f g)

  eval = K Eval
  curry (K f) = K (Curry f)
  uncurry (K f) = K (Uncurry f)
  fork (K f) (K g) = K (Fork f g)
  exl = K Exl
  exr = K Exr
  unit = K U
instance IsBool Bool where
  fromBool = Prelude.id
instance IsBool b => IsBool (K a b) where
  fromBool b = K (Lit (Bool b))
instance IsString b => IsString (K a b) where
  fromString b = K (Lit (String b))
instance Num b => Num (K a b) where
  (+) = error "TODO"
  (-) = error "TODO"
  (*) = error "TODO"
  abs = error "TODO"
  signum = error "TODO"
  fromInteger b = K (Lit (Num b))

-- | Some very basic optimizations for the generated terms.
optimize :: K a b -> K a b
optimize (K u) = K (go u) where
  go (Curry x) =
    case go x of
      Uncurry x' -> x'
      x' -> Curry x'
  go (Uncurry x) =
    case go x of
      Curry x' -> x'
      x' -> Uncurry x'
  go (Fork x y) =
    case (go x, go y) of
      (Exl, Exr) -> Id
      (x', y') -> Fork x' y'
  go (Compose x y) =
    case (go x, go y) of
      (Id, y') -> y'
      (x', Id) -> x'
      (x', y') -> Compose x' y'
  go other = other

-- | A simple 'showsPrec' style pretty printer for terms.
prettyPrint :: K a b -> String
prettyPrint (K u) = go 0 u where
  go _ Exl             = "fst"
  go _ Exr             = "snd"
  go _ Id              = "id"
  go d Eval            = "uncurry id"
  go d (Curry e)       = parensIf (d > 10) ("curry " ++ go 11 e)
  go d (Uncurry e)     = parensIf (d > 10) ("uncurry " ++ go 11 e)
  go d (Fork e1 e2)    = parensIf (d > 3)  (go 4  e1 ++ " &&& " ++ go 3 e2)
  go d (Compose e1 e2) = parensIf (d > 9)  (go 10 e1 ++ " . "   ++ go 9 e2)
  go _ U               = "(const ())"
  go _ (Lit (Bool x))  = "(const " ++ show x ++ ")"
  go _ (Lit (Num x))   = "(const " ++ show x ++ ")"
  go _ (Lit (String x))= "(const " ++ show x ++ ")"

  parensIf True s = "(" ++ s ++ ")"
  parensIf _    s = s
instance Show (K a b) where
  show = prettyPrint
instance Show UntypedAST where
  show x = show (K x :: K () ())

type Ct' k a = Ct k a a

-- | We need to be able to insert terms based on the shape of the context.
-- To make the type checker do this for us, we introduce a type class 'Cast'.
--
-- The instances strip off products from the front of the first type until the
-- two types become equal.
--
-- (Thanks to @kcsongor for showing me how to implement this without requiring
-- @IncoherentInstances@!)
class CCC k exp product terminal => Cast k (exp :: * -> * -> *) (product :: * -> * -> * ) terminal x y | k -> exp, k -> product, k -> terminal where
  cast :: k x y

instance (CCC k exp product terminal, Ct k b b, Ct k a a, Ct k i i, Ct' k (product b i), Cast k exp product terminal b a, product b i ~ t) => Cast k exp product terminal t a where
  cast = cast . exl
instance CCC k exp product terminal => Cast k exp product terminal a a where
  cast = id


-- | Lambda abstraction. The higher-rank type here allows us to avoid explicit
-- calls to 'cast', since the elaborator will insert them for us. It does mean,
-- however, that the type and implementation of 'lam' are more complicated.
--
-- The simpler version without casts looks like this:
--
-- @lam :: forall k i a b. CCC k => (k (Product k i a) a -> k (Product k i a) b) -> k i (Exp k a b)@
--
-- which looks a lot like a standard HOAS function encoding, except that we have
-- stored the value of type @a@ in the "context" inside the function body.
lam :: forall k ct e p t i a b . (CCC k e p t, Ct k (p (e a b) a) (p (e a b) a), Ct k i i, Ct k a a, Ct k b b, Ct' k (p i a)) => ((forall x. (Ct' k x, Cast k e p t x (p i a)) => k x a) -> k (p i a) b) -> k i (e a b)
lam f = curry (f (exr . (cast :: Cast k e p t x (p i a) => k x (p i a))  ))

-- | Application is simpler since we don't need to modify the context.
($) :: (CCC k e p t,  Ct' k (p (e a b) a), Ct k i i, Ct k (e a b) (e a b), Ct k a a, Ct k b b) => k i (e a b) -> k i a -> k i b
($) f x = eval <<< fork f x


(<<<) = (.)
(>>>) = flip (.)

infixr 0 $

-- | Lift a morphism to a function on our terms.
--
-- >>> liftCCC :: Hask a b -> Hask () a -> Hask () b
-- >>> liftCCC :: K a b -> Vertex a -> Vertex b
liftCCC :: (CCC k e p t, Ct' k a, Ct' k i, Ct' k b) => k a b -> k i a -> k i b
liftCCC = (.)

-- | A term for extracting the first component of a product.
fst :: (CCC k e p t, Ct k a a, Ct k b b, Ct k (p a b) (p a b), Ct k i i) => k i (p a b) -> k i a
fst = liftCCC exl

-- | A term for extracting the second component of a product.
snd :: (CCC k e p t, Ct k a a, Ct k b b, Ct k (p a b) (p a b), Ct k i i) => k i (p a b) -> k i b
snd = liftCCC exr

-- | A term for constructing a product.
(*) :: (CCC k e p t, Ct k i i, Ct k a a, Ct k b b) => k i a -> k i b -> k i (p a b)
(*) = fork


-- | 'Normal' Haskell functions.
newtype Hask a b = Hask { getHask :: a -> b }
  deriving (Functor, Applicative, Monad)

{- deriving instance C.Category Hask -}
instance CCC Hask (->) (,) () where
  type Ct Hask = Coercible

  id = Hask Prelude.id
  Hask f . Hask g = Hask (f Prelude.. g)

  eval = Hask (Prelude.uncurry (Prelude.$))
  curry (Hask f) =  Hask (Prelude.curry f)
  uncurry (Hask f) =  Hask (Prelude.uncurry f)
  fork (Hask l) (Hask r) = Hask (\a -> (l a, r a))
  exl = Hask Prelude.fst
  exr = Hask Prelude.snd
  unit = Hask (const ())

-- Note: DerivingVia would help...
instance Num a => Num (Hask x a) where
  (+) = error "TODO"
  (-) = error "TODO"
  (*) = error "TODO"
  abs = error "TODO"
  signum = error "TODO"
  fromInteger = pure Prelude.. fromInteger
-- Note: DerivingVia would help...
instance IsString a => IsString (Hask x a) where
  fromString = pure Prelude.. fromString
-- Note: DerivingVia would help...
instance IsBool a => IsBool (Hask x a) where
  fromBool = pure Prelude.. fromBool

-- Overload booleans too:
class IsBool a where
  fromBool :: Bool -> a
true = fromBool True
false = fromBool False


runHask :: Hask () b -> b
runHask (Hask f) = f ()

asK :: K () b -> K () b
asK = Prelude.id


runK :: K () b -> UntypedAST
runK (K x) = x

type Vertex = K ()
vertex :: Vertex a -> Vertex a
vertex = Prelude.id

{- debug = runHask -}
debug = runK



test1 = (lam (\x -> x))
test2 = (lam (\x -> fst x))
test3 = (lam (\x -> fst (snd x)))
test4 = (lam (\x -> lam (\y -> x $ y)))
test5 = (lam (\x -> lam (\y -> (x $ y) $ y)))
test6 = (lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z))))
test7 = (lam (\x -> lam (\_ -> x)))
test8 =
  let s = lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z)))
      k = lam (\x -> lam (\_ -> x))
  in ((s $ k) $ k)
test9 =
  let s = lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z)))
      k = lam (\x -> lam (\_ -> x))
  in (lam (\x -> (x $ s) $ k))
test10 = (lam (\x -> lam (\y -> lam (\z -> x * snd y * z))))


testHask ::           (i -> a -> b) -> (i -> a) -> i -> b
testHask = runHask (lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z))))

testVertex :: Vertex ((i ~> (a ~> b)) ~> ((i ~> a) ~> (i ~> b)))
testVertex = vertex (lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z))))

testK :: UntypedAST
testK    = runK    (lam (\x -> lam (\y -> lam (\z -> (x $ z) $ y $ z))))


t1 :: Vertex ((a * b) ~> (b * String))
t1 = lam (\ab -> snd ab * "hello")
