{-# LANGUAGE DeriveFunctor #-}
module Data.Recover (
	Recover (..)
) where

import Data.Bifunctor (Bifunctor, bimap, first, second)

data Recover e v
	= Success v
	| Recover e v
	| Failure e
	deriving (Show, Functor)

instance Bifunctor Recover where
	bimap _ g (Success v) = Success (g v)
	bimap f g (Recover e v) = Recover (f e) (g v)
	bimap f _ (Failure e) = Failure (f e)

	first _ (Success v) = Success v
	first f (Recover e v) = Recover (f e) v
	first f (Failure e) = Failure (f e)

	second g (Success v) = Success (g v)
	second g (Recover e v) = Recover e (g v)
	second _ (Failure e) = Failure e

instance Semigroup e => Applicative (Recover e) where
	pure = Success
	Success f <*> Success v = Success (f v)
	Success f <*> Recover e v = Recover e (f v)
	Success _ <*> Failure e = Failure e
	Recover e f <*> Success v = Recover e (f v)
	Recover e f <*> Recover ee v = Recover (e <> ee) (f v)
	Recover e _ <*> Failure ee = Failure (e <> ee)
	Failure e <*> Success _ = Failure e
	Failure e <*> Recover ee _ = Failure (e <> ee)
	Failure e <*> Failure ee  = Failure (e <> ee)

instance (Semigroup e, Semigroup a) => Semigroup (Recover e a) where
	Success a <> Success aa = Success (a <> aa)
	Success a <> Recover ee aa = Recover ee (a <> aa)
	Success a <> Failure ee = Recover ee a
	Recover e a <> Success aa = Recover e (a <> aa)
	Recover e a <> Recover ee aa = Recover (e <> ee) (a <> aa)
	Recover e a <> Failure  ee = Recover (e <> ee) a
	Failure e <> Success aa = Recover e aa
	Failure e <> Recover ee aa = Recover (e <> ee) aa
	Failure e <> Failure ee = Failure (e <> ee)

ensure :: Semigroup e => Recover e a -> (a -> Recover e b) -> Recover e b
ensure (Success a) f = case f a of
	Failure e -> Failure e
	Recover e b -> Recover e b
	Success b -> Success b
ensure (Recover e a) f = case f a of
	Failure ee -> Failure (e <> ee)
	Recover ee b -> Recover (e <> ee) b
	Success b -> Recover e b
ensure (Failure e) _ = Failure e

-- | Recover from failure
recover :: Semigroup e => a -> Recover e a -> Recover e a
recover a (Failure e) = Recover e a
recover _ v = v

failFromEither :: Semigroup e => Either e v -> Recover e v
failFromEither (Left e) = Failure e
failFromEither (Right v) = Success v

-- | Recover from single mode failure
recoverFromEither :: Semigroup e => v -> Either e v -> Recover e v
recoverFromEither v = recover v . failFromEither

-- | Fail from single mode failure
failFromMaybe :: Semigroup e => e -> Maybe v -> Recover e v
failFromMaybe e Nothing = Failure e
failFromMaybe _ (Just v) = Success v

-- | Recover from single mode failure
recoverFromMaybe :: Semigroup e => e -> v -> Maybe v -> Recover e v
recoverFromMaybe e v = recover v . failFromMaybe e
