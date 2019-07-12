{-# LANGUAGE DeriveFunctor #-}

-- | A data type similar to 'Data.Validation' that recovers from errors.
module Data.Recover
	( Recover (..)
	, ensure
	, recover
	, failFromEither
	, recoverFromEither
	, failFromMaybe
	, recoverFromMaybe
) where

import Data.Bifunctor (Bifunctor, bimap, first, second)

-- | A @Recover e v@ contains a value @v@ or an error @e@ or both. This is
-- similar to `Data.These`, but with a different `Applicative` instance.
--
-- Like `Data.Validation`, the `Applicative` instance of `Recover` enables the
-- of validating various values while accumulating all the errors.
--
-- > Foo <$> (Success a) <*> (Success b) == Success (Foo a b)
-- > Foo <$> (Failure e) <*> (Failure ee) == Failure (e <> ee)
-- > Foo <$> (Success a) <*> (Failure ee) == Failure e
--
-- Unlike `Data.Validation`, `Recover` also has a constructor that represents
-- the situation in which there were errors but a value could be nonetheless
-- obtained.
--
-- > Foo <$> (Recover e a) <*> (Success b) = Recover e (Foo a b)
-- > Foo <$> (Recover e a) <*> (Recover ee b) = Recover (e <> ee) (Foo a b)
data Recover e v
	-- | Represents the situation in which a value @v@ was obtained without
	-- problems.
	= Success v
	-- | a value @v@ was obtained despite encountering error @e@
	| Recover e v
	-- | found error @e@ and couldn't generate a value @v@
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

-- | Conditions the success of a @(a -> Recover a b)@ function to the success of
-- a previous @Recover e a@ value.
--
-- >>> (Success True) `ensure` (const (Success ()) == Success ()
-- >>> (Recover [False] True) `ensure` (const Success ()) == Recover [False] ()
-- >>> (Recover [False] True) `ensure` (const Recover [False] ()) == Recover [False,False] ()
-- >>> (Failure [False]) `ensure` (const (Success ()) == Failure [False]
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

-- | Recover with a value @Recover e a@ in case the second argument is 'Failure' e.
recover :: Semigroup e => a -> Recover e a -> Recover e a
recover a (Failure e) = Recover e a
recover _ v = v

-- | Converts 'Either' to 'Recover'. 'Left' is 'Failure', 'Right' is 'Success'
failFromEither :: Semigroup e => Either e v -> Recover e v
failFromEither (Left e) = Failure e
failFromEither (Right v) = Success v

-- | Similar to 'failFromEither' but 'Left' e is 'Recover' e v.
recoverFromEither :: Semigroup e => v -> Either e v -> Recover e v
recoverFromEither v = recover v . failFromEither

-- | Fail with @e@ in case of 'Nothing'
failFromMaybe :: Semigroup e => e -> Maybe v -> Recover e v
failFromMaybe e = maybe (Failure e) Success

-- | Recover with @Recover e v@ in case of 'Nothing'
recoverFromMaybe :: Semigroup e => e -> v -> Maybe v -> Recover e v
recoverFromMaybe e v = recover v . failFromMaybe e
