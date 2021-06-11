A data type similar to `Data.Validation` that recovers from errors.

```haskell
data Recover e v = Success v | Recover e v | Failure e
```

A `Recover e v` contains a value `v` or an error `e` or both. This is
similar to `Data.These`, but with a different `Applicative` instance.

```haskell
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
```

Like `Data.Validation`, the `Applicative` instance of `Recover` allows the
validation of various values while accumulating all the errors.

```haskell
Foo <$> (Success a) <*> (Success b) == Success (Foo a b)
Foo <$> (Failure e) <*> (Failure ee) == Failure (e <> ee)
Foo <$> (Success a) <*> (Failure ee) == Failure e
```

Unlike `Data.Validation`, `Recover` also has a constructor that represents
the situation in which there were errors but a value could, nonetheless, be
obtained. All errors are still accumulated.

```haskell
Foo <$> (Recover e a) <*> (Success b) = Recover e (Foo a b)
Foo <$> (Recover e a) <*> (Recover ee b) = Recover (e <> ee) (Foo a b)
```
