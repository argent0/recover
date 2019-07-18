A data type similar to `Data.Validation` that recovers from errors.

A `Recover e v` contains a value `v` or an error `e` or both. This is
similar to `Data.These`, but with a different `Applicative` instance.
.
Like `Data.Validation`, the `Applicative` instance of `Recover` enables the
of validating various values while accumulating all the errors.

```{haskell}
Foo <$> (Success a) <*> (Success b) == Success (Foo a b)
Foo <$> (Failure e) <*> (Failure ee) == Failure (e <> ee)
Foo <$> (Success a) <*> (Failure ee) == Failure e
```

Unlike `Data.Validation`, `Recover` also has a constructor that represents
the situation in which there were errors but a value could be nonetheless
obtained. All errors are still accumulated.

```{haskell}
Foo <$> (Recover e a) <*> (Success b) = Recover e (Foo a b)
Foo <$> (Recover e a) <*> (Recover ee b) = Recover (e <> ee) (Foo a b)
```
