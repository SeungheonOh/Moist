

data Funny = forall a. Show a => Funny a

data NotFunny a = Show a => NotFunny a

data Li a = Nil | Cons a (Li a)

-XExtenstionalTypes
[Funny 10, Funny "hello"] :: [Funny]

magic :: forall a. a -> Integer

-XRankNTypes
f :: forall a. a -> (forall b. b -> a)
g :: forall a b. a -> (b -> a)

f 1 :: forall b. b -> a

rankN :: (forall n. Num n => n -> n) -> (Int, Double)
rankN f = (f 1, f 1.0)

foo :: forall b c d. (forall a. a -> b) -> (c, d) -> (b, b)
foo f (x, y) = (f x, f y)

nonrankN :: (Num n => n -> n) -> (Int, Double)
nonrankN f = (f 1, f 1.0)


-- nash

foo :: ...
foo = [UPLC|arstarst....]

{-# comp #-}
tails :: Integer -> UPLC

tails 10 := tail (tail (tail ...))