-- good: decreasing on the argument
total
len: List a -> Nat
len [] = 0
len (x :: xs) = S (len xs)

-- bad: increasing on the argument
partial
notLen: List Nat -> Nat
notLen xs = notLen (1 :: xs)

-- also bad: not decreasing on the argument
partial
ohNo: a -> Void
ohNo x = ohNo x

-- Ackermann function: good, even though
-- different recursive calls decrease on
-- different arguments; "nested primitive
-- recursion"
total
ack: Nat -> Nat -> Nat
ack Z n = S n
ack (S m) Z = ack m 1
ack (S m) (S n) = ack m (ack (S m) n)
