total
mrg: (Ord a) => List a -> List a -> List a
mrg [] ys = ys
mrg xs [] = xs
mrg (x :: xs) (y :: ys) =
  if x < y
    then x :: (mrg xs (y :: ys))
    else y :: (mrg (x :: xs) ys)

partial
mrgSort: (Ord a) => List a -> List a
mrgSort [] = []
mrgSort [x] = [x]
mrgSort xs =
  mrg (mrgSort firstHalf) (mrgSort secondHalf)
  where
    halfLen: Nat
    halfLen = (length xs) `div` 2
    firstHalf = take halfLen xs
    secondHalf = drop halfLen xs
