module InsertionSort

%default total

public export
insert : Ord a => a -> List a -> List a
insert x [] = [x]
insert x (y::ys) = if x <= y then x::y::ys else y::insert x ys

public export
insertionSortAcc : Ord a => List a -> List a -> List a
insertionSortAcc acc [] = acc
insertionSortAcc acc (x::xs) = insertionSortAcc (insert x acc) xs

public export
insertionSort : Ord a => List a -> List a
insertionSort = insertionSortAcc []



{- Examples -}

private
example1 : insertionSort [5, 2, 1, 4, 3] = [1, 2, 3, 4, 5]
example1 = Refl

private
example2 : insertionSort ["aba", "bab", "aaa", "ab"] = ["aaa", "ab", "aba", "bab"]
example2 = Refl