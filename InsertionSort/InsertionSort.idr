module InsertionSort

%default total

public export
insert : {A : Type} -> Ord A => A -> List A -> List A
insert x [] = [x]
insert x (y::ys) = if x <= y then x::y::ys else y::insert x ys

public export
insertionSortAcc : {A : Type} -> Ord A => List A -> List A -> List A
insertionSortAcc acc [] = acc
insertionSortAcc acc (x::xs) = insertionSortAcc (insert x acc) xs

public export
insertionSort : {A : Type} -> Ord A => List A -> List A
insertionSort = insertionSortAcc []



{- Examples -}

private
example1 : insertionSort [5, 2, 1, 4, 3] = [1, 2, 3, 4, 5]
example1 = Refl

private
example2 : insertionSort ["aba", "bab", "aaa", "ab"] = ["aaa", "ab", "aba", "bab"]
example2 = Refl