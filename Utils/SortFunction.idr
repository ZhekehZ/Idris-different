module Utils.SortFunction

import Utils.Sorted
import Utils.Permutation
import Utils.TotalOrder

%default total

public export
data IsSortFunction : ({A : Type} -> Ord A => List A -> List A) -> Type where
    isSortFunction : 
        (f : {A : Type} -> Ord A => List A -> List A) 
        -> ({A : Type} -> Ord A => IsTotal A -> (xs : List A) -> Sorted (f xs)) 
        -> ({A : Type} -> Ord A => IsTotal A -> (xs : List A) -> IsPerm (f xs) xs)
        -> IsSortFunction f