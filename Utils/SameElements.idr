module Utils.SameElements

import Utils.TotalOrder

%default total


public export
data lCount : {A : Type} -> A -> List A -> Nat -> Type where
    lcNil : lCount a [] 0
    lcCons : {A : Type} -> (a : A) -> {xs : List A} -> (k : Nat) 
            -> lCount a xs k -> lCount a (a::xs) (S k)
    lcCons' : {A : Type} -> (a : A) -> {xs : List A} -> (k : Nat) -> {x : A} 
            -> lCount a xs k -> Not (x = a) -> lCount a (x::xs) k


public export
data AreSameElements : {A : Type} -> List A -> List A -> Type where
    areSameE : {A : Type} -> Ord A 
        => IsTotal A 
        -> (xs, ys : List A) 
        -> ((x : A) -> (k : Nat) -> lCount x xs k -> lCount x ys k) 
        -> AreSameElements xs ys
