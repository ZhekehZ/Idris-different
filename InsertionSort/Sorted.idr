module Sorted

||| Head or default 
public export
headDef : a -> List a -> a 
headDef a [] = a
headDef a (x::_) = x


||| Sorted relation
public export
data Sorted : Ord a => List a -> Type where
    sNil : Ord a => Sorted {a=a} []                        -- empty
    sCon : {A : Type} -> Ord A => {a : A} -> {xs : List A} 
                -> a <= headDef a xs = True 
                -> Sorted xs 
                -> Sorted (a::xs)                          -- cons 