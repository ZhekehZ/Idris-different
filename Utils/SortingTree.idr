module Utils.SortingTree

import Utils.Tree


||| Rightmost element or default
public export
maxTDef : Ord a => a -> Tree a -> a 
maxTDef a Leaf = a
maxTDef a (Node l x r) = maxTDef x r


||| Leftmost element or default
public export
minTDef : a -> Tree a -> a 
minTDef a Leaf = a
minTDef a (Node l x r) = minTDef x l


||| Sorting tree relation
public export
data IsSortingTree : {A : Type} -> Ord A => Tree A -> Type where
    stLeaf : {A : Type} -> Ord A => IsSortingTree {A=A} (Leaf)
    stNode : {A : Type} -> Ord A => {l, r : Tree A} 
                -> IsSortingTree l 
                -> (x : A) 
                -> IsSortingTree r 
                -> maxTDef x l <= x = True
                -> x <= minTDef x r = True
                -> IsSortingTree (Node l x r)
