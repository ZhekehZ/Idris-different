module TreeSort 

import Utils.Tree

%default total

public export
insert : {A : Type} -> Ord A => A -> Tree A -> Tree A 
insert a Leaf = Node Leaf a Leaf
insert a (Node l x r) = if a <= x then Node (insert a l) x r else Node l x (insert a r)

public export
listToTreeAcc : {A : Type} -> Ord A => Tree A -> List A -> Tree A
listToTreeAcc acc [] = acc
listToTreeAcc acc (x::xs) = listToTreeAcc (insert x acc) xs

public export
listToTree : {A : Type} -> Ord A => List A -> Tree A
listToTree = listToTreeAcc Leaf

public export
treeToListAcc : {A : Type} -> Ord A => List A -> Tree A -> List A
treeToListAcc acc Leaf = acc
treeToListAcc acc (Node l x r) = treeToListAcc (x :: treeToListAcc acc r) l

public export
treeToList : {A : Type} -> Ord A => Tree A -> List A 
treeToList = treeToListAcc []

public export
treeSort : {A : Type} -> Ord A => List A -> List A
treeSort = treeToList . listToTree



{- Examples -}

private
example1 : treeSort [5, 2, 1, 4, 3] = [1, 2, 3, 4, 5]
example1 = Refl

private
example2 : treeSort ["aba", "bab", "aaa", "ab"] = ["aaa", "ab", "aba", "bab"]
example2 = Refl

