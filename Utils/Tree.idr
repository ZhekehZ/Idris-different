module Utils.Tree

public export
data Tree a = Node (Tree a) a (Tree a)
            | Leaf