module Utils.TotalOrder

infix 6 <=|  

||| Left-or-equal relation via Ord.<=
public export
(<=|) : {A : Type} -> Ord A => (x, y : A) -> Type
x <=| y = x <= y = True     


||| Total preorder 
public export
data IsTotal : (A : Type) -> Ord A => Type where
    totalProofs : {A : Type} -> Ord A 
        => ((x : A) -> x <=| x)                              -- reflexive  
        -> ((x, y, z : A) -> x <=| y -> y <=| z -> x <=| z)  -- transitive
        -> ((x, y : A) -> Either (x <=| y) (y <=| x))        -- total
        -> IsTotal A


||| Reflexivity getter
public export
totalRefl : {A : Type} -> Ord A => IsTotal A -> (x : A) -> x <=| x
totalRefl (totalProofs p _ _) = p


||| Transitivity getter
public export
totalTran : {A : Type} -> Ord A => IsTotal A -> {x, y, z : A} -> (x <=| y) -> (y <=| z) -> (x <=| z)
totalTran (totalProofs _ p _) {x=x} {y=y} {z=z} = p x y z


||| Totality getter
public export
totalTot : {A : Type} -> Ord A => IsTotal A -> (x, y : A) -> Either (x <=| y) (y <=| x)
totalTot (totalProofs _ _ p) = p


