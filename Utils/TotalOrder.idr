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



{- For concrete types -}

public export
natIsTotal : IsTotal Nat
natIsTotal = totalProofs refl tran tot
    where
        refl : (x : Nat) -> x <= x = True
        refl Z = Refl
        refl (S n) = refl n

        tran : (x, y, z : Nat) -> x <=| y -> y <=| z -> x <=| z
        tran  Z     Z     z    a b = b
        tran (S n)  Z     z    a b = void (uninhabited a)
        tran  Z    (S n)  Z    a b = Refl
        tran  Z    (S n) (S z) a b = Refl
        tran (S x) (S y)  Z    a b = b
        tran (S x) (S y) (S z) a b = tran x y z a b

        tot : (x, y : Nat) -> Either (x <=| y) (y <=| x)
        tot Z Z = Left Refl
        tot Z (S y) = Left Refl
        tot (S x) Z = Right Refl
        tot (S x) (S y) = tot x y

