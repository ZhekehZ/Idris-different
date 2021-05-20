module Utils.Permutation

%default total

public export
data IsPerm : List a -> List a -> Type where
    pNil : IsPerm [] []    
    pCons : {A : Type} -> {x, y : A} -> {xs, ys : List A} 
            -> x = y 
            -> IsPerm xs ys 
            -> IsPerm (x::xs) (y::ys) 
    pFlip : {A : Type}  -> {xs, ys : List A} -> {x, x', y, y' : A} 
            -> x = y 
            -> x' = y' 
            -> IsPerm xs ys 
            -> IsPerm (x'::x::xs) (y::y'::ys)
    pTrans : {A : Type} -> {xs, ys, zs : List A} 
            -> IsPerm xs ys 
            -> IsPerm ys zs 
            -> IsPerm xs zs



public export
idPerm : {A : Type} -> {x : List A} -> IsPerm x x 
idPerm {x=[]} = pNil
idPerm {x=x::xs} = pCons Refl idPerm