import InsertionSort

import Prelude.Uninhabited

import Utils.TotalOrder
import Utils.DependentPatternMatching
import Utils.Sorted
import Utils.Permutation
import Utils.SortFunction

%default total


||| (forall x in xs : y <= x) /\ (y <= t) ==> y <= insert t xs
lemma1 : {A : Type} -> Ord A => {t, y : A} -> {xs : List A} 
    -> y <= headDef y xs = True 
    -> y <= t = True 
    -> y <= headDef y (insert t xs) = True 
lemma1 {xs=[]} _ q = q
lemma1 {xs=x'::xs} p q with (t <= x')
    lemma1 {xs=x'::xs} _ q | True = q
    lemma1 {xs=x'::xs} p _ | False = p


||| Insertion preserves sort
insertSorted : {A : Type} -> Ord A => {xs : List A} 
    -> IsTotal A
    -> (a : A) 
    -> (s : Sorted xs) 
    -> Sorted (insert a xs)
insertSorted t {xs=[]} a s = sCon (totalRefl t a) sNil
insertSorted t {xs=x::xs} a s with (dpm (a <=) x)
    insertSorted t {xs=x::xs} a s 
        | (True ** yes) = rewrite yes in sCon yes s
    insertSorted t {xs=x::xs} a (sCon r q) 
        | (False ** no) = rewrite no in sCon (lemma1 r (aux2 (totalTot t a x) (aux1 no))) (insertSorted t a q)
    where 
        aux1 : {x, y : A} -> x <= y = False -> Not (x <= y = True)
        aux1 p = rewrite p in uninhabited

        aux2 : {A, B : Type} -> Either A B -> Not A -> B
        aux2 (Right r) _ = r  
        aux2 (Left l) p = void (p l)  


||| InsertionSortAcc is sort (if initial acc is sorded) 
lemma2 : {A : Type} -> Ord A 
    => IsTotal A 
    -> (xs, ys : List A) 
    -> Sorted ys 
    -> Sorted (insertionSortAcc ys xs)
lemma2 t [] ys p = p
lemma2 t (x::xs) ys p = lemma2 t xs (insert x ys) (insertSorted t x p)


||| InsertionSort is sort
insertionSortSorted : {A : Type} -> Ord A 
    => IsTotal A 
    -> (xs : List A) 
    -> Sorted (insertionSort xs)
insertionSortSorted t [] = sNil
insertionSortSorted t (x::xs) = lemma2 t xs [x] (sCon (totalRefl t x) sNil)



lemma3 : {A : Type} -> (a, y : A) -> (as, ys : List A) -> IsPerm (y :: (a :: (as ++ ys))) (a :: (as ++ (y :: ys)))
lemma3 a y [] ys = pFlip Refl Refl idPerm
lemma3 a y (a'::as) ys = pTrans (pFlip Refl Refl idPerm) (pCons Refl (lemma3 a' y as ys))


||| InsrtionSortAcc returns permutation
insertionSortAccPerm : {A : Type} -> Ord A 
    => IsTotal A 
    -> (acc : List A) 
    -> (xs : List A) 
    -> IsPerm (insertionSortAcc acc xs) (acc ++ xs)
insertionSortAccPerm tt [] [] = pNil
insertionSortAccPerm tt [] (y::ys) = insertionSortAccPerm tt [y] ys  
insertionSortAccPerm tt (a::as) [] = pCons Refl (rewrite (sym (aux as)) in idPerm)
    where 
        aux : (x : List A) -> x = x ++ []
        aux [] = Refl
        aux (x::xs) = cong (x::) (aux xs)
insertionSortAccPerm tt (a::as) (y::ys) with (y <= a)
    insertionSortAccPerm tt (a::as) (y::ys) | True = 
        pTrans (insertionSortAccPerm tt (y :: a :: as) ys) (lemma3 a y as ys)
    insertionSortAccPerm tt (a::as) (y::ys) | False = 
        pTrans (insertionSortAccPerm tt (a :: insert y as) ys) (pCons Refl (aux y as ys))
        where
            aux : (y : A) -> (as, ys : List A) -> IsPerm (insert y as ++ ys) (as ++ (y :: ys))
            aux y [] ys = idPerm
            aux y (a::as) ys with (y <= a)
                aux y (a::as) ys | True = lemma3 a y as ys
                aux y (a::as) ys | False = pCons Refl (aux y as ys)

||| InsrtionSort returns permutation
insertionSortPerm : {A : Type} -> Ord A => IsTotal A -> (xs : List A) -> IsPerm (insertionSort xs) xs
insertionSortPerm tt [] = pNil
insertionSortPerm tt (x::xs) = insertionSortAccPerm tt [x] xs 


||| InsertionSort is correct sort function
insrtionSortIsCorrect : IsSortFunction (\x => insertionSort x)
insrtionSortIsCorrect = isSortFunction insertionSort insertionSortSorted insertionSortPerm
