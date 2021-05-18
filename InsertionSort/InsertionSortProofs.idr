import InsertionSort

import Prelude.Uninhabited

import Utils.TotalOrder
import Utils.DependentPatternMatching
import Utils.Sorted

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



{- Proofs for concrete types -}

insertionSortSortedNat : (xs : List Nat) -> Sorted (insertionSort xs)
insertionSortSortedNat xs = insertionSortSorted (totalProofs refl tran tot) xs
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
