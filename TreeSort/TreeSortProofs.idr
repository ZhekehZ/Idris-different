import TreeSort

import Utils.TotalOrder
import Utils.Sorted
import Utils.DependentPatternMatching
import Utils.SortingTree
import Utils.Tree
import Utils.Permutation
import Utils.SameElements
import Utils.NatUtils
import Utils.SortFunction

%default total


lemma1 : {A : Type} -> Ord A => (a, x, y : A) -> (t : Tree A) -> maxTDef x (insert a t) = maxTDef y (insert a t)
lemma1 a x y Leaf = Refl
lemma1 a x y (Node l u r) with (a <= u)
    lemma1 a x y (Node l u r) | True = Refl
    lemma1 a x y (Node l u r) | False = Refl


lemma2 : {A : Type} -> Ord A => IsTotal A -> {x, y : A} -> {t : Tree A} -> maxTDef y t <=| x -> maxTDef x t <=| x
lemma2 q {t=Leaf} p = totalRefl q x
lemma2 q {t=(Node l u r)} p = p

lemma3 : {A : Type} -> Ord A => {a, x : A} 
    -> (tree : Tree A) 
    -> IsTotal A 
    -> a <=| x 
    -> maxTDef x tree <=| x 
    -> maxTDef x (insert a tree) <=| x 
lemma3 Leaf tt p q = p
lemma3 {a=a} (Node l d r) tt p q with (a <= d)
    lemma3 {a=a} (Node l d r) tt p q | True = q
    lemma3 {a=a} (Node l d r) tt p q | False = rewrite lemma1 a d x r in lemma3 r tt p (lemma2 tt q)


lemma4 : {A : Type} -> Ord A => (a, x, y : A) -> (t : Tree A) -> minTDef x (insert a t) = minTDef y (insert a t)
lemma4 a x y Leaf = Refl
lemma4 a x y (Node l u r) with (a <= u)
    lemma4 a x y (Node l u r) | True = Refl
    lemma4 a x y (Node l u r) | False = Refl


lemma5 : {A : Type} -> Ord A => IsTotal A -> {x, y : A} -> {t : Tree A} -> x <=| minTDef y t -> x <=| minTDef x t
lemma5 q {t=Leaf} p = totalRefl q x
lemma5 q {t=(Node l u r)} p = p


lemma6 : {A : Type} -> Ord A => {a, x : A} 
    -> (tree : Tree A) 
    -> IsTotal A 
    -> x <=| a 
    -> x <=| minTDef x tree 
    -> x <=| minTDef x (insert a tree) 
lemma6 Leaf tt p q = p
lemma6 {a=a} (Node l d r) tt p q with (a <= d)
    lemma6 {a=a} (Node l d r) tt p q | True = rewrite lemma4 a d x l in lemma6 l tt p (lemma5 tt q)
    lemma6 {a=a} (Node l d r) tt p q | False = q


||| insert preservers sort
insertSorted : {A : Type} -> Ord A => IsTotal A -> (x : A) -> (t : Tree A) -> IsSortingTree t -> IsSortingTree (insert x t) 
insertSorted tt a Leaf p = stNode stLeaf a stLeaf (totalRefl tt a) (totalRefl tt a)
insertSorted tt a (Node l y r) p with (dpm (a <=) y)
    insertSorted tt a (Node l y r) (stNode sl _ sr p o) | (True ** yes) = rewrite yes in
            stNode (insertSorted tt a l sl) y sr (lemma3 l tt yes p) o
    insertSorted tt a (Node l y r) (stNode sl _ sr p o) | (False ** no) = rewrite no in 
        stNode sl y (insertSorted tt a r sr) p (lemma6 r tt aux o)
            where
                aux : y <= a = True
                aux with (totalTot tt a y)
                    aux | Left l = void (uninhabited (trans (sym no) l))
                    aux | Right r = r


||| listToTreeAcc converts list to sorting tree
listToTreeAccSorted : {A : Type} -> Ord A 
    => IsTotal A 
    -> (l: List A) 
    -> {acc : Tree A} 
    -> IsSortingTree acc 
    -> IsSortingTree (listToTreeAcc acc l)
listToTreeAccSorted t [] p = p
listToTreeAccSorted t (x::xs) {acc=w} p = listToTreeAccSorted t xs (insertSorted t x w p)


||| listToTree converts list to sorting tree
listToTreeSorted : {A : Type} -> Ord A => IsTotal A -> (l: List A) -> IsSortingTree (listToTree l)
listToTreeSorted t l = listToTreeAccSorted t l stLeaf 


lemma7 : {A : Type} -> Ord A 
    => (l, r : Tree A)
    -> (x, y : A)
    -> (xs : List A)
    -> minTDef x (Node l y r) = headDef x (treeToListAcc xs (Node l y r))
lemma7 Leaf r x y acc = Refl
lemma7 (Node ll ly lr) r x y acc = lemma7 ll lr x ly (y :: treeToListAcc acc r) 


||| treeToListAcc converts sorted tree to sorted list
treeToListAccSorted : {A : Type} -> Ord A 
    => IsTotal A 
    -> {t : Tree A}
    -> {acc : List A}
    -> IsSortingTree t 
    -> Sorted acc
    -> {head : A}
    -> (headDef head acc = head)
    -> (maxTDef head t <=| head)
    -> Sorted (treeToListAcc acc t)
treeToListAccSorted tt {t=Leaf} p sacc {head=h} ph mtlh = sacc
treeToListAccSorted tt {t=Node l x r} (stNode stl _ str y1 y2) sacc {head=h} ph mtlh = 
    treeToListAccSorted tt stl (sCon aux (treeToListAccSorted tt str sacc ph (lemma2 tt mtlh))) Refl y1
    where
        replace : a = b -> a -> b
        replace Refl a = a

        aux : x <= headDef x (treeToListAcc acc r) = True
        aux with (dpm' r)
            aux | (Leaf ** p) = rewrite p in case acc of
                    [] => totalRefl tt x
                    a::as => rewrite ph in replace (cong (\r => maxTDef x r <=| h) p) mtlh
            aux | (Node rl rx rr ** q) = let t = lemma7 rl rr x rx acc 
                in rewrite q in replace (cong (x <=|) t) (replace (cong (\r => x <=| minTDef x r) q) y2)


||| treeToList converts sorted tree to sorted list
treeToListSorted : {A : Type} -> Ord A 
    => IsTotal A 
    -> {t : Tree A}
    -> IsSortingTree t
    -> Sorted (treeToList t)
treeToListSorted tt {t=Leaf} _ = sNil    
treeToListSorted tt {t=Node l x r} p = treeToListAccSorted tt p sNil Refl (totalRefl tt (maxTDef x r))


||| treeSort is sort
treeSortSorted : {A : Type} -> Ord A 
    => IsTotal A 
    -> (xs : List A)
    -> Sorted (treeSort xs)
treeSortSorted tt xs = treeToListSorted tt (listToTreeSorted tt xs)



data tCount : {A : Type} -> A -> Tree A -> Nat -> Type where
    tcLeaf : tCount a Leaf 0 
    tcNode : {A : Type} -> (a : A) -> {l, r : Tree A} -> (k1, k2 : Nat) 
            -> tCount a l k1 -> tCount a r k2 -> tCount a (Node l a r) (S (k2 + k1))
    tcNode' : {A : Type} -> (a : A) -> {l, r : Tree A} -> (k1, k2 : Nat) -> {x : A}
            -> tCount a l k1 -> tCount a r k2 -> Not (x = a) -> tCount a (Node l x r) (k2 + k1) 

lemma8 :  {A : Type} -> Ord A => IsTotal A -> {t : Tree A} -> {k : Nat} -> (a : A) -> tCount a t k -> tCount a (insert a t) (S k)
lemma8 tt {t=Leaf} a p = tcNode a _ 0 p tcLeaf
lemma8 tt {t=Node l _ r} a (tcNode _ a2 a3 a4 a5) = rewrite totalRefl tt a in rewrite sSumEqSumS a3 a2 in 
        tcNode a (S a2) _ (lemma8 tt a a4) a5
lemma8 tt {t=Node l x r} a (tcNode' _ a2 a3 a4 a5 a6) with (dpm (a<=) x)
    lemma8 tt {t=Node l x r} a (tcNode' _ a2 a3 a4 a5 a6) | (True ** yes) = rewrite yes in rewrite sSumEqSumS a3 a2 in 
        tcNode' a (S a2) _ (lemma8 tt a a4) a5 a6
    lemma8 tt {t=Node l x r} a (tcNode' _ a2 a3 a4 a5 a6) | (False ** no) = rewrite no in tcNode' a _ _ a4 (lemma8 tt a a5) a6 


lemma9 :  {A : Type} -> Ord A => IsTotal A -> {t : Tree A} -> {k : Nat} 
    -> (a, x : A) -> tCount a t k -> Not (x = a) -> tCount a (insert x t) k
lemma9 tt {t=Leaf} a x p q = tcNode' a _ _ p tcLeaf q
lemma9 tt {t=Node l y r} _ x (tcNode _ k1 k2 r1 r2) q with (dpm (x <=) y)
    lemma9 tt {t=Node l y r} _ x (tcNode _ k1 k2 r1 r2) q | (True ** yes) = rewrite yes in tcNode _ _ _ (lemma9 tt y x r1 q) r2 
    lemma9 tt {t=Node l y r} _ x (tcNode _ k1 k2 r1 r2) q | (False ** no) = rewrite no in tcNode _ _ _ r1 (lemma9 tt y x r2 q) 
lemma9 tt {t=Node l y r} a x (tcNode' _ k1 k2 r1 r2 r3) q with (dpm (x <=) y)
    lemma9 tt {t=Node l y r} a x (tcNode' _ k1 k2 r1 r2 r3) q | (True ** yes) = rewrite yes in tcNode' _ _ _ (lemma9 tt a x r1 q) r2 r3
    lemma9 tt {t=Node l y r} a x (tcNode' _ k1 k2 r1 r2 r3) q | (False ** no) = rewrite no in tcNode' _ _ _ r1 (lemma9 tt _ _ r2 q) r3

lemma10 : {A : Type} -> Ord A => IsTotal A -> (xs : List A) -> {t : Tree A} -> (a : A) -> (k : Nat) 
    -> {m : Nat} -> tCount a t m -> lCount a xs k -> tCount a (listToTreeAcc t xs) (k + m)
lemma10 tt [] a k q p with (k)
    lemma10 tt [] a k q p | Z = q
lemma10 tt (x::xs) _ (S k) q (lcCons _ _ q3) = rewrite sSumEqSumS k m in lemma10 tt xs x _ (lemma8 tt x q) q3
lemma10 tt (x::xs) a k q (lcCons' _ _ q3 q4) = lemma10 tt xs a _ (lemma9 tt a x q q4) q3


listToTreeKeepsElements : {A : Type} -> Ord A 
    => IsTotal A -> (xs : List A) -> (a : A) -> (k : Nat) -> lCount a xs k -> tCount a (listToTree xs) k
listToTreeKeepsElements tt xs a k p = rewrite sym (xPlusZ k) in lemma10 tt xs a k tcLeaf p


lemma11 : {A : Type} -> Ord A => IsTotal A -> (xs : Tree A) -> {t : List A} -> (a : A) -> (k : Nat) 
    -> {m : Nat} -> lCount a t m -> tCount a xs k -> lCount a (treeToListAcc t xs) (k + m)
lemma11 tt Leaf a Z p q = p
lemma11 tt (Node l _ r) a _ p (tcNode _ a2 a3 a4 a5) = rewrite sym (aux a2 a3 m) in lemma11 tt l _ _ (lcCons a _ (lemma11 tt _ a _ p a5)) a4
    where
        aux : (a2, a3, m : Nat) -> a2 + S (a3 + m) = S ((a3 + a2) + m)
        aux Z Z m = Refl
        aux (S a2) Z m = cong S (aux a2 Z m)
        aux a2 (S a3) m = (rewrite sym (sSumEqSumS a2 (S (a3 + m))) in cong S (aux _ _ _))
lemma11 tt (Node l x r) a _ p (tcNode' _ a2 a3 a4 a5 a6) = 
    let qq = trans (plusAssociative a2 a3 m) (cong (+ m) (plusCommutative a2 a3)) in 
    rewrite sym qq in lemma11 tt l _ _ (lcCons' a _ (lemma11 tt _ a _ p a5) a6) a4


treeToListKeepsElements : {A : Type} -> Ord A => IsTotal A -> (t : Tree A) -> (a : A) -> (k : Nat) -> tCount a t k -> lCount a (treeToList t) k
treeToListKeepsElements tt t a k p = rewrite sym (xPlusZ k) in lemma11 tt t a k lcNil p


treeSortKeepsElements : {A : Type} -> Ord A => IsTotal A -> (xs : List A) -> AreSameElements xs (treeSort xs)
treeSortKeepsElements tt xs = areSameE tt xs (treeSort xs) 
    (\a => \k => \p => treeToListKeepsElements tt (listToTree xs) a k (listToTreeKeepsElements tt xs a k p))


||| TreeSort is correct sort function
treeSortIsCorrect : IsSortFunction (\x => treeSort x)
treeSortIsCorrect = isSortFunctionSameElements treeSort treeSortSorted treeSortKeepsElements
