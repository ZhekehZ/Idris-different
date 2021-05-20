import TreeSort

import Utils.TotalOrder
import Utils.Sorted
import Utils.DependentPatternMatching
import Utils.SortingTree
import Utils.Tree


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
