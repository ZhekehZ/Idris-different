module Utils.NatUtils

%default total

public export
xPlusZ : (x : Nat) -> x + 0 = x
xPlusZ Z     = Refl
xPlusZ (S n) = cong S (xPlusZ n)

public export
sSumEqSumS : (x, y : Nat) -> S (x + y) = x + (S y)
sSumEqSumS Z _ = Refl
sSumEqSumS (S x) y = cong S (sSumEqSumS x y)

public export
plusCommutative : (x, y : Nat) -> x + y = y + x
plusCommutative Z y = sym (xPlusZ y)
plusCommutative (S x) y = rewrite plusCommutative x y in sSumEqSumS y x

public export
plusAssociative : (x, y, z : Nat) -> x + (y + z) = (x + y) + z
plusAssociative Z _ _ = Refl
plusAssociative (S x) y z = cong S (plusAssociative x y z)
