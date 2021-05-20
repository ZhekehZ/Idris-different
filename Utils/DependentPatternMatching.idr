module Utils.DependentPatternMatching

||| Dependent pattern matching 
public export
dpm : (f : a -> b) -> (x : a) -> (y : b ** f x = y)
dpm f x = (f x ** Refl)

public export
dpm' : {A : Type} -> (x : A) -> (y : A ** x = y)
dpm' x = (x ** Refl)
