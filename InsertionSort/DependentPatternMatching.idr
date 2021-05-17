module DependentPatternMatching

|||     
public export
dpm : (f : a -> b) -> (x : a) -> (y : b ** f x = y)
dpm f x = (f x ** Refl)