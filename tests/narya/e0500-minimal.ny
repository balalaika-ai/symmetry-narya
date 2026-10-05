{` bug[E0500] "dimension mismatch in field of struct (e ≠ 0)".
   Projecting a field out of a transport in a 3-dimensional degeneracy of a record
   type, applied to a degenerated tuple.  Narya efafad2, default (HOTT) mode.
   Run: narya -source-only -no-reformat e0500-minimal.ny `}
def R (A : Type) : Type ≔ sig ( fst : A )
axiom A : Type
axiom x : A
echo refl (Id (Id (R A) (x,) (x,)) (refl (x,)) (refl (x,))) .trr (x,)⁽ᵉᵉ⁾ .fst
