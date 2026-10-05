export "504-torsors"

{` Chapter 5, footnote to def:Gtorsor: for a group G, any G-type (type family
   over BG) in the component of the principal torsor z ↦ (sh_G = z) is
   set-valued, so ∞-torsors of a group are G-sets. `}
def torsor_type_family_sets (G : Group) (X : BG G .carrier → Type)
  (t : Mere (Id (BG G .carrier → Type) (z ↦ Id (BG G .carrier) (shape G) z) X)) (z : BG G .carrier) : isSet (X z)
  ≔ mere_rec (Id (BG G .carrier → Type) (w ↦ Id (BG G .carrier) (shape G) w) X) (isSet (X z)) (isset_isprop (X z))
      (p ↦ transport (BG G .carrier → Type) (F ↦ isSet (F z)) (w ↦ Id (BG G .carrier) (shape G) w) X p
        (bg_groupoid G (shape G) z))
      t
