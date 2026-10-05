export "96-yoneda-embedding"

def representable_component_map (X : Type) (connected : Connected X) (base : X) (x : X)
  : NativeComponent (X → Type) (Representable X base)
  ≔ (Representable X x, trunc_map native_truncation (Id X base x)
      (Id (X → Type) (Representable X base) (Representable X x))
      (map_path X (X → Type) (Representable X) base x) (connected .snd base x))

def representable_component_ap_equiv (X : Type) (connected : Connected X) (base x z : X)
  : BookEquiv (Id X x z)
      (Id (NativeComponent (X → Type) (Representable X base))
        (representable_component_map X connected base x) (representable_component_map X connected base z))
  ≔ book_equivalence (Id X x z)
      (Id (NativeComponent (X → Type) (Representable X base))
        (representable_component_map X connected base x) (representable_component_map X connected base z))
      (equivalence_from_coordinates (Id X x z)
        (Id (NativeComponent (X → Type) (Representable X base))
          (representable_component_map X connected base x) (representable_component_map X connected base z))
        (Id (X → Type) (Representable X x) (Representable X z))
        (native_equivalence (Id X x z) (Id (X → Type) (Representable X x) (Representable X z))
          (representable_ap_equiv X x z))
        (subtype_path_equiv (X → Type) (F ↦ Mere (Id (X → Type) (Representable X base) F))
          (F ↦ mere_isprop (Id (X → Type) (Representable X base) F))
          (representable_component_map X connected base x) (representable_component_map X connected base z))
        (map_path X (NativeComponent (X → Type) (Representable X base))
          (representable_component_map X connected base) x z)
        (p ↦ refl (map_path X (X → Type) (Representable X) x z p)))

{` The unnumbered Yoneda argument in the first proof of thm:S1bysymmetries
   works for any connected type, without a CircleSignature. `}
def representable_component_equiv (X : Type) (connected : Connected X) (base : X)
  : BookEquiv X (NativeComponent (X → Type) (Representable X base))
  ≔ nonempty_connected_embedding_equiv native_truncation X
      (NativeComponent (X → Type) (Representable X base)) (representable_component_map X connected base)
      (connected .fst) (native_component_connected (X → Type) (Representable X base))
      (path_equivalences_embedding X (NativeComponent (X → Type) (Representable X base))
        (representable_component_map X connected base)
        (x z ↦ representable_component_ap_equiv X connected base x z .equiv))

def circle_universal_family_component (C : CircleSignature)
  : BookEquiv (C .carrier)
      (NativeComponent (C .carrier → Type) (Representable (C .carrier) (C .base)))
  ≔ representable_component_equiv (C .carrier) (native_circle_connected C) (C .base)
