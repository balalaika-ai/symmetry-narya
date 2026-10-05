export "24-connected-types"

def IsCovering (A B : Type) (f : A → B) : Type ≔ (b : B) → isSet (BookFiber A B f b)
def Coverings (B : Type) : Type ≔ Σ Type (A ↦ Σ (A → B) (IsCovering A B))
def CoveringProperty (B : Type) (t : MapsInto B) : Type ≔ IsCovering (t .fst) B (t .snd)
def BundledCovering (B : Type) : Type ≔ Σ (MapsInto B) (CoveringProperty B)

def covering_property_prop (B : Type) (t : MapsInto B) : isProp (CoveringProperty B t)
  ≔ pi_prop B (b ↦ isSet (fibers_of_map B t b)) (b ↦ isset_isprop (fibers_of_map B t b))

def covering_to_setfamily (B : Type) (c : BundledCovering B) : B → SetTypes
  ≔ b ↦ (fibers_of_map B (c .fst) b, c .snd b)

def setfamily_to_covering (B : Type) (S : B → SetTypes) : BundledCovering B
  ≔ (map_of_family B (b ↦ S b .fst), b ↦
      hlevel_two_to_set (BookFiber (Σ B (b ↦ S b .fst)) B (t ↦ t .fst) b)
        (hlevel_equiv (suc. (suc. zero.)) (S b .fst)
          (BookFiber (Σ B (b ↦ S b .fst)) B (t ↦ t .fst) b)
          (native_equivalence (S b .fst) (BookFiber (Σ B (b ↦ S b .fst)) B (t ↦ t .fst) b)
            (book_projection_inclusion_equiv B (b ↦ S b .fst) b))
          (set_to_hlevel_two (S b .fst) (S b .snd))))

def setfamilies_coverings_eta (B : Type) (c : BundledCovering B)
  : Id (BundledCovering B) (setfamily_to_covering B (covering_to_setfamily B c)) c
  ≔ let d ≔ setfamily_to_covering B (covering_to_setfamily B c) in
    let p ≔ maps_families_eta B (c .fst) in
    (p, pathover_of_eq (MapsInto B) (CoveringProperty B) (d .fst) (c .fst) p (d .snd) (c .snd)
      (covering_property_prop B (c .fst)
        (transport (MapsInto B) (CoveringProperty B) (d .fst) (c .fst) p (d .snd)) (c .snd)))

def setfamilies_coverings_beta (B : Type) (S : B → SetTypes)
  : Id (B → SetTypes) (covering_to_setfamily B (setfamily_to_covering B S)) S
  ≔ funext B (_ ↦ SetTypes) (covering_to_setfamily B (setfamily_to_covering B S)) S
      (b ↦ let R ≔ covering_to_setfamily B (setfamily_to_covering B S) b in
        let p ≔ ua (R .fst) (S b .fst)
          (native_equivalence (R .fst) (S b .fst) (book_projection_fiber_equiv B (b ↦ S b .fst) b)) in
        (p, pathover_of_eq Type isSet (R .fst) (S b .fst) p (R .snd) (S b .snd)
          (isset_isprop (S b .fst) (transport Type isSet (R .fst) (S b .fst) p (R .snd)) (S b .snd))))

def coverings_bundle_equiv (B : Type) : Equiv (Coverings B) (BundledCovering B)
  ≔ quasi_inverse_equiv (Coverings B) (BundledCovering B)
      (c ↦ ((c .fst, c .snd .fst), c .snd .snd))
      (c ↦ (c .fst .fst, (c .fst .snd, c .snd))) (c ↦ refl c) (c ↦ refl c)

{` The forward map is the actual fiber family, not an unspecified inverse
   of the previously constructed equivalence of structured families. `}
def coverings_setfamilies_equiv (B : Type) : Equiv (Coverings B) (B → SetTypes)
  ≔ compose_equiv (Coverings B) (BundledCovering B) (B → SetTypes) (coverings_bundle_equiv B)
      (quasi_inverse_equiv (BundledCovering B) (B → SetTypes)
        (covering_to_setfamily B) (setfamily_to_covering B)
        (setfamilies_coverings_eta B) (setfamilies_coverings_beta B))

def groupoid_to_hlevel (A : Type) (h : isGroupoid A) : HLevel (suc. (suc. (suc. zero.))) A
  ≔ x y ↦ set_to_hlevel_two (Id A x y) (h x y)

def hlevel_to_groupoid (A : Type) (h : HLevel (suc. (suc. (suc. zero.))) A) : isGroupoid A
  ≔ x y ↦ hlevel_two_to_set (Id A x y) (h x y)

{` lem:setbundle-is-groupoid `}
def coverings_groupoid (B : Type) : isGroupoid (Coverings B)
  ≔ hlevel_to_groupoid (Coverings B)
      (hlevel_equiv (suc. (suc. (suc. zero.))) (B → SetTypes) (Coverings B)
        (canonical_inverse_equiv (Coverings B) (B → SetTypes) (coverings_setfamilies_equiv B))
        (hlevel_function (suc. (suc. (suc. zero.))) B SetTypes (groupoid_to_hlevel SetTypes sets_groupoid)))

def Permutations : Type ≔ Σ SetTypes (S ↦ Equiv (S .fst) (S .fst))
def TypeAutomorphisms : Type ≔ Σ Type (A ↦ Equiv A A)

def set_paths_transport_equiv (A B : SetTypes)
  : Equiv (Id SetTypes A B) (Equiv (A .fst) (B .fst))
  ≔ compose_equiv (Id SetTypes A B) (Id Type (A .fst) (B .fst)) (Equiv (A .fst) (B .fst))
      (subtype_path_equiv Type isSet isset_isprop A B) (transport_univalence_equiv (A .fst) (B .fst))

def circle_families_automorphisms (C : CircleSignature)
  : Equiv (C .carrier → Type) TypeAutomorphisms
  ≔ compose_equiv (C .carrier → Type) (FreeLoop Type) TypeAutomorphisms
      (circle_universal_property C Type)
      (family_equiv Type (A ↦ Id Type A A) (A ↦ Equiv A A) (A ↦ transport_univalence_equiv A A))

def circle_setfamilies_permutations (C : CircleSignature)
  : Equiv (C .carrier → SetTypes) Permutations
  ≔ compose_equiv (C .carrier → SetTypes) (FreeLoop SetTypes) Permutations
      (circle_universal_property C SetTypes)
      (family_equiv SetTypes (S ↦ Id SetTypes S S) (S ↦ Equiv (S .fst) (S .fst))
        (S ↦ set_paths_transport_equiv S S))

{` thm:coveringsofS1perms, for every CircleSignature (instantiated at constructed_circle in module 250).
   The classification uses the fiber over the base and transport along
   the generating loop, as the source theorem specifies. `}
def circle_coverings_permutations (C : CircleSignature) : Equiv (Coverings (C .carrier)) Permutations
  ≔ compose_equiv (Coverings (C .carrier)) (C .carrier → SetTypes) Permutations
      (coverings_setfamilies_equiv (C .carrier)) (circle_setfamilies_permutations C)

def forget_covering (B : Type) (c : Coverings B) : MapsInto B ≔ (c .fst, c .snd .fst)
def forget_setfamily (B : Type) (S : B → SetTypes) : B → Type ≔ b ↦ S b .fst
def forget_permutation (p : Permutations) : TypeAutomorphisms ≔ (p .fst .fst, p .snd)

def coverings_diagram_left (B : Type) (c : Coverings B)
  : Id (B → Type) (forget_setfamily B (coverings_setfamilies_equiv B .map c))
      (fibers_of_map B (forget_covering B c))
  ≔ refl (fibers_of_map B (forget_covering B c))

def coverings_diagram_right (C : CircleSignature) (S : C .carrier → SetTypes)
  : Id TypeAutomorphisms (forget_permutation (circle_setfamilies_permutations C .map S))
      (circle_families_automorphisms C .map (forget_setfamily (C .carrier) S))
  ≔ refl (circle_families_automorphisms C .map (forget_setfamily (C .carrier) S))

def circle_covering_monodromy (C : CircleSignature) (c : Coverings (C .carrier))
  (x : BookFiber (c .fst) (C .carrier) (c .snd .fst) (C .base))
  : Id (BookFiber (c .fst) (C .carrier) (c .snd .fst) (C .base))
      (circle_coverings_permutations C .map c .snd .map x)
      (refl (BookFiber (c .fst) (C .carrier) (c .snd .fst)) (C .loop) .trr x)
  ≔ refl (refl (BookFiber (c .fst) (C .carrier) (c .snd .fst)) (C .loop) .trr x)

{` def:universalcover: the path family over a groupoid is a set family,
   and its total space has the canonical contraction. `}
def path_cover_family (B : Type) (hB : isGroupoid B) (b : B) : B → SetTypes
  ≔ x ↦ (Id B b x, hB b x)

def path_cover (B : Type) (hB : isGroupoid B) (b : B) : Coverings B
  ≔ let c ≔ setfamily_to_covering B (path_cover_family B hB b) in
    (c .fst .fst, (c .fst .snd, c .snd))

def path_cover_contractible (B : Type) (hB : isGroupoid B) (b : B)
  : BookIsContr (path_cover B hB b .fst)
  ≔ book_pathspace_contractible B b

def BookPermutations : Type ≔ Σ SetTypes (S ↦ BookEquiv (S .fst) (S .fst))

def book_circle_coverings_permutations (C : CircleSignature)
  : BookEquiv (Coverings (C .carrier)) BookPermutations
  ≔ book_equivalence (Coverings (C .carrier)) BookPermutations
      (compose_equiv (Coverings (C .carrier)) Permutations BookPermutations
        (circle_coverings_permutations C)
        (family_equiv SetTypes (S ↦ Equiv (S .fst) (S .fst)) (S ↦ BookEquiv (S .fst) (S .fst))
          (S ↦ equivalence_conventions_equiv (S .fst) (S .fst))))
