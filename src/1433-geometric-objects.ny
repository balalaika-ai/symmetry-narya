export "1432-euclidean-group"
export "502-subgroups"

{` Chapter 14, section "Geometric objects" (geometry.tex 193-245): for a set
   M of materials, a geometric object is (E, g) : EucObj_M ≔ Σ_{E : ES}
   (Points E → M). EucObj_M is a groupoid (the first exercise), so a
   geometric object o has a symmetry group Aut(o) (automorphism group in
   EucObj_M, module 400). Second exercise: for an object o = (𝔼ⁿ, g) the
   symmetry group is a subgroup of E(n) (chapter 5, def:set-of-subgroups):
   the E(n)-set X(E) = Σ_{g'} ‖o = (E, g')‖ is transitive and its total space
   is equivalent, as a pointed type, to the component of o, so the
   underlying group of the subgroup is identified with Aut(o). `}

def EuclideanObject (K : EuclideanField) (M : SetTypes) : Type
  ≔ Σ (EuclideanSpace K) (E ↦ euclidean_points K E → M .fst)

{` Exercise (geometry.tex 241): EucObj_M is a groupoid. `}
def euclidean_object_groupoid (K : EuclideanField) (M : SetTypes) : isGroupoid (EuclideanObject K M)
  ≔ hlevel_to_groupoid (EuclideanObject K M)
      (hlevel_sigma (suc. (suc. (suc. zero.))) (EuclideanSpace K) (E ↦ euclidean_points K E → M .fst)
        (groupoid_to_hlevel (EuclideanSpace K) (euclidean_space_groupoid K))
        (E ↦ set_hlevel_above_two (suc. zero.) (euclidean_points K E → M .fst)
          (pi_set (euclidean_points K E) (_ ↦ M .fst) (_ ↦ M .snd))))

{` The symmetry group of a geometric object. `}
def geometric_object_symmetry_group (K : EuclideanField) (M : SetTypes) (o : EuclideanObject K M) : Group
  ≔ automorphism_group (EuclideanObject K M) (euclidean_object_groupoid K M) o

{` A geometric object in 𝔼ⁿ. `}
def standard_object (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  : EuclideanObject K M
  ≔ (euclidean_space_dim_forget K n (euclidean_standard K n), g)

{` The E(n)-set of objects in the component of o. `}
def object_component_gset (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  : GSet (euclidean_group K n)
  ≔ E ↦
    let Obj ≔ EuclideanObject K M in let o ≔ standard_object K M n g in
    let E' ≔ euclidean_space_dim_forget K n E in
    (Σ (euclidean_points K E' → M .fst) (h ↦ Mere (Id Obj o (E', h))),
     sigma_set (euclidean_points K E' → M .fst) (h ↦ Mere (Id Obj o (E', h)))
       (pi_set (euclidean_points K E') (_ ↦ M .fst) (_ ↦ M .snd))
       (h ↦ prop_is_set (Mere (Id Obj o (E', h))) (mere_isprop (Id Obj o (E', h)))))

{` An object merely equal to o lives in a space of dimension n. `}
def object_component_dimension (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  (c : NativeComponent (EuclideanObject K M) (standard_object K M n g))
  : HasDimension (K .field) n (c .fst .fst .fst .space)
  ≔ let Obj ≔ EuclideanObject K M in let o ≔ standard_object K M n g in
    let hd ≔ (x : Obj) ↦ HasDimension (K .field) n (x .fst .fst .space) in
    mere_rec (Id Obj o (c .fst)) (hd (c .fst))
      (mere_isprop (Σ (Fin n → c .fst .fst .fst .space .carrier)
        (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (c .fst .fst .fst .space) i)))
      (p ↦ transport Obj hd o (c .fst) p (standard_has_dimension K n))
      (c .snd)

def object_action_type_to_component (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  (u : ActionType (euclidean_group K n) (object_component_gset K M n g))
  : NativeComponent (EuclideanObject K M) (standard_object K M n g)
  ≔ ((euclidean_space_dim_forget K n (u .fst), u .snd .fst), u .snd .snd)

def object_component_to_action_type (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  (c : NativeComponent (EuclideanObject K M) (standard_object K M n g))
  : ActionType (euclidean_group K n) (object_component_gset K M n g)
  ≔ (((c .fst .fst .fst, object_component_dimension K M n g c), c .fst .fst .snd), (c .fst .snd, c .snd))

def object_action_type_component_equiv (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  : Equiv (ActionType (euclidean_group K n) (object_component_gset K M n g))
      (NativeComponent (EuclideanObject K M) (standard_object K M n g))
  ≔ let AT ≔ ActionType (euclidean_group K n) (object_component_gset K M n g) in
    let C ≔ NativeComponent (EuclideanObject K M) (standard_object K M n g) in
    quasi_inverse_equiv AT C (object_action_type_to_component K M n g) (object_component_to_action_type K M n g)
      (u ↦
        let V ≔ u .fst .fst .fst in
        let Hd ≔ HasDimension (K .field) n (V .space) in
        refl ((h ↦ (((V, h), u .fst .snd), u .snd)) : Hd → AT)
          (mere_isprop (Σ (Fin n → V .space .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (V .space) i))
            (object_component_dimension K M n g (object_action_type_to_component K M n g u)) (u .fst .fst .snd)))
      (c ↦ refl c)

def object_component_gset_transitive (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  : IsTransitive (euclidean_group K n) (object_component_gset K M n g)
  ≔ let AT ≔ ActionType (euclidean_group K n) (object_component_gset K M n g) in
    let Obj ≔ EuclideanObject K M in let o ≔ standard_object K M n g in
    let C ≔ NativeComponent Obj o in
    connected_action_type_transitive (euclidean_group K n) (object_component_gset K M n g)
      (connected_equiv C AT (canonical_inverse_equiv AT C (object_action_type_component_equiv K M n g)) .map
        (native_component_connected Obj o))

{` Exercise (geometry.tex 247): the symmetry group of a geometric object in
   𝔼ⁿ is a subgroup of E(n). `}
def geometric_object_subgroup (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  : Subgroups (euclidean_group K n)
  ≔ (object_component_gset K M n g,
     (g, mere (Id (EuclideanObject K M) (standard_object K M n g) (standard_object K M n g)) (refl (standard_object K M n g))),
     object_component_gset_transitive K M n g)

def geometric_object_subgroup_iso (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  : GroupIso (subgroup_group (euclidean_group K n) (geometric_object_subgroup K M n g))
      (geometric_object_symmetry_group K M (standard_object K M n g))
  ≔ let S ≔ subgroup_group (euclidean_group K n) (geometric_object_subgroup K M n g) in
    let Sym ≔ geometric_object_symmetry_group K M (standard_object K M n g) in
    let e ≔ object_action_type_component_equiv K M n g in
    (mkhom S Sym (object_action_type_to_component K M n g, refl (shape Sym)),
     book_equivalence (BG S .carrier) (BG Sym .carrier) e .equiv)

def geometric_object_subgroup_path (K : EuclideanField) (M : SetTypes) (n : Nat) (g : (Fin n → ef_carrier K) → M .fst)
  : Id Group (subgroup_group (euclidean_group K n) (geometric_object_subgroup K M n g))
      (geometric_object_symmetry_group K M (standard_object K M n g))
  ≔ group_path_from_iso (subgroup_group (euclidean_group K n) (geometric_object_subgroup K M n g))
      (geometric_object_symmetry_group K M (standard_object K M n g)) (geometric_object_subgroup_iso K M n g)
