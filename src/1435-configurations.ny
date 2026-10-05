export "1434-point-objects"

{` Chapter 14, section "Geometric objects" continued (geometry.tex 199-290).

   Running text (205-214): in the standard plane 𝔼² the x-axis is the
   predicate (x, y) ↦ (y = 0); the translation t : (x, y) ↦ (x + 3, y) is
   compatible with the action of the vectors (it is an automorphism of the
   torsor) and sends the line to itself, so it gives an identification
   (𝔼², g) = (𝔼², g) in Σ_{E : ES} (Points E → Prop).

   Definitions (262-290): configurations of geometric objects indexed by a
   type I with material sets M_i, their constituents, arrangements of given
   objects T_i (constituents merely equal to T_i) and incidence types
   (connected components of the type of arrangements). Litmus: arrangements
   of a single object T are the elements of the component of T. `}

{` 3 = 1 + 1 + 1 in K, and the vector (3, 0). `}
def ef_three (K : EuclideanField) : ef_carrier K ≔ ring_of_nat (K .field .fst) 3

def x_shift_vector (K : EuclideanField) : Fin 2 → ef_carrier K
  ≔ [ inl. _ ↦ ef_three K | inr. _ ↦ K .field .fst .zero ]

def standard_plane (K : EuclideanField) : EuclideanSpace K
  ≔ euclidean_space_dim_forget K 2 (euclidean_standard K 2)

{` The x-axis: P ↦ (P_y = 0). `}
def x_axis (K : EuclideanField) : (Fin 2 → ef_carrier K) → PropTypes
  ≔ P ↦ (Id (ef_carrier K) (P fin_two_second) (K .field .fst .zero), ring_set (K .field .fst) (P fin_two_second) (K .field .fst .zero))

def x_axis_object (K : EuclideanField) : EuclideanObject K propositions_settype ≔ (standard_plane K, x_axis K)

{` t(P) = P + (3, 0) leaves the y-coordinate unchanged, so the x-axis is sent
   to itself. `}
def x_axis_translation_invariant (K : EuclideanField) (P : Fin 2 → ef_carrier K)
  : Id PropTypes (x_axis K (standard_vector_space (K .field) 2 .add P (x_shift_vector K))) (x_axis K P)
  ≔ let R ≔ K .field .fst in
    refl ((y ↦ (Id (R .carrier) y (R .zero), ring_set R y (R .zero))) : R .carrier → PropTypes)
      (R .add_laws .unit_right (P fin_two_second))

{` The translation as an identification 𝔼² = 𝔼² (the space component of the
   symmetry euclidean_translation, module 1432). `}
def plane_x_translation_path (K : EuclideanField) : Id (EuclideanSpace K) (standard_plane K) (standard_plane K)
  ≔ let G ≔ ip_additive_group K (standard_inner_product_space K 2) in
    let p ≔ agset_path_from_iso G (agset_principal G) (agset_principal G) (principal_torsor_translation G (x_shift_vector K)) in
    (refl (standard_inner_product_space K 2),
     (p, prop_family_pathover (AbstractGSet G) (X ↦ Mere (Id (AbstractGSet G) (agset_principal G) X))
           (X ↦ mere_isprop (Id (AbstractGSet G) (agset_principal G) X)) (agset_principal G) (agset_principal G) p
           (abstract_principal_torsor G .snd) (abstract_principal_torsor G .snd)))

def plane_x_translation_is_symmetry (K : EuclideanField)
  : Id (Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
      (refl ((E ↦ euclidean_space_dim_forget K 2 E) : EuclideanSpaceDim K 2 → EuclideanSpace K) (euclidean_translation K 2 (x_shift_vector K)))
      (plane_x_translation_path K)
  ≔ refl (plane_x_translation_path K)

{` Transport along the translation path is P ↦ P + (3, 0). `}
def plane_x_translation_transport (K : EuclideanField) (P : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K) (refl (euclidean_points K) (plane_x_translation_path K) .trr P)
      (standard_vector_space (K .field) 2 .add P (x_shift_vector K))
  ≔ let G ≔ ip_additive_group K (standard_inner_product_space K 2) in
    let f ≔ principal_torsor_translation G (x_shift_vector K) in
    refl ((φ ↦ φ .fst .map P) : AbstractGSetIso G (agset_principal G) (agset_principal G) → Fin 2 → ef_carrier K)
      (agset_path_from_iso_section G (agset_principal G) (agset_principal G) f)

{` "by univalence, the translation t gives rise to an identification of type
   (E, g) = (E, g)". `}
def x_axis_translation_symmetry (K : EuclideanField)
  : Id (EuclideanObject K propositions_settype) (x_axis_object K) (x_axis_object K)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in
    let e ≔ plane_x_translation_path K in
    let Pt ≔ refl (euclidean_points K) e in
    (e,
     x ⤇
       let q : Id F (Pt .trr x.0) x.1 ≔ type_pathover_transport F F Pt x.0 x.1 x.2 in
       let q' : Id F (standard_vector_space (K .field) 2 .add x.0 (x_shift_vector K)) x.1
         ≔ concat F (standard_vector_space (K .field) 2 .add x.0 (x_shift_vector K)) (Pt .trr x.0) x.1
             (inverse F (Pt .trr x.0) (standard_vector_space (K .field) 2 .add x.0 (x_shift_vector K))
               (plane_x_translation_transport K x.0)) q in
       concat PropTypes (x_axis K x.0) (x_axis K (standard_vector_space (K .field) 2 .add x.0 (x_shift_vector K))) (x_axis K x.1)
         (inverse PropTypes (x_axis K (standard_vector_space (K .field) 2 .add x.0 (x_shift_vector K))) (x_axis K x.0)
           (x_axis_translation_invariant K x.0))
         (refl (x_axis K) q'))

{` Configurations: a Euclidean space E with p_i : Points E → M_i. `}
def Configuration (K : EuclideanField) (I : Type) (M : I → SetTypes) : Type
  ≔ Σ (EuclideanSpace K) (E ↦ (i : I) → euclidean_points K E → M i .fst)

def configuration_constituent (K : EuclideanField) (I : Type) (M : I → SetTypes) (c : Configuration K I M) (i : I)
  : EuclideanObject K (M i)
  ≔ (c .fst, c .snd i)

{` A configuration of n objects: I = Fin n. `}
def ConfigurationOfObjects (K : EuclideanField) (n : Nat) (M : Fin n → SetTypes) : Type ≔ Configuration K (Fin n) M

{` Arrangements of objects T_i: configurations whose i-th constituent is
   merely equal to T_i. `}
def Arrangement (K : EuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → EuclideanObject K (M i)) : Type
  ≔ Σ (Configuration K I M)
      (c ↦ (i : I) → Mere (Id (EuclideanObject K (M i)) (configuration_constituent K I M c i) (T i)))

{` Incidence types: the connected component of an arrangement a. `}
def IncidenceType (K : EuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → EuclideanObject K (M i))
  (a : Arrangement K I M T) : Type
  ≔ NativeComponent (Arrangement K I M T) a

def incidence_type_connected (K : EuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → EuclideanObject K (M i))
  (a : Arrangement K I M T) : Connected (IncidenceType K I M T a)
  ≔ native_component_connected (Arrangement K I M T) a

{` Litmus: arrangements of one object T (I = Unit) are the objects merely
   equal to T. `}
def single_arrangement_equiv (K : EuclideanField) (M : SetTypes) (T : EuclideanObject K M)
  : Equiv (Arrangement K Unit (_ ↦ M) (_ ↦ T)) (Σ (EuclideanObject K M) (x ↦ Mere (Id (EuclideanObject K M) x T)))
  ≔ let Obj ≔ EuclideanObject K M in
    let A ≔ Arrangement K Unit (_ ↦ M) (_ ↦ T) in
    let B ≔ Σ Obj (x ↦ Mere (Id Obj x T)) in
    quasi_inverse_equiv A B
      (a ↦ ((a .fst .fst, a .fst .snd star.), a .snd star.))
      (b ↦ ((b .fst .fst, _ ↦ b .fst .snd), _ ↦ b .snd))
      (a ↦
        let E ≔ a .fst .fst in
        let Fn ≔ (i : Unit) → euclidean_points K E → M .fst in
        let ext : Id Fn (_ ↦ a .fst .snd star.) (a .fst .snd)
          ≔ funext Unit (_ ↦ euclidean_points K E → M .fst) (_ ↦ a .fst .snd star.) (a .fst .snd)
              (i ↦ match i [ star. ↦ refl (a .fst .snd star.) ]) in
        let C ≔ Σ Fn (p ↦ (i : Unit) → Mere (Id Obj (E, p i) T)) in
        let hC : (p : Fn) → isProp ((i : Unit) → Mere (Id Obj (E, p i) T))
          ≔ p ↦ pi_prop Unit (i ↦ Mere (Id Obj (E, p i) T)) (i ↦ mere_isprop (Id Obj (E, p i) T)) in
        refl ((u ↦ ((E, u .fst), u .snd)) : C → A)
          (subtype_equal Fn (p ↦ (i : Unit) → Mere (Id Obj (E, p i) T)) hC
            (_ ↦ a .fst .snd star., _ ↦ a .snd star.) (a .fst .snd, a .snd) ext))
      (b ↦ refl b)
