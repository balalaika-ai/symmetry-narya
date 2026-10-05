export "900-group-monos-epis"
export "934-epi-connected-fibers"
export "1122-generation-rho-embedding"
export "412-symmetric-group-two"

{` def:gens-gp (fggroups.tex:153) and lem:gens-gp-iff (fggroups.tex:162).

   GeneratesGroup S dec G ι: the induced homomorphism F_S → G is an epimorphism
   (IsGroupEpi, def:epimorphism of chapter 9), literally as in the book.
   generates_iff_surjective: this is equivalent to surjectivity on symmetries
   (line 209; lem:epi-surj, module 934).

   lem:gens-gp-iff is FALSE as printed (the "if" direction):
   - gens_gp_only_if: if S generates G then ρ_S is an embedding (proved, module 1122);
   - gens_gp_if_counterexample: S = ∅ and G = Σ_2.  ρ_∅ : BΣ_2 → Σ_X (∅ → X → X) is
     t ↦ ((t = sh), !), and t ↦ (t = sh) is an embedding (for a 2-element set A,
     A ≃ (Fin 2 = A), so the map is the inclusion of the component of 2-element sets
     into U up to a natural equivalence), but ∅ does not generate Σ_2 (the free group
     on ∅ is trivial, while Σ_2 has the non-identity swap).
   The argument works for every group of order 2; in general the converse holds iff
   every automorphism of USym G commuting with the ι(s)·_ is a right multiplication. `}

def GeneratesGroup (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G) : Type
  ≔ IsGroupEpi (constructed_free_group S dec) G (free_induced_hom S dec G iota)

def generates_iff_surjective (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G)
  : Equiv (GeneratesGroup S dec G iota) (GeneratesSurjectively S dec G iota)
  ≔ gepi_epi_usym_surjective_equiv (constructed_free_group S dec) G (free_induced_hom S dec G iota)

def gens_gp_only_if (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G)
  (h : GeneratesGroup S dec G iota) : RhoEmbedding G S iota
  ≔ rho_embedding_of_connected S dec G iota
      (gepi_epi_connected_fibers (constructed_free_group S dec) G (free_induced_hom S dec G iota) h)

{` "In this case G is the automorphism group of ρ_S(sh_G)" (line 174): an embedding
   induces equivalences on identity types, in particular USym G ≃ (ρ_S(sh) = ρ_S(sh)). `}
def gens_gp_automorphisms (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G)
  (h : GeneratesGroup S dec G iota)
  : BookEquiv (USym G) (Id (RhoTarget S) (rho_map G S iota (shape G)) (rho_map G S iota (shape G)))
  ≔ embedding_on_paths (BG G .carrier) (RhoTarget S) (rho_map G S iota) (gens_gp_only_if S dec G iota h) (shape G) (shape G)

{` ---------- The counterexample ---------- `}

def empty_decidable_equality : DecidableEquality Empty ≔ x y ↦ match x []

def sigma_two : Group ≔ symmetric_group two

def empty_iota : Empty → USym sigma_two ≔ s ↦ match s []

def empty_endos (X : Type) : Empty → X → X ≔ s ↦ match s []

def empty_structure_equiv : Equiv Type (RhoTarget Empty)
  ≔ quasi_inverse_equiv Type (RhoTarget Empty) (X ↦ (X, empty_endos X)) (u ↦ u .fst)
      (X ↦ refl X)
      (u ↦ (refl (u .fst), funext Empty (_ ↦ u .fst → u .fst) (empty_endos (u .fst)) (u .snd) (s ↦ match s [])))

def path_flip_equiv (A : Type) (x y : A) : Equiv (Id A x y) (Id A y x)
  ≔ quasi_inverse_equiv (Id A x y) (Id A y x) (inverse A x y) (inverse A y x)
      (inverse_inverse A x y) (inverse_inverse A y x)

def sigma_two_shape_paths_equiv (t : BG sigma_two .carrier)
  : Equiv (Id (BG sigma_two .carrier) t (shape sigma_two)) (t .fst .fst)
  ≔ let S0 ≔ standard_set two in
    let A ≔ t .fst .fst in
    let h : TwoElement A
      ≔ mere_rec (Id SetTypes S0 (t .fst)) (TwoElement A) (two_element_prop A)
          (p ↦ mere (Id Type (Fin two) A) (refl ((u : SetTypes) ↦ u .fst) p)) (t .snd) in
    compose_equiv (Id (BG sigma_two .carrier) t (shape sigma_two)) (Id SetTypes (t .fst) S0) A
      (component_path_equiv SetTypes S0 t (shape sigma_two))
      (compose_equiv (Id SetTypes (t .fst) S0) (Id Type A (Fin two)) A
        (subtype_path_equiv Type isSet isset_isprop (t .fst) S0)
        (compose_equiv (Id Type A (Fin two)) (Id Type (Fin two) A) A
          (path_flip_equiv Type A (Fin two))
          (canonical_inverse_equiv A (Id Type (Fin two) A) (two_points_paths_equiv A h))))

def sigma_two_carrier_embedding : IsEmbedding (BG sigma_two .carrier) Type (t ↦ t .fst .fst)
  ≔ embedding_compose (BG sigma_two .carrier) SetTypes Type (t ↦ t .fst) (u ↦ u .fst)
      (subtype_projection_embedding SetTypes (x ↦ Mere (Id SetTypes (standard_set two) x))
        (x ↦ mere_isprop (Id SetTypes (standard_set two) x)))
      (subtype_projection_embedding Type isSet isset_isprop)

def sigma_two_shape_paths_embedding
  : IsEmbedding (BG sigma_two .carrier) Type (t ↦ Id (BG sigma_two .carrier) t (shape sigma_two))
  ≔ embedding_homotopic (BG sigma_two .carrier) Type (t ↦ t .fst .fst) (t ↦ Id (BG sigma_two .carrier) t (shape sigma_two))
      (t ↦ inverse Type (Id (BG sigma_two .carrier) t (shape sigma_two)) (t .fst .fst)
        (ua (Id (BG sigma_two .carrier) t (shape sigma_two)) (t .fst .fst) (sigma_two_shape_paths_equiv t)))
      sigma_two_carrier_embedding

def empty_rho_embedding : RhoEmbedding sigma_two Empty empty_iota
  ≔ embedding_homotopic (BG sigma_two .carrier) (RhoTarget Empty)
      (t ↦ (Id (BG sigma_two .carrier) t (shape sigma_two), empty_endos (Id (BG sigma_two .carrier) t (shape sigma_two))))
      (rho_map sigma_two Empty empty_iota)
      (t ↦ (refl (Id (BG sigma_two .carrier) t (shape sigma_two)),
        funext Empty (_ ↦ Id (BG sigma_two .carrier) t (shape sigma_two) → Id (BG sigma_two .carrier) t (shape sigma_two))
          (empty_endos (Id (BG sigma_two .carrier) t (shape sigma_two))) (rho_map sigma_two Empty empty_iota t .snd)
          (s ↦ match s [])))
      (embedding_compose (BG sigma_two .carrier) Type (RhoTarget Empty)
        (t ↦ Id (BG sigma_two .carrier) t (shape sigma_two)) (X ↦ (X, empty_endos X))
        sigma_two_shape_paths_embedding
        (embedding_of_equiv Type (RhoTarget Empty) empty_structure_equiv))

def empty_signed_word_nil (w : SignedWord Empty) : Id (SignedWord Empty) w nil.
  ≔ match w [ nil. ↦ refl (nil. : SignedWord Empty) | cons. x _ ↦ match x [ inl. e ↦ match e [] | inr. e ↦ match e [] ] ]

def empty_free_usym_unit (w : USym (constructed_free_group Empty empty_decidable_equality))
  : Id (USym (constructed_free_group Empty empty_decidable_equality)) w (usym_unit (constructed_free_group Empty empty_decidable_equality))
  ≔ let F ≔ constructed_free_group Empty empty_decidable_equality in
    let e ≔ constructed_free_group_usym_equiv Empty empty_decidable_equality in
    let P ≔ (r s : ReducedWord Empty) ↦ reduced_word_path Empty r s
        (concat (SignedWord Empty) (r .fst) nil. (s .fst) (empty_signed_word_nil (r .fst))
          (inverse (SignedWord Empty) (s .fst) nil. (empty_signed_word_nil (s .fst)))) in
    concat (USym F) w (equiv_inverse_map (USym F) (ReducedWord Empty) e (e .map w)) (usym_unit F)
      (equiv_unit (USym F) (ReducedWord Empty) e w)
      (concat (USym F) (equiv_inverse_map (USym F) (ReducedWord Empty) e (e .map w))
        (equiv_inverse_map (USym F) (ReducedWord Empty) e (e .map (usym_unit F))) (usym_unit F)
        (refl (equiv_inverse_map (USym F) (ReducedWord Empty) e) (P (e .map w) (e .map (usym_unit F))))
        (equiv_retraction (USym F) (ReducedWord Empty) e (usym_unit F)))

def sigma_two_swap : USym sigma_two ≔ permutation_symmetry (standard_set two) fin2_swap_equiv

def sigma_two_swap_nontrivial (p : Id (USym sigma_two) sigma_two_swap (usym_unit sigma_two)) : Empty
  ≔ fin2_zero_ne_one
      (inverse (Fin two) fin2_one fin2_zero
        (concat (Fin two) fin2_one (permutation_action (standard_set two) (usym_unit sigma_two) fin2_zero) fin2_zero
          (refl ((g : USym sigma_two) ↦ permutation_action (standard_set two) g fin2_zero) p)
          (permutation_action_unit (standard_set two) fin2_zero)))

def empty_not_generates (h : GeneratesGroup Empty empty_decidable_equality sigma_two empty_iota) : Empty
  ≔ let F ≔ constructed_free_group Empty empty_decidable_equality in
    let phi ≔ free_induced_hom Empty empty_decidable_equality sigma_two empty_iota in
    mere_rec (BookFiber (USym F) (USym sigma_two) (usym_hom F sigma_two phi) sigma_two_swap) Empty empty_prop
      (u ↦ sigma_two_swap_nontrivial
        (concat (USym sigma_two) sigma_two_swap (usym_hom F sigma_two phi (u .fst)) (usym_unit sigma_two) (u .snd)
          (concat (USym sigma_two) (usym_hom F sigma_two phi (u .fst)) (usym_hom F sigma_two phi (usym_unit F)) (usym_unit sigma_two)
            (refl (usym_hom F sigma_two phi) (empty_free_usym_unit (u .fst)))
            (usym_hom_unit F sigma_two phi))))
      (generates_iff_surjective Empty empty_decidable_equality sigma_two empty_iota .map h sigma_two_swap)

{` lem:gens-gp-iff, the "if" direction fails. `}
def gens_gp_if_counterexample
  : Product (RhoEmbedding sigma_two Empty empty_iota) (Not (GeneratesGroup Empty empty_decidable_equality sigma_two empty_iota))
  ≔ (empty_rho_embedding, empty_not_generates)

def gens_gp_if_refuted
  : Not ((S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G) → RhoEmbedding G S iota → GeneratesGroup S dec G iota)
  ≔ h ↦ empty_not_generates (h Empty empty_decidable_equality sigma_two empty_iota empty_rho_embedding)
