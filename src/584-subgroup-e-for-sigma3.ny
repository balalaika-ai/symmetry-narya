export "583-fixed-point-subgroups"

{` Chapter 5, exa:EforSG3: the subgroup (X, k) of Σ_{m+1} fixing the new point
   k = inr ★ (the book's "3" for m = 2) and the monomorphism (Σ_m, i_m) of
   ex:SGninSGn+1 correspond under lem:SubG=MonoG: F(X, inr ★) = (Σ_m, i_m),
   hence (X, inr ★) = E(Σ_m, i_m) in Sub(Σ_{m+1}). This is proved for every m;
   the book's case is m = 2. `}

{` Bi_m ∘ (S, s) ↦ S ∖ {s} is the first projection, up to the splitting
   S ≃ (S ∖ {s}) + 1. `}
def fix_point_restore_path (m : Nat) (u : PointedFiniteSetsAt (suc. m))
  : Id (BookFiniteSetsAt (suc. m))
      (hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m) (finite_remove_point m u))
      (u .fst)
  ≔ let S ≔ u .fst in
    let s ≔ u .snd in
    let dS ≔ finite_decidable_equality (S .fst .fst) (finite_sets_at_finite (suc. m) S) in
    finite_sets_path (suc. m)
      (hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m) (finite_remove_point m u)) S
      (canonical_inverse_equiv (S .fst .fst) (Sum (Without (S .fst .fst) s) Unit) (point_split_equiv (S .fst .fst) dS s))

{` The pointing coherence: the loop at sh_{Σ_{m+1}} built from the pointing paths
   acts trivially on Fin (m+1), hence is refl (gset_permutation_ext). `}
def fix_point_loop (m : Nat) : USym (symmetric_group (suc. m))
  ≔ let C ≔ BookFiniteSetsAt (suc. m) in
    let c0 ≔ shape (symmetric_group (suc. m)) in
    let pt' : PointedFiniteSetsAt (suc. m) ≔ (c0, inr. star.) in
    let ept ≔ fixed_point_subgroup_pointed_equiv m (inr. star.) .fst .snd in
    let Bi ≔ hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m) in
    concat C c0 (Bi (finite_remove_point m pt')) c0
      (concat C c0 c0 (Bi (finite_remove_point m pt')) (refl c0)
        (map_path (BookFiniteSetsAt m) C Bi (shape (symmetric_group m)) (finite_remove_point m pt') ept))
      (fix_point_restore_path m pt')

def fix_point_loop_pointwise (m : Nat) (x : Fin (suc. m))
  : Id (Fin (suc. m))
      (transport (BookFiniteSetsAt (suc. m)) (c ↦ c .fst .fst)
        (hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m)
          (finite_remove_point m (shape (symmetric_group (suc. m)), inr. star.)))
        (shape (symmetric_group (suc. m)))
        (fix_point_restore_path m (shape (symmetric_group (suc. m)), inr. star.))
        (transport (BookFiniteSetsAt (suc. m)) (c ↦ c .fst .fst) (shape (symmetric_group (suc. m)))
          (hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m)
            (finite_remove_point m (shape (symmetric_group (suc. m)), inr. star.)))
          (map_path (BookFiniteSetsAt m) (BookFiniteSetsAt (suc. m))
            (hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m))
            (shape (symmetric_group m)) (finite_remove_point m (shape (symmetric_group (suc. m)), inr. star.))
            (fixed_point_subgroup_pointed_equiv m (inr. star.) .fst .snd))
          x))
      x
  ≔ let W ≔ Without (Fin (suc. m)) (inr. star.) in
    let e1 ≔ canonical_inverse_equiv W (Fin m) (without_fin_equiv m (inr. star.)) in
    let r ≔ ua (Fin m) W e1 in
    let C ≔ BookFiniteSetsAt (suc. m) in
    let c0 ≔ shape (symmetric_group (suc. m)) in
    let c1 ≔ hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m)
      (finite_remove_point m (c0, inr. star.)) in
    let h ≔ fix_point_restore_path m (c0, inr. star.) in
    match x [
    | inl. y ↦ map_path (Sum W Unit) (Fin (suc. m)) (z ↦ transport C (c ↦ c .fst .fst) c1 c0 h z)
        (transport Type (Y ↦ Y) (Sum (Fin m) Unit) (Sum W Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) r) (inl. y))
        (inl. (transport Type (Y ↦ Y) (Fin m) W r y))
        (transport_sum_right_inl Unit (Fin m) W r y)
    | inr. u ↦ match u [ star. ↦
        map_path (Sum W Unit) (Fin (suc. m)) (z ↦ transport C (c ↦ c .fst .fst) c1 c0 h z)
          (transport Type (Y ↦ Y) (Sum (Fin m) Unit) (Sum W Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) r) (inr. star.))
          (inr. star.)
          (transport_sum_right_inr Unit (Fin m) W r star.) ] ]

def fix_point_loop_action (m : Nat) (x : Fin (suc. m))
  : Id (Fin (suc. m)) (permutation_action (standard_set (suc. m)) (fix_point_loop m) x) x
  ≔ let C ≔ BookFiniteSetsAt (suc. m) in
    let F : C → Type ≔ c ↦ c .fst .fst in
    let c0 ≔ shape (symmetric_group (suc. m)) in
    let pt' : PointedFiniteSetsAt (suc. m) ≔ (c0, inr. star.) in
    let ept ≔ fixed_point_subgroup_pointed_equiv m (inr. star.) .fst .snd in
    let Bi ≔ hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m) in
    let c1 ≔ Bi (finite_remove_point m pt') in
    let a ≔ map_path (BookFiniteSetsAt m) C Bi (shape (symmetric_group m)) (finite_remove_point m pt') ept in
    let h ≔ fix_point_restore_path m pt' in
    let W ≔ Without (Fin (suc. m)) (inr. star.) in
    let t1 : Fin (suc. m) → Sum W Unit ≔ y ↦ transport C F c0 c1 a y in
    calc
      permutation_action (standard_set (suc. m)) (fix_point_loop m) x
      = transport C F c1 c0 h (transport C F c0 c1 (concat C c0 c0 c1 (refl c0) a) x)
        by transport_concat C F c0 c1 c0 (concat C c0 c0 c1 (refl c0) a) h x
      = transport C F c1 c0 h (transport C F c0 c1 a (transport C F c0 c0 (refl c0) x))
        by map_path (Sum W Unit) (Fin (suc. m)) (transport C F c1 c0 h)
             (transport C F c0 c1 (concat C c0 c0 c1 (refl c0) a) x) (transport C F c0 c1 a (transport C F c0 c0 (refl c0) x))
             (transport_concat C F c0 c0 c1 (refl c0) a x)
      = transport C F c1 c0 h (t1 x)
        by map_path (Fin (suc. m)) (Fin (suc. m)) (y ↦ transport C F c1 c0 h (t1 y))
             (transport C F c0 c0 (refl c0) x) x (transport_refl C F c0 x)
      = x by fix_point_loop_pointwise m x ∎

def fix_point_loop_refl (m : Nat) : Id (USym (symmetric_group (suc. m))) (fix_point_loop m) (refl (shape (symmetric_group (suc. m))))
  ≔ gset_permutation_ext (standard_set (suc. m)) (fix_point_loop m) (refl (shape (symmetric_group (suc. m))))
      (x ↦ concat (Fin (suc. m)) (permutation_action (standard_set (suc. m)) (fix_point_loop m) x) x
        (permutation_action (standard_set (suc. m)) (refl (shape (symmetric_group (suc. m)))) x)
        (fix_point_loop_action m x)
        (inverse (Fin (suc. m)) (permutation_action (standard_set (suc. m)) (refl (shape (symmetric_group (suc. m)))) x) x
          (transport_refl Type (Y ↦ Y) (Fin (suc. m)) x)))

{` F(X, inr ★) = (Σ_m, i_m) in Mono(Σ_{m+1}) (pointed_over_path), hence
   (X, inr ★) = E(Σ_m, i_m) in Sub(Σ_{m+1}). `}
def fix_point_homotopy (m : Nat)
  : PointedHomotopy (BG (subgroup_group (symmetric_group (suc. m)) (fixed_point_subgroup m (inr. star.))))
      (BG (symmetric_group (suc. m)))
      (book_pointed_compose (BG (subgroup_group (symmetric_group (suc. m)) (fixed_point_subgroup m (inr. star.))))
        (BG (symmetric_group m)) (BG (symmetric_group (suc. m)))
        (fixed_point_subgroup_pointed_equiv m (inr. star.) .fst)
        (hom_B (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m)))
      (hom_B (subgroup_group (symmetric_group (suc. m)) (fixed_point_subgroup m (inr. star.))) (symmetric_group (suc. m))
        (subgroup_inclusion (symmetric_group (suc. m)) (fixed_point_subgroup m (inr. star.))))
  ≔ (u ↦ fix_point_restore_path m u, fix_point_loop_refl m)

def fix_point_mono_path (m : Nat)
  : Id (GroupMonos (symmetric_group (suc. m)))
      (subgroup_to_mono (symmetric_group (suc. m)) (fixed_point_subgroup m (inr. star.)))
      (symmetric_group_inclusion_monomorphism m)
  ≔ let K ≔ symmetric_group (suc. m) in
    let S ≔ fixed_point_subgroup m (inr. star.) in
    let B ≔ BG K in
    map_path (MonoData K) (GroupMonos K) (mono_data_to_mono K)
      (mono_to_mono_data K (subgroup_to_mono K S)) (mono_to_mono_data K (symmetric_group_inclusion_monomorphism m))
      (subtype_equal (PointedMapsOver B)
        (w ↦ Product (Product (Connected (w .fst .carrier)) (isGroupoid (w .fst .carrier)))
          (IsEmbedding (Loop (w .fst)) (USym K) (loops_map (w .fst) B (w .snd))))
        (mono_data_prop K)
        (mono_to_mono_data K (subgroup_to_mono K S)) (mono_to_mono_data K (symmetric_group_inclusion_monomorphism m))
        (pointed_over_path B (BG (subgroup_group K S)) (BG (symmetric_group m))
          (hom_B (subgroup_group K S) K (subgroup_inclusion K S))
          (hom_B (symmetric_group m) K (symmetric_group_inclusion m))
          (fixed_point_subgroup_pointed_equiv m (inr. star.)) (fix_point_homotopy m)))

def fix_point_subgroup_e_path (m : Nat)
  : Id (Subgroups (symmetric_group (suc. m))) (fixed_point_subgroup m (inr. star.))
      (mono_to_subgroup (symmetric_group (suc. m)) (symmetric_group_inclusion_monomorphism m))
  ≔ let K ≔ symmetric_group (suc. m) in
    let S ≔ fixed_point_subgroup m (inr. star.) in
    concat (Subgroups K) S (mono_to_subgroup K (subgroup_to_mono K S))
      (mono_to_subgroup K (symmetric_group_inclusion_monomorphism m))
      (inverse (Subgroups K) (mono_to_subgroup K (subgroup_to_mono K S)) S (subgroup_mono_roundtrip K S))
      (map_path (GroupMonos K) (Subgroups K) (mono_to_subgroup K) (subgroup_to_mono K S)
        (symmetric_group_inclusion_monomorphism m) (fix_point_mono_path m))
