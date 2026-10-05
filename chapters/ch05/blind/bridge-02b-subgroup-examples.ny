{` Bridges for chapter 5, blind file 02-subgroups, part 2: the examples and exercises
   (ex:Rm0-subgroup, exa:fix1subSGn, xca:n-is-ptd-n+1, xca:A-is-A-1+1, exa:C3subC6, ex:SGninSGn+1, xca:SG2subSG3,
   xca:C3subSG3, exa:EforSG3, xca:lagrange-Z-action-Rm). `}
export "bridge-02-subgroups"
export "../../../src/585-repointed-inclusions"
export "../../../src/593-c3-in-sigma3-monos"
export "../../../src/595-circle-power-lagrange"

{` Round trip of transport along a path of types (as in module 1500, outside this import closure). `}
def bridge_trr_trl (A B : Type) (e : Id Type A B) (b : B) : Id B (e .trr (e .trl b)) b
  ≔ J Type A (B' e' ↦ (b' : B') → Id B' (e' .trr (e' .trl b')) b')
      (b' ↦ concat A (refl A .trr (refl A .trl b')) (refl A .trl b') b'
         (inverse A (refl A .trl b') (refl A .trr (refl A .trl b')) (refl A .liftr (refl A .trl b')))
         (refl A .liftl b')) B e b

{` The inverse of an equivalence whose map is transport along p is backwards transport along p. `}
def bridge_inv_trl (A B : Type) (p : Id Type A B) (e : Equiv A B) (h : (a : A) → Id B (e .map a) (p .trr a)) (b : B)
  : Id A (equiv_inverse_map A B e b) (p .trl b)
  ≔ equivalence_injective A B e (equiv_inverse_map A B e b) (p .trl b)
      (concat B (e .map (equiv_inverse_map A B e b)) b (e .map (p .trl b))
        (equiv_counit A B e b)
        (inverse B (e .map (p .trl b)) b
          (concat B (e .map (p .trl b)) (p .trr (p .trl b)) b (h (p .trl b)) (bridge_trr_trl A B p b))))

{` ex:Rm0-subgroup. The blind R_m is our power_circle_family on the nose; the blind 0 is ours. `}
def bridge_def_Rm (C : CircleSignature) (n : Nat) : Id (GSet (circle_group C)) (blind_Rm C n) (rmsub_gset C n)
  ≔ refl (rmsub_gset C n)

def bridge_Rm_zero (C : CircleSignature) (n : Nat) : Id (RmBase C n) (rmsub_point C n) (blind_Rm_zero C n)
  ≔ bridge_inv_trl (RmBase C n) (Fin (suc. n)) (power_circle_family_beta C n .fst .fst) (power_base_trivialization C n)
      (a ↦ refl (power_circle_family_beta C n .fst .fst .trr a)) (inr. star.)

def bridge_Rm_transitive : blind_Rm_transitive ≔ C n ↦ rmsub_transitive C n

def BridgeRmFix (C : CircleSignature) (n : Nat) (p : USym (circle_group C)) (y : RmBase C n) : Type
  ≔ Id (RmBase C n) (gset_usym_act (circle_group C) (rmsub_gset C n) p y) y

def bridge_Rm_mult_swap (C : CircleSignature) (n : Nat) (p : USym (circle_group C))
  (a : Int → Int) (b : Int → Int) (ab : (k : Int) → Id Int (a k) (b k))
  (m : Mere (Σ Int (k ↦ Id (USym (circle_group C)) p (loop_power (C .carrier) (C .base) (C .loop) (a k)))))
  : Mere (Σ Int (k ↦ Id (USym (circle_group C)) p (loop_power (C .carrier) (C .base) (C .loop) (b k))))
  ≔ let lp : Int → USym (circle_group C) ≔ k ↦ loop_power (C .carrier) (C .base) (C .loop) k in
    mere_rec (Σ Int (k ↦ Id (USym (circle_group C)) p (lp (a k)))) (Mere (Σ Int (k ↦ Id (USym (circle_group C)) p (lp (b k)))))
      (mere_isprop (Σ Int (k ↦ Id (USym (circle_group C)) p (lp (b k)))))
      (v ↦ mere (Σ Int (k ↦ Id (USym (circle_group C)) p (lp (b k))))
        (v .fst, concat (USym (circle_group C)) p (lp (a (v .fst))) (lp (b (v .fst))) (v .snd) (refl lp (ab (v .fst))))) m

def bridge_Rm_stabilizer : blind_Rm_stabilizer
  ≔ C n p ↦
    let m : Int ≔ pos. (suc. n) in
    let z ≔ bridge_Rm_zero C n in
    let ours ≔ rmsub_picks_out C n p in
    (h ↦ bridge_Rm_mult_swap C n p (k ↦ int_mul k m) (k ↦ int_mul m k) (k ↦ int_mul_comm k m)
           (ours .map (transport (RmBase C n) (BridgeRmFix C n p) (blind_Rm_zero C n) (rmsub_point C n)
              (inverse (RmBase C n) (rmsub_point C n) (blind_Rm_zero C n) z) h)),
     h ↦ transport (RmBase C n) (BridgeRmFix C n p) (rmsub_point C n) (blind_Rm_zero C n) z
           (equiv_inverse_map (BridgeRmFix C n p (rmsub_point C n)) (Mere (Σ Int (k ↦ Id (USym (circle_group C)) p
                (loop_power (C .carrier) (C .base) (C .loop) (int_mul k m))))) ours
              (bridge_Rm_mult_swap C n p (k ↦ int_mul m k) (k ↦ int_mul k m) (k ↦ int_mul_comm m k) h)))

{` xca:lagrange-Z-action-Rm: ours for the subgroup pointed at our 0, transported to the blind 0. `}
def BridgeRmLagrange (C : CircleSignature) (n : Nat) (y : RmBase C n) : Type
  ≔ Equiv (USym (circle_group C))
      (Product (Fin (suc. n)) (Id (ActionType (circle_group C) (rmsub_gset C n)) (C .base, y) (C .base, y)))

def bridge_lagrange_Z_action_Rm : blind_lagrange_Z_action_Rm
  ≔ C n t ↦ transport (RmBase C n) (BridgeRmLagrange C n) (rmsub_point C n) (blind_Rm_zero C n) (bridge_Rm_zero C n)
      (rmlag_fin_equiv C n)

{` ex:Rm0-subgroup, m = 0. The blind R (a recursion into Set) is not ours on the nose; it carries its own
   integer code, built from its computation law exactly as ours, and the statements follow from the generic
   encode-decode lemmas of module 27. `}
def BridgeRb (C : CircleSignature) : C .carrier → Type ≔ z ↦ blind_R C z .fst

def bridge_R_triv (C : CircleSignature) : Equiv (BridgeRb C (C .base)) Int
  ≔ set_paths_transport_equiv (blind_R C (C .base)) (Int, int_set) .map (circle_rec_beta C SetTypes blind_R_data .fst)

def bridge_R_step (C : CircleSignature) (x : BridgeRb C (C .base))
  : Id Int (bridge_R_triv C .map (refl (BridgeRb C) (C .loop) .trr x)) (int_succ (bridge_R_triv C .map x))
  ≔ automorphism_pathover_commutes (blind_R C (C .base)) (Int, int_set) (circle_rec_beta C SetTypes blind_R_data .fst)
      (set_paths_transport_equiv (blind_R C (C .base)) (blind_R C (C .base)) .map (refl (blind_R C) (C .loop)))
      (set_paths_transport_equiv (Int, int_set) (Int, int_set) .map (set_types_path (Int, int_set) (Int, int_set) int_succ_equiv))
      .map (refl ((b l ↦ set_paths_transport_equiv b b .map l) : (b : SetTypes) → Id SetTypes b b → SetAutomorphisms b)
              (circle_rec_beta C SetTypes blind_R_data .fst) (circle_rec_beta C SetTypes blind_R_data .snd))
      x

def bridge_R_code (C : CircleSignature) : CircleCode C (BridgeRb C)
  ≔ let A ≔ BridgeRb C (C .base) in
    let E ≔ bridge_R_triv C in
    let inv ≔ equiv_inverse_map A Int E in
    let T : A → A ≔ x ↦ refl (BridgeRb C) (C .loop) .trr x in
    (enumeration ≔ canonical_inverse_equiv A Int E,
     step ≔ k ↦ equivalence_injective A Int E (T (inv k)) (inv (int_succ k))
       (concat Int (E .map (T (inv k))) (int_succ (E .map (inv k))) (E .map (inv (int_succ k)))
          (bridge_R_step C (inv k))
          (concat Int (int_succ (E .map (inv k))) (int_succ k) (E .map (inv (int_succ k)))
             (refl int_succ (equiv_counit A Int E k))
             (inverse Int (E .map (inv (int_succ k))) (int_succ k) (equiv_counit A Int E (int_succ k))))))

def bridge_R_zero (C : CircleSignature)
  : Id (BridgeRb C (C .base)) (code_root C (BridgeRb C) (bridge_R_code C)) (blind_R_zero C)
  ≔ bridge_inv_trl (BridgeRb C (C .base)) Int (circle_rec_beta C SetTypes blind_R_data .fst .fst) (bridge_R_triv C)
      (a ↦ refl (circle_rec_beta C SetTypes blind_R_data .fst .fst .trr a)) int_zero

def bridge_R_total_contractible (C : CircleSignature) : BookIsContr (Σ (C .carrier) (BridgeRb C))
  ≔ book_contraction (Σ (C .carrier) (BridgeRb C))
      (hlevel_equiv zero. (Σ (C .carrier) (z ↦ Id (C .carrier) (C .base) z)) (Σ (C .carrier) (BridgeRb C))
        (family_equiv (C .carrier) (z ↦ Id (C .carrier) (C .base) z) (BridgeRb C)
          (circle_path_code_equiv C (BridgeRb C) (bridge_R_code C)))
        (iscontr_idfrom (C .carrier) (C .base)))

def bridge_R_transitive : blind_R_transitive
  ≔ C ↦ connected_action_type_transitive (circle_group C) (blind_R C)
      (contractible_connected (Σ (C .carrier) (BridgeRb C)) (bridge_R_total_contractible C))

def bridge_R_loop_power : blind_R_loop_power
  ≔ C k ↦
    let A ≔ BridgeRb C (C .base) in
    let E ≔ bridge_R_triv C in
    let m ≔ bridge_R_code C in
    let lk ≔ loop_power (C .carrier) (C .base) (C .loop) k in
    let act : A → A ≔ y ↦ transport (C .carrier) (BridgeRb C) (C .base) (C .base) lk y in
    concat Int (E .map (act (blind_R_zero C))) (E .map (act (code_root C (BridgeRb C) m))) k
      (refl ((y ↦ E .map (act y)) : A → Int)
        (inverse A (code_root C (BridgeRb C) m) (blind_R_zero C) (bridge_R_zero C)))
      (concat Int (E .map (act (code_root C (BridgeRb C) m))) (E .map (m .enumeration .map k)) k
        (refl (E .map) (code_encode_power C (BridgeRb C) m k))
        (equiv_counit A Int E k))

def BridgeRFix (C : CircleSignature) (p : USym (circle_group C)) (y : BridgeRb C (C .base)) : Type
  ≔ Id (BridgeRb C (C .base)) (transport (C .carrier) (BridgeRb C) (C .base) (C .base) p y) y

def bridge_R_picks_out_root (C : CircleSignature) (g : USym (circle_group C))
  : Product (BridgeRFix C g (code_root C (BridgeRb C) (bridge_R_code C)) → Id (USym (circle_group C)) g (refl (C .base)))
      (Id (USym (circle_group C)) g (refl (C .base)) → BridgeRFix C g (code_root C (BridgeRb C) (bridge_R_code C)))
  ≔ let R ≔ BridgeRb C in
    let m ≔ bridge_R_code C in
    let enc ≔ code_encode C R m (C .base) in
    let x0 ≔ code_root C R m in
    (h ↦ equivalence_injective (Id (C .carrier) (C .base) (C .base)) (R (C .base)) (circle_path_code_equiv C R m (C .base))
        g (refl (C .base))
        (concat (R (C .base)) (enc g) x0 (enc (refl (C .base))) h
          (inverse (R (C .base)) (enc (refl (C .base))) x0 (transport_refl (C .carrier) R (C .base) x0))),
     e ↦ concat (R (C .base)) (enc g) (enc (refl (C .base))) x0 (refl enc e) (transport_refl (C .carrier) R (C .base) x0))

def bridge_R_stabilizer : blind_R_stabilizer
  ≔ C p ↦
    let A ≔ BridgeRb C (C .base) in
    let r ≔ code_root C (BridgeRb C) (bridge_R_code C) in
    (h ↦ bridge_R_picks_out_root C p .fst
           (transport A (BridgeRFix C p) (blind_R_zero C) r (inverse A r (blind_R_zero C) (bridge_R_zero C)) h),
     e ↦ transport A (BridgeRFix C p) r (blind_R_zero C) (bridge_R_zero C) (bridge_R_picks_out_root C p .snd e))

{` exa:fix1subSGn. `}
def bridge_fix1_action : blind_fix1_action
  ≔ m π k ↦ refl (permutation_action (standard_set (suc. m)) π k)

def bridge_fix1subSGn : blind_fix1subSGn
  ≔ m k t ↦
    let G ≔ symmetric_group (suc. m) in
    let X ≔ standard_symmetric_gset (suc. m) in
    group_path_iso_equiv (blind_subgroup_group G (blind_fix1_subgroup m k t)) (symmetric_group m) .map
      (concat Group (blind_subgroup_group G (blind_fix1_subgroup m k t)) (subgroup_group G (fixed_point_subgroup m k))
         (symmetric_group m)
         (bridge_group_conn G X k (blind_tot_connected G X t) (transitive_action_type_connected G X (fixed_point_gset_transitive m)))
         (fixed_point_subgroup_group_path m k))

{` xca:n-is-ptd-n+1. `}
def bridge_n_is_ptd_n1 : blind_n_is_ptd_n1 ≔ n ↦ finite_pointed_equiv n

{` xca:A-is-A-1+1. Ours removes a point with complement + Unit; the blind statement uses + Fin 1. `}
def bridge_unit_fin1_equiv : Equiv Unit (Fin (suc. zero.))
  ≔ quasi_inverse_equiv Unit (Fin (suc. zero.)) (u ↦ inr. u) [ inr. u ↦ u | inl. e ↦ match e [] ]
      (u ↦ refl u) [ inr. u ↦ refl (inr. u : Fin (suc. zero.)) | inl. e ↦ match e [] ]

def bridge_A_is_A_1_1 : blind_A_is_A_1_1
  ≔ A hA d ↦
    compose_equiv A (PointRemovals A) (Σ Type (B ↦ Id Type A (Sum B (Fin (suc. zero.)))))
      (native_equivalence A (PointRemovals A) (point_removal_equiv A d))
      (family_equiv Type (B ↦ Id Type A (Sum B Unit)) (B ↦ Id Type A (Sum B (Fin (suc. zero.))))
        (B ↦ transport_equiv (Id Type A (Sum B Unit)) (Id Type A (Sum B (Fin (suc. zero.))))
          (refl ((Y ↦ Id Type A (Sum B Y)) : Type → Type) (ua Unit (Fin (suc. zero.)) bridge_unit_fin1_equiv))))

{` exa:C3subC6. The blind C₆-set X/2 is ours on the nose. `}
def bridge_def_c3c6_F : Id (GSet blind_C6) blind_c3c6_F c6half_gset ≔ refl c6half_gset

def bridge_c3c6_transitive : blind_c3c6_transitive ≔ c6half_transitive

def bridge_c3c6_action : blind_c3c6_action ≔ π k ↦ c6half_act_class π k

def bridge_c3c6_underlying : blind_c3c6_underlying
  ≔ t ↦
    let H ≔ blind_subgroup_group blind_C6 (blind_c3c6_F, (blind_c3c6_class (inr. star.), t)) in
    group_path_iso_equiv H (cyclic_group_fin (suc. (suc. zero.))) .map
      (concat Group H (subgroup_group c6half_group c6half_subgroup) (cyclic_group_fin (suc. (suc. zero.)))
        (bridge_group_conn c6half_group c6half_gset (c6half_class c6half_q0) (blind_tot_connected c6half_group c6half_gset t)
          (transitive_action_type_connected c6half_group c6half_gset c6half_transitive))
        c6half_subgroup_is_c3)

{` ex:SGninSGn+1. The blind i_n with pointing p is our repointed inclusion at the symmetry of p. `}
def bridge_def_sigma_incl_at (n : Nat) (p : Id SetTypes (standard_set (suc. n)) (blind_plus_one (standard_set n)))
  : Id (GroupHom (symmetric_group n) (symmetric_group (suc. n))) (blind_sigma_incl_at n p)
      (repointed_inclusion n (component_path SetTypes (standard_set (suc. n)) (shape (symmetric_group (suc. n)))
        (shape (symmetric_group (suc. n))) p))
  ≔ refl (blind_sigma_incl_at n p)

def bridge_component_refl (n : Nat)
  : Id (USym (symmetric_group n)) (refl (shape (symmetric_group n)))
      (component_path SetTypes (standard_set n) (shape (symmetric_group n)) (shape (symmetric_group n)) (refl (standard_set n)))
  ≔ let u ≔ shape (symmetric_group n) in
    let e ≔ subtype_path_equiv SetTypes (x ↦ Mere (Id SetTypes (standard_set n) x)) (x ↦ mere_isprop (Id SetTypes (standard_set n) x)) u u in
    equivalence_injective (Id (BG (symmetric_group n) .carrier) u u) (Id SetTypes (u .fst) (u .fst)) e
      (refl u) (component_path SetTypes (standard_set n) u u (refl (standard_set n)))
      (inverse (Id SetTypes (u .fst) (u .fst)) (e .map (equiv_inverse_map (Id (BG (symmetric_group n) .carrier) u u) (Id SetTypes (u .fst) (u .fst)) e (refl (u .fst))))
         (refl (u .fst)) (equiv_counit (Id (BG (symmetric_group n) .carrier) u u) (Id SetTypes (u .fst) (u .fst)) e (refl (u .fst))))

def bridge_SGninSGn1_mono : blind_SGninSGn1_mono
  ≔ n ↦ repointed_inclusion_mono n (component_path SetTypes (standard_set (suc. n)) (shape (symmetric_group (suc. n)))
        (shape (symmetric_group (suc. n))) (refl (standard_set (suc. n))))

def BridgeExtends (n : Nat) (π : USym (symmetric_group n)) (p : USym (symmetric_group (suc. n))) : Type
  ≔ Product
      ((x : Fin n) → Id (Fin (suc. n))
         (permutation_action (standard_set (suc. n)) (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (repointed_inclusion n p) π) (inl. x))
         (inl. (permutation_action (standard_set n) π x)))
      (Id (Fin (suc. n))
         (permutation_action (standard_set (suc. n)) (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (repointed_inclusion n p) π) (inr. star.))
         (inr. star.))

def bridge_SGninSGn1_extends : blind_SGninSGn1_extends
  ≔ n π ↦ transport (USym (symmetric_group (suc. n))) (BridgeExtends n π) (refl (shape (symmetric_group (suc. n))))
      (component_path SetTypes (standard_set (suc. n)) (shape (symmetric_group (suc. n))) (shape (symmetric_group (suc. n)))
        (refl (standard_set (suc. n))))
      (bridge_component_refl (suc. n))
      (x ↦ symmetric_group_inclusion_inl n π x, symmetric_group_inclusion_inr n π)

{` xca:SG2subSG3 (i_3 read as i_2). With p = the symmetry of π, ours: σ is in the image iff σ fixes p⁻¹·★ = π⁻¹(★). `}
def bridge_SG2subSG3 : blind_SG2subSG3
  ≔ π σ ↦
    let K ≔ symmetric_group three in
    let X ≔ standard_symmetric_gset three in
    let F ≔ Fin three in
    let p ≔ permutation_symmetry (standard_set three) π in
    let q ≔ repointed_point two p in
    let ours ≔ repointed_image_stabilizer two p σ in
    let star3 : F ≔ inr. star. in
    let pq : Id F (π .map q) star3 ≔ gset_act_inv_right K X p star3 in
    let qx : (x : F) → Id F (π .map x) star3 → Id F x q
      ≔ x h ↦ equivalence_injective F F π x q (concat F (π .map x) star3 (π .map q) h (inverse F (π .map q) star3 pq)) in
    (t x h ↦ transport F (y ↦ Id F (gset_usym_act K X σ y) y) q x (inverse F x q (qx x h)) (ours .fst t),
     f ↦ ours .snd (f q pq))

{` xca:C3subSG3. `}
def bridge_C3subSG3 : blind_C3subSG3
  ≔ (c3inv_j, (c3inv_j_mono, (c3inv_j_prime, (c3inv_j_prime_mono,
      (E ↦ c3inv_usym_differ E,
       inverse (GroupMonos (symmetric_group three)) c3inv_j_prime_monomorphism c3inv_j_monomorphism c3inv_monos_path)))))

{` exa:EforSG3 (the printed (Σ₂, i₃) read as (Σ₂, i₂)). `}
def bridge_EforSG3 : blind_EforSG3
  ≔ t ↦
    let K ≔ symmetric_group three in
    let X ≔ standard_symmetric_gset three in
    let S ≔ fixed_point_subgroup two (inr. star.) in
    concat (BlindHomInto K) (blind_F0 K (X, (inr. star., t))) (bridge_forget_mono K (subgroup_to_mono K S))
      (symmetric_group two, blind_sigma_incl two)
      (bridge_hominto_conn K X (inr. star.) (blind_tot_connected K X t)
        (transitive_action_type_connected K X (fixed_point_gset_transitive two)))
      (concat (BlindHomInto K) (bridge_forget_mono K (subgroup_to_mono K S))
        (bridge_forget_mono K (symmetric_group_inclusion_monomorphism two)) (symmetric_group two, blind_sigma_incl two)
        (refl (bridge_forget_mono K) (fix_point_mono_path two))
        (refl ((p ↦ (symmetric_group two, repointed_inclusion two p)) : USym K → BlindHomInto K) (bridge_component_refl three)))
