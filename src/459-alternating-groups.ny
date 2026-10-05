export "458-sign-properties"

{` Chapter 4, sec:sign-homomorphism: def:alternating-groups. The shapes of A_n
   are the pairs (A, s) with A : BΣ_n and s : Bsgn(A), designated at
   (n, Bsgn_pt(pt_2)), where pt_2 is 0 ∈ Fin 2 (= +1). For n ≥ 2 this type is a
   pointed connected groupoid and A_n is as printed. For n = 0, 1 it is not
   connected (Bsgn is constant at a two-element set), so the printed
   definition does not give a group; the corrected A_n for all n is the
   automorphism group of the designated shape, i.e. its connected component,
   which agrees with the printed one for n ≥ 2. `}

def AlternatingShapes (n : Nat) : Type ≔ Σ (BookFiniteSetsAt n) (A ↦ bsgn n A .fst .fst)

def alternating_shapes_groupoid (n : Nat) : isGroupoid (AlternatingShapes n)
  ≔ hlevel_to_groupoid (AlternatingShapes n)
      (hlevel_sigma (suc. (suc. (suc. zero.)))(BookFiniteSetsAt n) (A ↦ bsgn n A .fst .fst)
        (groupoid_to_hlevel (BookFiniteSetsAt n) (bg_groupoid (symmetric_group n)))
        (A ↦ groupoid_to_hlevel (bsgn n A .fst .fst) (set_is_groupoid (bsgn n A .fst .fst) (bsgn n A .fst .snd))))

def alternating_point_value (n : Nat) : bsgn n (standard_shape n) .fst .fst
  ≔ transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (shape sign_sigma_two) (bsgn n (standard_shape n)) (bsgn_point n) (inr. star.)

def alternating_point (n : Nat) : AlternatingShapes n ≔ (standard_shape n, alternating_point_value n)

{` Helpers (kept outside the case tree to avoid Narya bug E0500). `}
def alternating_swap_symmetry (m : Nat) : USym (symmetric_group (suc. (suc. m)))
  ≔ permutation_symmetry (standard_set (suc. (suc. m))) (fin_swap01_equiv m)

def alternating_swap_moves_point (m : Nat) (s' : bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))) .fst .fst)
  (ne : Not (Id (bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))) .fst .fst) s' (alternating_point_value (suc. (suc. m)))))
  : Id (bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))) .fst .fst)
      (transport (BookFiniteSetsAt (suc. (suc. m))) (A ↦ bsgn (suc. (suc. m)) A .fst .fst)
        (standard_shape (suc. (suc. m))) (standard_shape (suc. (suc. m))) (alternating_swap_symmetry m) (alternating_point_value (suc. (suc. m))))
      s'
  ≔ let n : Nat ≔ suc. (suc. m) in let A0 ≔ standard_shape n in
    let hT ≔ two_set_two_element (bsgn n A0) in
    let s0 ≔ alternating_point_value n in
    let tt ≔ bsigma_two_transport (bsgn n A0) (bsgn n A0) (refl (bsgn n) (alternating_swap_symmetry m)) in
    two_element_ne_ne (bsgn n A0 .fst .fst) hT (tt .map s0) s0 s'
      (r ↦ two_moves_true_moved (bsgn n A0 .fst .fst) hT tt (bsgn_swap01_moves m) s0 (inverse (bsgn n A0 .fst .fst) (tt .map s0) s0 r))
      (r ↦ ne r)

{` Two generic ways to identify (a, s0) with (b, y) in Σ X F, given q : b = a:
   either q transports y to s0, or a loop tau at a moves s0 to the transport of y. `}
def sigma_shape_path_same (X : Type) (F : X → Type) (a b : X) (s0 : F a) (y : F b) (q : Id X b a)
  (e : Id (F a) (transport X F b a q y) s0) : Id (Σ X F) (a, s0) (b, y)
  ≔ (inverse X b a q,
      pathover_of_eq X F a b (inverse X b a q) s0 y
        (concat (F b) (transport X F a b (inverse X b a q) s0) (transport X F a b (inverse X b a q) (transport X F b a q y)) y
          (refl (transport X F a b (inverse X b a q)) (inverse (F a) (transport X F b a q y) s0 e))
          (transport_inverse_roundtrip X F b a q y)))

def sigma_shape_path_moved (X : Type) (F : X → Type) (a b : X) (s0 : F a) (y : F b) (q : Id X b a)
  (tau : Id X a a) (mv : Id (F a) (transport X F a a tau s0) (transport X F b a q y)) : Id (Σ X F) (a, s0) (b, y)
  ≔ (concat X a a b tau (inverse X b a q),
      pathover_of_eq X F a b (concat X a a b tau (inverse X b a q)) s0 y
        (calc transport X F a b (concat X a a b tau (inverse X b a q)) s0
          = transport X F a b (inverse X b a q) (transport X F a a tau s0) by transport_concat X F a a b tau (inverse X b a q) s0
          = transport X F a b (inverse X b a q) (transport X F b a q y) by refl (transport X F a b (inverse X b a q)) mv
          = y by transport_inverse_roundtrip X F b a q y ∎))

{` For n ≥ 2 every shape is merely identified with the designated one. `}
def alternating_point_path_step (m : Nat) (u : AlternatingShapes (suc. (suc. m)))
  (q : Id (BookFiniteSetsAt (suc. (suc. m))) (u .fst) (standard_shape (suc. (suc. m))))
  (d : Decidable (Id (bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))) .fst .fst)
    (transport (BookFiniteSetsAt (suc. (suc. m))) (A ↦ bsgn (suc. (suc. m)) A .fst .fst) (u .fst) (standard_shape (suc. (suc. m))) q (u .snd))
    (alternating_point_value (suc. (suc. m)))))
  : Id (AlternatingShapes (suc. (suc. m))) (alternating_point (suc. (suc. m))) u
  ≔ let n : Nat ≔ suc. (suc. m) in
    match d [
    | inl. e ↦ sigma_shape_path_same (BookFiniteSetsAt n) (A ↦ bsgn n A .fst .fst) (standard_shape n) (u .fst)
        (alternating_point_value n) (u .snd) q e
    | inr. ne ↦ sigma_shape_path_moved (BookFiniteSetsAt n) (A ↦ bsgn n A .fst .fst) (standard_shape n) (u .fst)
        (alternating_point_value n) (u .snd) q (alternating_swap_symmetry m)
        (alternating_swap_moves_point m
          (transport (BookFiniteSetsAt n) (A ↦ bsgn n A .fst .fst) (u .fst) (standard_shape n) q (u .snd)) ne) ]

def alternating_point_path (m : Nat) (u : AlternatingShapes (suc. (suc. m)))
  : Mere (Id (AlternatingShapes (suc. (suc. m))) (alternating_point (suc. (suc. m))) u)
  ≔ let n : Nat ≔ suc. (suc. m) in let A0 ≔ standard_shape n in
    let X ≔ BookFiniteSetsAt n in let F : X → Type ≔ A ↦ bsgn n A .fst .fst in
    mere_rec (Id X A0 (u .fst)) (Mere (Id (AlternatingShapes n) (alternating_point n) u))
      (mere_isprop (Id (AlternatingShapes n) (alternating_point n) u))
      (p ↦ let q ≔ inverse X A0 (u .fst) p in
        mere (Id (AlternatingShapes n) (alternating_point n) u)
          (alternating_point_path_step m u q
            (two_element_decidable_equality (F A0) (two_set_two_element (bsgn n A0))
              (transport X F (u .fst) A0 q (u .snd)) (alternating_point_value n))))
      (bg_connected (symmetric_group n) .snd A0 (u .fst))

def alternating_shapes_connected (m : Nat) : Connected (AlternatingShapes (suc. (suc. m)))
  ≔ let n : Nat ≔ suc. (suc. m) in let S ≔ AlternatingShapes n in
    (mere S (alternating_point n),
      u v ↦ mere_rec (Id S (alternating_point n) u) (Mere (Id S u v)) (mere_isprop (Id S u v))
        (p ↦ trunc_map native_truncation (Id S (alternating_point n) v) (Id S u v)
          (r ↦ concat S u (alternating_point n) v (inverse S (alternating_point n) u p) r) (alternating_point_path m v))
        (alternating_point_path m u))

{` def:alternating-groups as printed, for n ≥ 2. `}
def alternating_group_printed (m : Nat) : Group
  ≔ mkgroup (AlternatingShapes (suc. (suc. m)), alternating_point (suc. (suc. m)),
      alternating_shapes_connected m, alternating_shapes_groupoid (suc. (suc. m)))

{` For n = 0, 1 the type of shapes is not connected: the two elements of
   Bsgn(n) = Fin 2 lie in different components. `}
def alternating_shapes_small_not_connected (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.)))
  (c : Connected (AlternatingShapes n)) : Empty
  ≔ let A0 ≔ standard_shape n in
    let hT ≔ two_set_two_element (bsgn n A0) in
    let s0 ≔ alternating_point_value n in
    let s1 ≔ two_element_other (bsgn n A0 .fst .fst) hT s0 in
    let F : AlternatingShapes n → Fin two
      ≔ u ↦ bsigma_two_transport (bsgn n (u .fst)) (shape sign_sigma_two) (bsgn_small_constant n hn (u .fst)) .map (u .snd) in
    mere_rec (Id (AlternatingShapes n) (A0, s0) (A0, s1)) Empty empty_prop
      (p ↦ two_element_other_ne (bsgn n A0 .fst .fst) hT s0
        (inverse (bsgn n A0 .fst .fst) s0 s1
          (equiv_injective_path (bsgn n A0 .fst .fst) (Fin two)
            (bsigma_two_transport (bsgn n A0) (shape sign_sigma_two) (bsgn_small_constant n hn A0)) s0 s1 (refl F p))))
      (c .snd (A0, s0) (A0, s1))

{` The corrected definition for every n: the automorphism group of the
   designated shape (its connected component). `}
def alternating_group (n : Nat) : Group
  ≔ automorphism_group (AlternatingShapes n) (alternating_shapes_groupoid n) (alternating_point n)

def alternating_component_equiv (X : Type) (x : X) (h : Connected X) : Equiv (NativeComponent X x) X
  ≔ quasi_inverse_equiv (NativeComponent X x) X (u ↦ u .fst) (y ↦ (y, h .snd x y))
      (u ↦ component_path X x (u .fst, h .snd x (u .fst)) u (refl (u .fst)))
      (y ↦ refl y)

def alternating_group_printed_path (m : Nat) : Id Group (alternating_group (suc. (suc. m))) (alternating_group_printed m)
  ≔ let n : Nat ≔ suc. (suc. m) in
    group_path_from_pointed_equiv (alternating_group n) (alternating_group_printed m)
      ((u ↦ u .fst, refl (alternating_point n)),
        book_equivalence (NativeComponent (AlternatingShapes n) (alternating_point n)) (AlternatingShapes n)
          (alternating_component_equiv (AlternatingShapes n) (alternating_point n) (alternating_shapes_connected m)) .equiv)

{` The symmetries in A_n are the even permutations: USym A_n ≃ symmetries σ of
   Σ_n with sgn σ = +1 (n ≥ 2). `}
def EvenSymmetries (n : Nat) : Type ≔ Σ (USym (symmetric_group n)) (s ↦ Id Sign (sigma_two_sign (usgn n s)) plus.)

def alternating_fixed_iff_even (m : Nat) (s : USym (symmetric_group (suc. (suc. m))))
  : Equiv (Id (bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))) .fst .fst)
        (transport (BookFiniteSetsAt (suc. (suc. m))) (A ↦ bsgn (suc. (suc. m)) A .fst .fst)
          (standard_shape (suc. (suc. m))) (standard_shape (suc. (suc. m))) s (alternating_point_value (suc. (suc. m))))
        (alternating_point_value (suc. (suc. m))))
      (Id Sign (sigma_two_sign (usgn (suc. (suc. m)) s)) plus.)
  ≔ let n : Nat ≔ suc. (suc. m) in let A0 ≔ standard_shape n in
    let T ≔ bsgn n A0 in let hT ≔ two_set_two_element T in
    let s0 ≔ alternating_point_value n in
    let tt ≔ bsigma_two_transport T T (refl (bsgn n) s) in
    let mv ≔ two_loop_moves T (refl (bsgn n) s) in
    let sgn_eq : Id Sign (sigma_two_sign (usgn n s)) (bool_sign mv)
      ≔ two_loop_sign_conjugate (shape sign_sigma_two) T (bsgn_point n) (refl (bsgn n) s) in
    iff_equiv (Id (T .fst .fst) (tt .map s0) s0) (Id Sign (sigma_two_sign (usgn n s)) plus.)
      (T .fst .snd (tt .map s0) s0) (sign_set (sigma_two_sign (usgn n s)) plus.)
      (r ↦ concat Sign (sigma_two_sign (usgn n s)) (bool_sign mv) plus. sgn_eq
        (refl bool_sign
          (concat Bool mv (two_differ (T .fst .fst) hT s0 (tt .map s0)) false.
            (two_moves_value (T .fst .fst) hT tt s0)
            (two_differ_eq (T .fst .fst) hT s0 (tt .map s0) (inverse (T .fst .fst) (tt .map s0) s0 r)))))
      (q ↦ two_moves_false_fixed (T .fst .fst) hT tt
        (bool_sign_injective mv false.
          (concat Sign (bool_sign mv) (sigma_two_sign (usgn n s)) plus. (inverse Sign (sigma_two_sign (usgn n s)) (bool_sign mv) sgn_eq) q))
        s0)

def alternating_usym_even (m : Nat) : Equiv (USym (alternating_group_printed m)) (EvenSymmetries (suc. (suc. m)))
  ≔ let n : Nat ≔ suc. (suc. m) in let A0 ≔ standard_shape n in
    let X ≔ BookFiniteSetsAt n in let F : X → Type ≔ A ↦ bsgn n A .fst .fst in
    let s0 ≔ alternating_point_value n in
    compose_equiv (USym (alternating_group_printed m)) (SigmaPath X F (A0, s0) (A0, s0)) (EvenSymmetries n)
      (canonical_inverse_equiv (SigmaPath X F (A0, s0) (A0, s0)) (Id (AlternatingShapes n) (A0, s0) (A0, s0))
        (sigma_path_equiv X F (A0, s0) (A0, s0)))
      (family_equiv (Id X A0 A0) (p ↦ Id F p s0 s0) (p ↦ Id Sign (sigma_two_sign (usgn n p)) plus.)
        (p ↦ compose_equiv (Id F p s0 s0) (Id (F A0) (transport X F A0 A0 p s0) s0) (Id Sign (sigma_two_sign (usgn n p)) plus.)
          (pathover_transport_equiv X F A0 A0 p s0 s0) (alternating_fixed_iff_even m p)))

{` "The shapes of A_n are sign-ordered n-element sets": for n ≥ 2, Bsgn(A) is
   the set of sign orderings of A (bsgn_quotient_path, module 455), and the
   designated shape carries the class of the standard local ordering. `}
def alternating_point_standard_dec (m : Nat) (d : Decidable (Mere (TwoSubsets (Fin (suc. (suc. m))))))
  : Id (ParityQuotient (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m)))))
      (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst)
        (sign_mu_pointed (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))) d
          .fst (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m)))))
        (parity_quotient_bsigma_two (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
          (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m)))) (sign_subsets_inhabited m (standard_shape (suc. (suc. m)))))
        (sign_mu_value_ne (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
          (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m)))) (sign_subsets_inhabited m (standard_shape (suc. (suc. m)))) d)
        (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (shape sign_sigma_two)
          (sign_mu_pointed (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))) d
            .fst (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m)))))
          (concat (BookFiniteSetsAt two) (shape sign_sigma_two)
            (sign_mu_pointed (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))) d
              .fst (_ ↦ shape sign_sigma_two))
            (sign_mu_pointed (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))) d
              .fst (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m)))))
            (sign_mu_pointed (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))) d .snd)
            (refl (sign_mu_pointed (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))) d .fst)
              (standard_order_family_path (suc. (suc. m)))))
          (inr. star.)))
      (parity_class (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m)))) (standard_local_ordering (suc. (suc. m))))
  ≔ let n : Nat ≔ suc. (suc. m) in
    let B2 ≔ BookFiniteSetsAt two in let car : B2 → Type ≔ T ↦ T .fst .fst in
    let E ≔ TwoSubsets (Fin n) in let hE ≔ sign_subsets_finite n (standard_shape n) in
    let P ≔ two_subset_bsigma (Fin n) (fin_set n) in
    let c : E → B2 ≔ _ ↦ shape sign_sigma_two in
    let ne ≔ sign_subsets_inhabited m (standard_shape n) in
    let al ≔ standard_order_family_path n in
    match d [
    | inl. ne' ↦
        let Bmu : (E → B2) → B2 ≔ P' ↦ parity_quotient_bsigma_two E hE P' ne' in
        let f0 ≔ sign_mu_base_section E in
        calc transport B2 car (Bmu P) (parity_quotient_bsigma_two E hE P ne) (sign_mu_value_ne E hE P ne (inl. ne'))
            (transport B2 car (shape sign_sigma_two) (Bmu P)
              (concat B2 (shape sign_sigma_two) (Bmu c) (Bmu P) (sign_mu_point E hE ne') (refl Bmu al)) (inr. star.))
          = transport B2 car (shape sign_sigma_two) (Bmu P)
              (concat B2 (shape sign_sigma_two) (Bmu c) (Bmu P) (sign_mu_point E hE ne') (refl Bmu al)) (inr. star.)
            by transport_refl B2 car (Bmu P)
              (transport B2 car (shape sign_sigma_two) (Bmu P) (concat B2 (shape sign_sigma_two) (Bmu c) (Bmu P) (sign_mu_point E hE ne') (refl Bmu al)) (inr. star.))
          = transport B2 car (Bmu c) (Bmu P) (refl Bmu al) (sign_mu_point_equiv E hE ne' .map (inr. star.))
            by transport_concat B2 car (shape sign_sigma_two) (Bmu c) (Bmu P) (sign_mu_point E hE ne') (refl Bmu al) (inr. star.)
          = transport B2 car (Bmu c) (Bmu P) (refl Bmu al) (parity_class E hE c f0)
            by refl (transport B2 car (Bmu c) (Bmu P) (refl Bmu al)) (sign_mu_point_zero E hE ne')
          = parity_class E hE P (transport (E → B2) (LocalSections E) c P al f0)
            by quotient_family_transport (E → B2) (LocalSections E) (parity_relation E hE) c P al f0
          = parity_class E hE P (standard_local_ordering n)
            by refl (parity_class E hE P)
              (funext E (e ↦ P e .fst .fst) (transport (E → B2) (LocalSections E) c P al f0) (standard_local_ordering n)
                (e ↦ calc transport (E → B2) (LocalSections E) c P al f0 e
                    = transport B2 car (shape sign_sigma_two) (P e) (al (refl e)) (inr. star.)
                      by local_sections_transport E c P al f0 e
                    = transport B2 car (shape sign_sigma_two) (P e) (standard_order_path n e) (inr. star.)
                      by refl ((q ↦ transport B2 car (shape sign_sigma_two) (P e) q (inr. star.)) : Id B2 (shape sign_sigma_two) (P e) → P e .fst .fst)
                        (inverse (Id B2 (shape sign_sigma_two) (P e)) (standard_order_path n e) (al (refl e))
                          (funext_beta E (_ ↦ B2) c P (standard_order_path n) e))
                    = standard_local_ordering n e by refl (standard_local_ordering n e) ∎)) ∎
    | inr. no ↦ match no ne [] ]

def alternating_point_standard (m : Nat)
  : Id (SignOrderings (Fin (suc. (suc. m))) (fin_set (suc. (suc. m))) (bsigma_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))))
      (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (bsgn_quotient m (standard_shape (suc. (suc. m)))) (bsgn_quotient_path m (standard_shape (suc. (suc. m))))
        (alternating_point_value (suc. (suc. m))))
      (parity_class (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m)))) (standard_local_ordering (suc. (suc. m))))
  ≔ alternating_point_standard_dec m
      (finite_inhabited_decidable (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))))
