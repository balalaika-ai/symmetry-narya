export "454-sign-orderings"

{` Chapter 4, sec:sign-homomorphism: def:sgn. Bsgn(A) ≔ Bμ_{E(A)}(P) for A in
   BΣ_n, pointed by the standard total order of Fin n and the pointing of Bμ.
   The definition is made for every n, as printed; for n = 0, 1 the set E(A)
   is empty, μ_{E(A)} is trivial and Bsgn is constant at the standard
   two-element set (bsgn_small_constant). For n ≥ 2, Bsgn(A) is identified
   with the set of sign orderings of A and USym sgn is computed by the parity
   of the action on the standard local ordering. `}

def bsigma_finite (n : Nat) (A : BookFiniteSetsAt n) : IsFinite (A .fst .fst)
  ≔ trunc_map native_truncation (Id SetTypes (Fin n, fin_set n) (A .fst)) (Σ Nat (m ↦ Id Type (A .fst .fst) (Fin m)))
      (p ↦ (n, inverse Type (Fin n) (A .fst .fst) (p .fst))) (A .snd)

def sign_subsets_finite (n : Nat) (A : BookFiniteSetsAt n) : IsFinite (TwoSubsets (A .fst .fst))
  ≔ ksubsets_finite (A .fst .fst) (bsigma_finite n A) two

def sign_family (n : Nat) (A : BookFiniteSetsAt n) : TwoSubsets (A .fst .fst) → BookFiniteSetsAt two
  ≔ two_subset_bsigma (A .fst .fst) (A .fst .snd)

{` def:sgn, the underlying map Bsgn÷ : BΣ_n → BΣ_2. `}
def bsgn (n : Nat) (A : BookFiniteSetsAt n) : BookFiniteSetsAt two
  ≔ sign_mu_classifying (TwoSubsets (A .fst .fst)) (sign_subsets_finite n A) (sign_family n A)

def standard_shape (n : Nat) : BookFiniteSetsAt n ≔ shape (symmetric_group n)

{` The pointing: sh_{Σ_2} = Bμ(constant family) (pointing of Bμ), followed by
   Bμ applied to the identification of the constant family with P given by
   the standard order of each two-element subset of Fin n. `}
def bsgn_point (n : Nat) : Id (BookFiniteSetsAt two) (shape sign_sigma_two) (bsgn n (standard_shape n))
  ≔ let E ≔ TwoSubsets (Fin n) in let hE ≔ sign_subsets_finite n (standard_shape n) in
    concat (BookFiniteSetsAt two) (shape sign_sigma_two) (sign_mu_classifying E hE (_ ↦ shape sign_sigma_two))
      (sign_mu_classifying E hE (two_subset_bsigma (Fin n) (fin_set n)))
      (hom_point (power_sigma_two E hE) sign_sigma_two (sign_mu E hE))
      (refl (sign_mu_classifying E hE) (standard_order_family_path n))

def bsgn_pointed (n : Nat) : BookPointedMap (BG (symmetric_group n)) (BG sign_sigma_two) ≔ (bsgn n, bsgn_point n)

{` def:sgn: the sign homomorphism sgn : Hom(Σ_n, Σ_2). `}
def sign_hom (n : Nat) : GroupHom (symmetric_group n) sign_sigma_two ≔ mkhom (symmetric_group n) sign_sigma_two (bsgn_pointed n)

def usgn (n : Nat) (s : USym (symmetric_group n)) : USym sign_sigma_two ≔ usym_hom (symmetric_group n) sign_sigma_two (sign_hom n) s

{` Values of Bμ according to the decision. `}
def sign_mu_value_ne (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (ne : Mere E) (d : Decidable (Mere E))
  : Id (BookFiniteSetsAt two) (sign_mu_pointed E hE d .fst P) (parity_quotient_bsigma_two E hE P ne)
  ≔ match d [
  | inl. ne' ↦ component_path SetTypes (Fin two, fin_set two) (parity_quotient_bsigma_two E hE P ne')
      (parity_quotient_bsigma_two E hE P ne) (refl (ParityQuotient E hE P, parity_quotient_set E hE P))
  | inr. no ↦ match no ne [] ]

def sign_mu_value_empty (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (no : Not (Mere E)) (d : Decidable (Mere E))
  : Id (BookFiniteSetsAt two) (sign_mu_pointed E hE d .fst P) (shape sign_sigma_two)
  ≔ match d [ inl. ne ↦ match no ne [] | inr. _ ↦ refl (shape sign_sigma_two) ]

{` n = 0, 1: there are no two-element subsets and Bsgn is constant. `}
def sign_fin_one_prop : isProp (Fin (suc. zero.))
  ≔ [ inl. e, _ ↦ match e [] | inr. u, inl. e ↦ match e [] | inr. u, inr. v ↦ inr. (unit_prop u v) ]

def two_subsets_of_prop_empty (A : Type) (hA : isProp A) (e : TwoSubsets A) : Empty
  ≔ let C ≔ SubtypeCarrier A (e .fst) in
    mere_rec (Id Type C (Fin two)) Empty empty_prop
      (p ↦ let t ≔ id_to_equiv C (Fin two) p in
        let c0 ≔ equiv_inverse_map C (Fin two) t (inr. star.) in
        let c1 ≔ equiv_inverse_map C (Fin two) t (inl. (inr. star.)) in
        let q : Id C c0 c1 ≔ subtype_equal A (x ↦ e .fst x .fst) (x ↦ e .fst x .snd) c0 c1 (hA (c0 .fst) (c1 .fst)) in
        fin_two_zero_ne_one
          (calc (inr. star. : Fin two) = t .map c0 by inverse (Fin two) (t .map c0) (inr. star.) (equiv_counit C (Fin two) t (inr. star.))
            = t .map c1 by refl (t .map) q
            = inl. (inr. star.) by equiv_counit C (Fin two) t (inl. (inr. star.)) ∎))
      (e .snd)

def fin_small_isprop (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.))) : isProp (Fin n)
  ≔ match hn [
  | inl. q ↦ transport Nat (k ↦ isProp (Fin k)) zero. n (inverse Nat n zero. q) empty_prop
  | inr. q ↦ transport Nat (k ↦ isProp (Fin k)) (suc. zero.) n (inverse Nat n (suc. zero.) q) sign_fin_one_prop ]

def bsigma_small_prop (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.))) (A : BookFiniteSetsAt n) : isProp (A .fst .fst)
  ≔ mere_rec (Id SetTypes (Fin n, fin_set n) (A .fst)) (isProp (A .fst .fst)) (isprop_isprop (A .fst .fst))
      (p ↦ transport Type isProp (Fin n) (A .fst .fst) (p .fst) (fin_small_isprop n hn))
      (A .snd)

def bsgn_small_constant (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.))) (A : BookFiniteSetsAt n)
  : Id (BookFiniteSetsAt two) (bsgn n A) (shape sign_sigma_two)
  ≔ sign_mu_value_empty (TwoSubsets (A .fst .fst)) (sign_subsets_finite n A) (sign_family n A)
      (mere_rec (TwoSubsets (A .fst .fst)) Empty empty_prop (two_subsets_of_prop_empty (A .fst .fst) (bsigma_small_prop n hn A)))
      (finite_inhabited_decidable (TwoSubsets (A .fst .fst)) (sign_subsets_finite n A))

{` n ≥ 2: E(A) is inhabited and Bsgn(A) is the set of sign orderings of A. `}
def sign_subsets_inhabited (m : Nat) (A : BookFiniteSetsAt (suc. (suc. m))) : Mere (TwoSubsets (A .fst .fst))
  ≔ trunc_map native_truncation (Id SetTypes (Fin (suc. (suc. m)), fin_set (suc. (suc. m))) (A .fst)) (TwoSubsets (A .fst .fst))
      (p ↦ transport Type TwoSubsets (Fin (suc. (suc. m))) (A .fst .fst) (p .fst) (two_subsets_fin_inhabited m)) (A .snd)

def bsgn_quotient (m : Nat) (A : BookFiniteSetsAt (suc. (suc. m))) : BookFiniteSetsAt two
  ≔ parity_quotient_bsigma_two (TwoSubsets (A .fst .fst)) (sign_subsets_finite (suc. (suc. m)) A)
      (sign_family (suc. (suc. m)) A) (sign_subsets_inhabited m A)

def bsgn_quotient_carrier (m : Nat) (A : BookFiniteSetsAt (suc. (suc. m)))
  : Id Type (bsgn_quotient m A .fst .fst) (SignOrderings (A .fst .fst) (A .fst .snd) (bsigma_finite (suc. (suc. m)) A))
  ≔ refl (bsgn_quotient m A .fst .fst)

def bsgn_quotient_path (m : Nat) (A : BookFiniteSetsAt (suc. (suc. m)))
  : Id (BookFiniteSetsAt two) (bsgn (suc. (suc. m)) A) (bsgn_quotient m A)
  ≔ sign_mu_value_ne (TwoSubsets (A .fst .fst)) (sign_subsets_finite (suc. (suc. m)) A) (sign_family (suc. (suc. m)) A)
      (sign_subsets_inhabited m A) (finite_inhabited_decidable (TwoSubsets (A .fst .fst)) (sign_subsets_finite (suc. (suc. m)) A))

{` Naturality of transport along a homotopy of maps into BΣ_2, and the
   resulting invariance of "swaps" for the images of a loop. `}
def bsigma_two_homotopy_natural (X : Type) (f g : X → BookFiniteSetsAt two) (H : (x : X) → Id (BookFiniteSetsAt two) (f x) (g x))
  (x y : X) (p : Id X x y) (u : f x .fst .fst)
  : Id (g y .fst .fst) (transport X (z ↦ g z .fst .fst) x y p (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (f x) (g x) (H x) u))
      (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (f y) (g y) (H y) (transport X (z ↦ f z .fst .fst) x y p u))
  ≔ let B2 ≔ BookFiniteSetsAt two in
    let tH : f x .fst .fst → g x .fst .fst ≔ transport B2 (T ↦ T .fst .fst) (f x) (g x) (H x) in
    J X x (y p ↦ Id (g y .fst .fst) (transport X (z ↦ g z .fst .fst) x y p (tH u))
        (transport B2 (T ↦ T .fst .fst) (f y) (g y) (H y) (transport X (z ↦ f z .fst .fst) x y p u)))
      (concat (g x .fst .fst) (transport X (z ↦ g z .fst .fst) x x (refl x) (tH u)) (tH u)
        (tH (transport X (z ↦ f z .fst .fst) x x (refl x) u))
        (transport_refl X (z ↦ g z .fst .fst) x (tH u))
        (inverse (g x .fst .fst) (tH (transport X (z ↦ f z .fst .fst) x x (refl x) u)) (tH u)
          (refl tH (transport_refl X (z ↦ f z .fst .fst) x u))))
      y p

def two_loop_moves_homotopy (X : Type) (f g : X → BookFiniteSetsAt two) (H : (x : X) → Id (BookFiniteSetsAt two) (f x) (g x))
  (x : X) (s : Id X x x)
  : Id Bool (two_loop_moves (g x) (refl g s)) (two_loop_moves (f x) (refl f s))
  ≔ two_moves_conjugate (f x .fst .fst) (g x .fst .fst) (two_set_two_element (f x)) (two_set_two_element (g x))
      (bsigma_two_transport (f x) (g x) (H x)) (bsigma_two_transport (f x) (f x) (refl f s))
      (bsigma_two_transport (g x) (g x) (refl g s))
      (u ↦ bsigma_two_homotopy_natural X f g H x x s u)

{` Local orderings over BΣ_n, and the computation of USym sgn. `}
def sign_local_orderings (n : Nat) (A : BookFiniteSetsAt n) : Type
  ≔ LocalSections (TwoSubsets (A .fst .fst)) (sign_family n A)

def sign_parity_relation (n : Nat) (A : BookFiniteSetsAt n) : EquivalenceRelation (sign_local_orderings n A)
  ≔ parity_relation (TwoSubsets (A .fst .fst)) (sign_subsets_finite n A) (sign_family n A)

def bsgn_quotient_moves (m : Nat) (s : USym (symmetric_group (suc. (suc. m))))
  : Id Bool (two_loop_moves (bsgn_quotient m (standard_shape (suc. (suc. m)))) (refl (bsgn_quotient m) s))
      (parity_odd (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m))))
        (transport (BookFiniteSetsAt (suc. (suc. m))) (sign_local_orderings (suc. (suc. m)))
          (standard_shape (suc. (suc. m))) (standard_shape (suc. (suc. m))) s (standard_local_ordering (suc. (suc. m))))
        (standard_local_ordering (suc. (suc. m))))
  ≔ let n : Nat ≔ suc. (suc. m) in
    let A0 ≔ standard_shape n in
    let E ≔ TwoSubsets (Fin n) in let hE ≔ sign_subsets_finite n A0 in
    let P ≔ two_subset_bsigma (Fin n) (fin_set n) in
    let Q ≔ ParityQuotient E hE P in
    let hQ ≔ two_set_two_element (bsgn_quotient m A0) in
    let w0 ≔ standard_local_ordering n in
    let w1 ≔ transport (BookFiniteSetsAt n) (sign_local_orderings n) A0 A0 s w0 in
    let z0 ≔ parity_class E hE P w0 in
    let tz ≔ bsigma_two_transport (bsgn_quotient m A0) (bsgn_quotient m A0) (refl (bsgn_quotient m) s) in
    calc two_loop_moves (bsgn_quotient m A0) (refl (bsgn_quotient m) s)
      = two_differ Q hQ z0 (tz .map z0) by two_moves_value Q hQ tz z0
      = two_differ Q hQ z0 (parity_class E hE P w1)
        by refl (two_differ Q hQ z0)
          (quotient_family_transport (BookFiniteSetsAt n) (sign_local_orderings n) (sign_parity_relation n) A0 A0 s w0)
      = parity_odd E hE P w1 w0 by parity_class_differ E hE P (sign_subsets_inhabited m A0) hQ w0 w1 ∎

{` For n ≥ 2, the sign of USym sgn(s) is the parity of the disagreement
   between the transported standard local ordering and the standard one. `}
def usgn_sign_parity (m : Nat) (s : USym (symmetric_group (suc. (suc. m))))
  : Id Sign (sigma_two_sign (usgn (suc. (suc. m)) s))
      (bool_sign (parity_odd (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m))))
        (transport (BookFiniteSetsAt (suc. (suc. m))) (sign_local_orderings (suc. (suc. m)))
          (standard_shape (suc. (suc. m))) (standard_shape (suc. (suc. m))) s (standard_local_ordering (suc. (suc. m))))
        (standard_local_ordering (suc. (suc. m)))))
  ≔ let n : Nat ≔ suc. (suc. m) in
    let A0 ≔ standard_shape n in
    calc sigma_two_sign (usgn n s)
      = two_loop_sign (bsgn n A0) (refl (bsgn n) s)
        by two_loop_sign_conjugate (shape sign_sigma_two) (bsgn n A0) (bsgn_point n) (refl (bsgn n) s)
      = bool_sign (two_loop_moves (bsgn_quotient m A0) (refl (bsgn_quotient m) s))
        by refl bool_sign (inverse Bool (two_loop_moves (bsgn_quotient m A0) (refl (bsgn_quotient m) s))
          (two_loop_moves (bsgn n A0) (refl (bsgn n) s))
          (two_loop_moves_homotopy (BookFiniteSetsAt n) (bsgn n) (bsgn_quotient m) (bsgn_quotient_path m) A0 s))
      = bool_sign (parity_odd (TwoSubsets (Fin n)) (sign_subsets_finite n A0) (two_subset_bsigma (Fin n) (fin_set n))
          (transport (BookFiniteSetsAt n) (sign_local_orderings n) A0 A0 s (standard_local_ordering n))
          (standard_local_ordering n))
        by refl bool_sign (bsgn_quotient_moves m s) ∎

{` The action of an equivalence on local orderings: (t·w)(e) = t(w(t⁻¹ e)). `}
def LocalOrderingType (X : Type) : Type ≔ (e : TwoSubsets X) → SubtypeCarrier X (e .fst)

def subtype_reindex_equiv (X Y : Type) (t : Equiv X Y) (P : Y → Type) (hP : (y : Y) → isProp (P y))
  : Equiv (Σ X (x ↦ P (t .map x))) (Σ Y P)
  ≔ let ti ≔ equiv_inverse_map X Y t in
    quasi_inverse_equiv (Σ X (x ↦ P (t .map x))) (Σ Y P)
      (u ↦ (t .map (u .fst), u .snd))
      (v ↦ (ti (v .fst), transport Y P (v .fst) (t .map (ti (v .fst)))
        (inverse Y (t .map (ti (v .fst))) (v .fst) (equiv_counit X Y t (v .fst))) (v .snd)))
      (u ↦ subtype_equal X (x ↦ P (t .map x)) (x ↦ hP (t .map x))
        (ti (t .map (u .fst)), transport Y P (t .map (u .fst)) (t .map (ti (t .map (u .fst))))
          (inverse Y (t .map (ti (t .map (u .fst)))) (t .map (u .fst)) (equiv_counit X Y t (t .map (u .fst)))) (u .snd))
        u (equiv_retraction X Y t (u .fst)))
      (v ↦ subtype_equal Y P hP
        (t .map (ti (v .fst)), transport Y P (v .fst) (t .map (ti (v .fst)))
          (inverse Y (t .map (ti (v .fst))) (v .fst) (equiv_counit X Y t (v .fst))) (v .snd))
        v (equiv_counit X Y t (v .fst)))

def subset_preimage (X Y : Type) (t : Equiv X Y) (e : TwoSubsets Y) : TwoSubsets X
  ≔ (x ↦ e .fst (t .map x),
      trunc_map native_truncation (Id Type (SubtypeCarrier Y (e .fst)) (Fin two))
        (Id Type (SubtypeCarrier X (x ↦ e .fst (t .map x))) (Fin two))
        (q ↦ concat Type (SubtypeCarrier X (x ↦ e .fst (t .map x))) (SubtypeCarrier Y (e .fst)) (Fin two)
          (ua (SubtypeCarrier X (x ↦ e .fst (t .map x))) (SubtypeCarrier Y (e .fst))
            (subtype_reindex_equiv X Y t (y ↦ e .fst y .fst) (y ↦ e .fst y .snd))) q)
        (e .snd))

def local_ordering_action (X Y : Type) (t : Equiv X Y) (w : LocalOrderingType X) : LocalOrderingType Y
  ≔ e ↦ (t .map (w (subset_preimage X Y t e) .fst), w (subset_preimage X Y t e) .snd)

def local_ordering_action_identity (X : Type) (w : LocalOrderingType X) (e : TwoSubsets X)
  : Id (SubtypeCarrier X (e .fst)) (local_ordering_action X X (identity_equiv X) w e) (w e)
  ≔ refl w ((refl (e .fst), mere_isprop (Id Type (SubtypeCarrier X (e .fst)) (Fin two))
      (subset_preimage X X (identity_equiv X) e .snd) (e .snd)) : Id (TwoSubsets X) (subset_preimage X X (identity_equiv X) e) e)

{` Transport of local orderings along an identification X = Y is the action of
   the corresponding equivalence. `}
def local_ordering_transport (X Y : Type) (p : Id Type X Y) (w : LocalOrderingType X) (e : TwoSubsets Y)
  : Id (SubtypeCarrier Y (e .fst)) (transport Type LocalOrderingType X Y p w e)
      (local_ordering_action X Y (id_to_equiv X Y p) w e)
  ≔ J Type X (Y p ↦ (e : TwoSubsets Y) → Id (SubtypeCarrier Y (e .fst)) (transport Type LocalOrderingType X Y p w e)
        (local_ordering_action X Y (id_to_equiv X Y p) w e))
      (e ↦ calc transport Type LocalOrderingType X X (refl X) w e
          = w e by refl ((v ↦ v e) : LocalOrderingType X → SubtypeCarrier X (e .fst)) (transport_refl Type LocalOrderingType X w)
        = local_ordering_action X X (identity_equiv X) w e
          by inverse (SubtypeCarrier X (e .fst)) (local_ordering_action X X (identity_equiv X) w e) (w e)
            (local_ordering_action_identity X w e)
        = local_ordering_action X X (id_to_equiv X X (refl X)) w e
          by refl ((t ↦ local_ordering_action X X t w e) : Equiv X X → SubtypeCarrier X (e .fst))
            (Jβ Type X (B _ ↦ Equiv X B) (identity_equiv X)) ∎)
      Y p e

{` The same over BΣ_n, by induction on the identification. `}
def local_ordering_transport_bsigma (n : Nat) (A B : BookFiniteSetsAt n) (p : Id (BookFiniteSetsAt n) A B)
  (w : sign_local_orderings n A) (e : TwoSubsets (B .fst .fst))
  : Id (SubtypeCarrier (B .fst .fst) (e .fst)) (transport (BookFiniteSetsAt n) (sign_local_orderings n) A B p w e)
      (local_ordering_action (A .fst .fst) (B .fst .fst) (id_to_equiv (A .fst .fst) (B .fst .fst) (p .fst .fst)) w e)
  ≔ J (BookFiniteSetsAt n) A
      (B p ↦ (e : TwoSubsets (B .fst .fst)) → Id (SubtypeCarrier (B .fst .fst) (e .fst))
        (transport (BookFiniteSetsAt n) (sign_local_orderings n) A B p w e)
        (local_ordering_action (A .fst .fst) (B .fst .fst) (id_to_equiv (A .fst .fst) (B .fst .fst) (p .fst .fst)) w e))
      (e ↦ calc transport (BookFiniteSetsAt n) (sign_local_orderings n) A A (refl A) w e
          = w e by refl ((v ↦ v e) : sign_local_orderings n A → SubtypeCarrier (A .fst .fst) (e .fst))
              (transport_refl (BookFiniteSetsAt n) (sign_local_orderings n) A w)
        = local_ordering_action (A .fst .fst) (A .fst .fst) (identity_equiv (A .fst .fst)) w e
          by inverse (SubtypeCarrier (A .fst .fst) (e .fst)) (local_ordering_action (A .fst .fst) (A .fst .fst) (identity_equiv (A .fst .fst)) w e) (w e)
            (local_ordering_action_identity (A .fst .fst) w e)
        = local_ordering_action (A .fst .fst) (A .fst .fst) (id_to_equiv (A .fst .fst) (A .fst .fst) (refl (A .fst .fst))) w e
          by refl ((t ↦ local_ordering_action (A .fst .fst) (A .fst .fst) t w e) : Equiv (A .fst .fst) (A .fst .fst) → SubtypeCarrier (A .fst .fst) (e .fst))
            (Jβ Type (A .fst .fst) (C _ ↦ Equiv (A .fst .fst) C) (identity_equiv (A .fst .fst))) ∎)
      B p e

{` For the loop of a permutation t of Fin n, transport of local orderings is
   the action of t. `}
def permutation_local_ordering_transport (n : Nat) (t : Equiv (Fin n) (Fin n)) (w : LocalOrderingType (Fin n)) (e : TwoSubsets (Fin n))
  : Id (SubtypeCarrier (Fin n) (e .fst))
      (transport (BookFiniteSetsAt n) (sign_local_orderings n) (standard_shape n) (standard_shape n)
        (permutation_symmetry (standard_set n) t) w e)
      (local_ordering_action (Fin n) (Fin n) t w e)
  ≔ concat (SubtypeCarrier (Fin n) (e .fst))
      (transport (BookFiniteSetsAt n) (sign_local_orderings n) (standard_shape n) (standard_shape n)
        (permutation_symmetry (standard_set n) t) w e)
      (local_ordering_action (Fin n) (Fin n) (id_to_equiv (Fin n) (Fin n) (ua (Fin n) (Fin n) t)) w e)
      (local_ordering_action (Fin n) (Fin n) t w e)
      (local_ordering_transport_bsigma n (standard_shape n) (standard_shape n) (permutation_symmetry (standard_set n) t) w e)
      (refl ((u ↦ local_ordering_action (Fin n) (Fin n) u w e) : Equiv (Fin n) (Fin n) → SubtypeCarrier (Fin n) (e .fst))
        (ua_beta (Fin n) (Fin n) t))

def parity_odd_homotopy (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f f' g : LocalSections E P)
  (h : (e : E) → Id (P e .fst .fst) (f e) (f' e))
  : Id Bool (parity_odd E hE P f g) (parity_odd E hE P f' g)
  ≔ refl ((k ↦ parity_odd E hE P k g) : LocalSections E P → Bool) (funext E (e ↦ P e .fst .fst) f f' h)

{` USym sgn of the loop of a permutation t of Fin n (n ≥ 2): the parity of
   the disagreement between t·ω0 and ω0, ω0 the standard local ordering. `}
def usgn_permutation_parity (m : Nat) (t : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m))))
  : Id Sign (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) t)))
      (bool_sign (parity_odd (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m))))
        (local_ordering_action (Fin (suc. (suc. m))) (Fin (suc. (suc. m))) t (standard_local_ordering (suc. (suc. m))))
        (standard_local_ordering (suc. (suc. m)))))
  ≔ let n : Nat ≔ suc. (suc. m) in
    let A0 ≔ standard_shape n in
    let s ≔ permutation_symmetry (standard_set n) t in
    concat Sign (sigma_two_sign (usgn n s))
      (bool_sign (parity_odd (TwoSubsets (Fin n)) (sign_subsets_finite n A0) (two_subset_bsigma (Fin n) (fin_set n))
        (transport (BookFiniteSetsAt n) (sign_local_orderings n) A0 A0 s (standard_local_ordering n)) (standard_local_ordering n)))
      (bool_sign (parity_odd (TwoSubsets (Fin n)) (sign_subsets_finite n A0) (two_subset_bsigma (Fin n) (fin_set n))
        (local_ordering_action (Fin n) (Fin n) t (standard_local_ordering n)) (standard_local_ordering n)))
      (usgn_sign_parity m s)
      (refl bool_sign (parity_odd_homotopy (TwoSubsets (Fin n)) (sign_subsets_finite n A0) (two_subset_bsigma (Fin n) (fin_set n))
        (transport (BookFiniteSetsAt n) (sign_local_orderings n) A0 A0 s (standard_local_ordering n))
        (local_ordering_action (Fin n) (Fin n) t (standard_local_ordering n)) (standard_local_ordering n)
        (permutation_local_ordering_transport n t (standard_local_ordering n))))
