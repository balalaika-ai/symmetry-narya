export "505-gset-core-litmus"
export "65-cycle-paths"

{` Chapter 5 (actions.tex): the mkgroup(S¹ ∨ S¹)-set X of fig:not-normal and
   fig:not-normal-graph (xca:not-normal) and the choice map of
   xca:lagrange-if-subgr-not-normal.

   The pinned Narya has no higher inductive types. As for the circle
   (CircleSignature, module 05), S¹ ∨ S¹ is a PARAMETER: a signature with a
   base point, two loops and the dependent induction principle whose
   computation law is one identification of boundary data. (Its fields
   coincide with FigureEightSignature of module 483, which is not
   imported, so that this module does not depend on modules 470–482.) Connectedness follows from induction;
   that S¹ ∨ S¹ is a groupoid (so that mkgroup(S¹ ∨ S¹) is a group, the free
   group on two generators) is NOT proved here and enters as an explicit
   hypothesis hW : isGroupoid. The contractibility argument for X = X itself
   only uses connectedness.

   X is built by recursion: base ↦ Fin 3, loop₁ ↦ the cyclic successor s
   (0 ↦ 1 ↦ 2 ↦ 0), loop₂ ↦ the transposition t = (0 1), as in
   xca:lagrange-if-subgr-not-normal. In fig:not-normal-graph (nodes
   n1, n2, n3 at 0°, 120°, 240°; blue a: n1 → n2 → n3 → n1, red b fixing n1
   and swapping n2, n3) this is the relabelling n1 ↦ 2, n2 ↦ 0, n3 ↦ 1, so
   the marked point x = n2 is 0. Since recursion computes only typally,
   X(base) is identified with Fin 3 by the equivalence E of the
   computation law (wedge_identify), under which the two monodromies are s
   and t. `}

def CircleWedgeBoundary (W : Type) (base : W) (l1 l2 : Id W base base) (P : W → Type) : Type
  ≔ Σ (P base) (b ↦ Product (Id P l1 b b) (Id P l2 b b))

def circle_wedge_evaluate (W : Type) (base : W) (l1 l2 : Id W base base) (P : W → Type) (f : (x : W) → P x)
  : CircleWedgeBoundary W base l1 l2 P
  ≔ (f base, (refl f l1, refl f l2))

def CircleWedgeSignature : Type ≔ sig (
  carrier : Type,
  base : carrier,
  loop1 : Id carrier base base,
  loop2 : Id carrier base base,
  induction : (P : carrier → Type) (d : CircleWedgeBoundary carrier base loop1 loop2 P)
    → Σ ((x : carrier) → P x)
        (f ↦ Id (CircleWedgeBoundary carrier base loop1 loop2 P) (circle_wedge_evaluate carrier base loop1 loop2 P f) d))

def circle_wedge_ind_prop (W : CircleWedgeSignature) (P : W .carrier → Type)
  (hP : (x : W .carrier) → isProp (P x)) (b : P (W .base)) : (x : W .carrier) → P x
  ≔ W .induction P
      (b, (pathover_of_eq (W .carrier) P (W .base) (W .base) (W .loop1) b b
             (hP (W .base) (transport (W .carrier) P (W .base) (W .base) (W .loop1) b) b),
           pathover_of_eq (W .carrier) P (W .base) (W .base) (W .loop2) b b
             (hP (W .base) (transport (W .carrier) P (W .base) (W .base) (W .loop2) b) b))) .fst

def circle_wedge_connected (W : CircleWedgeSignature) : Connected (W .carrier)
  ≔ let A ≔ W .carrier in
    let reach : (x : A) → Mere (Id A (W .base) x)
      ≔ circle_wedge_ind_prop W (x ↦ Mere (Id A (W .base) x)) (x ↦ mere_isprop (Id A (W .base) x))
          (mere (Id A (W .base) (W .base)) (refl (W .base))) in
    (mere A (W .base), x y ↦ merely_paths_compose native_truncation A (W .base) x y (reach x) (reach y))

{` G ≔ mkgroup(S¹ ∨ S¹), under the hypothesis that S¹ ∨ S¹ is a groupoid. `}
def circle_wedge_group (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) : Group
  ≔ mkgroup (W .carrier, W .base, circle_wedge_connected W, hW)

{` The cyclic successor s of Fin 3 (0 ↦ 1 ↦ 2 ↦ 0). `}
def wedge_cycle_map : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. e)) ↦ match e [] ]

def wedge_cycle_inverse_map : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inl. (inr. u))
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def wedge_cycle_retraction (x : Fin three) : Id (Fin three) (wedge_cycle_inverse_map (wedge_cycle_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def wedge_cycle_section (x : Fin three) : Id (Fin three) (wedge_cycle_map (wedge_cycle_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def wedge_cycle_equiv : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) wedge_cycle_map wedge_cycle_inverse_map
      wedge_cycle_retraction wedge_cycle_section

{` The data (Fin 3, s, t) of the recursion. `}
def wedge_gset_data : Σ SetTypes (b ↦ Product (Id SetTypes b b) (Id SetTypes b b))
  ≔ (standard_set three,
     (set_types_path (standard_set three) (standard_set three) wedge_cycle_equiv,
      set_types_path (standard_set three) (standard_set three) fin3_swap01_equiv))

def wedge_family (W : CircleWedgeSignature) : W .carrier → SetTypes
  ≔ W .induction (_ ↦ SetTypes) wedge_gset_data .fst

def wedge_family_beta (W : CircleWedgeSignature)
  : Id (Σ SetTypes (b ↦ Product (Id SetTypes b b) (Id SetTypes b b)))
      (wedge_family W (W .base), (refl (wedge_family W) (W .loop1), refl (wedge_family W) (W .loop2)))
      wedge_gset_data
  ≔ W .induction (_ ↦ SetTypes) wedge_gset_data .snd

{` E : X(base) ≃ Fin 3, transport along the base computation. `}
def wedge_identify (W : CircleWedgeSignature) : Equiv (wedge_family W (W .base) .fst) (Fin three)
  ≔ set_paths_transport_equiv (wedge_family W (W .base)) (standard_set three) .map (wedge_family_beta W .fst)

def wedge_monodromy (W : CircleWedgeSignature) (l : Id (W .carrier) (W .base) (W .base))
  (x : wedge_family W (W .base) .fst) : wedge_family W (W .base) .fst
  ≔ transport (W .carrier) (z ↦ wedge_family W z .fst) (W .base) (W .base) l x

{` Under E the monodromy of loop₁ is s and that of loop₂ is t. `}
def wedge_monodromy1 (W : CircleWedgeSignature) (x : wedge_family W (W .base) .fst)
  : Id (Fin three) (wedge_identify W .map (wedge_monodromy W (W .loop1) x)) (wedge_cycle_map (wedge_identify W .map x))
  ≔ automorphism_pathover_commutes (wedge_family W (W .base)) (standard_set three) (wedge_family_beta W .fst)
      (set_paths_transport_equiv (wedge_family W (W .base)) (wedge_family W (W .base)) .map (refl (wedge_family W) (W .loop1)))
      (set_paths_transport_equiv (standard_set three) (standard_set three) .map
        (set_types_path (standard_set three) (standard_set three) wedge_cycle_equiv))
      .map (refl ((b l ↦ set_paths_transport_equiv b b .map l) : (b : SetTypes) → Id SetTypes b b → SetAutomorphisms b)
              (wedge_family_beta W .fst) (wedge_family_beta W .snd .fst))
      x

def wedge_monodromy2 (W : CircleWedgeSignature) (x : wedge_family W (W .base) .fst)
  : Id (Fin three) (wedge_identify W .map (wedge_monodromy W (W .loop2) x)) (fin3_swap01 (wedge_identify W .map x))
  ≔ automorphism_pathover_commutes (wedge_family W (W .base)) (standard_set three) (wedge_family_beta W .fst)
      (set_paths_transport_equiv (wedge_family W (W .base)) (wedge_family W (W .base)) .map (refl (wedge_family W) (W .loop2)))
      (set_paths_transport_equiv (standard_set three) (standard_set three) .map
        (set_types_path (standard_set three) (standard_set three) fin3_swap01_equiv))
      .map (refl ((b l ↦ set_paths_transport_equiv b b .map l) : (b : SetTypes) → Id SetTypes b b → SetAutomorphisms b)
              (wedge_family_beta W .fst) (wedge_family_beta W .snd .snd))
      x

{` Disjointness of the elements of Fin 3. `}
def wedge_fin3_zero_code : Fin three → Type ≔ [ inr. _ ↦ Unit | inl. _ ↦ Empty ]

def wedge_fin3_one_code : Fin three → Type ≔ [ inr. _ ↦ Empty | inl. (inr. _) ↦ Unit | inl. (inl. _) ↦ Empty ]

{` The only fixed point of t = (0 1) is 2. `}
def wedge_swap_fixed_two (y : Fin three) : Id (Fin three) (fin3_swap01 y) y → Id (Fin three) y fin3_two
  ≔ match y [
  | inr. star. ↦ h ↦ absurd (Id (Fin three) fin3_zero fin3_two)
      (transport (Fin three) wedge_fin3_zero_code fin3_zero fin3_one (inverse (Fin three) fin3_one fin3_zero h) star.)
  | inl. (inr. star.) ↦ h ↦ absurd (Id (Fin three) fin3_one fin3_two)
      (transport (Fin three) wedge_fin3_zero_code fin3_zero fin3_one h star.)
  | inl. (inl. (inr. star.)) ↦ _ ↦ refl fin3_two
  | inl. (inl. (inl. e)) ↦ match e [] ]

{` s has no fixed point. `}
def wedge_cycle_no_fixed (y : Fin three) : Id (Fin three) (wedge_cycle_map y) y → Empty
  ≔ match y [
  | inr. star. ↦ h ↦ transport (Fin three) wedge_fin3_zero_code fin3_zero fin3_one (inverse (Fin three) fin3_one fin3_zero h) star.
  | inl. (inr. star.) ↦ h ↦ transport (Fin three) wedge_fin3_one_code fin3_one fin3_two (inverse (Fin three) fin3_two fin3_one h) star.
  | inl. (inl. (inr. star.)) ↦ h ↦ transport (Fin three) wedge_fin3_zero_code fin3_zero fin3_two h star.
  | inl. (inl. (inl. e)) ↦ match e [] ]

{` A self-map of Fin 3 commuting with s and t is the identity. `}
def wedge_fin3_rigid (ψ : Fin three → Fin three)
  (hs : (k : Fin three) → Id (Fin three) (ψ (wedge_cycle_map k)) (wedge_cycle_map (ψ k)))
  (ht : (k : Fin three) → Id (Fin three) (ψ (fin3_swap01 k)) (fin3_swap01 (ψ k)))
  : (k : Fin three) → Id (Fin three) (ψ k) k
  ≔ let p2 : Id (Fin three) (ψ fin3_two) fin3_two
      ≔ wedge_swap_fixed_two (ψ fin3_two) (inverse (Fin three) (ψ fin3_two) (fin3_swap01 (ψ fin3_two)) (ht fin3_two)) in
    let p0 : Id (Fin three) (ψ fin3_zero) fin3_zero
      ≔ concat (Fin three) (ψ fin3_zero) (wedge_cycle_map (ψ fin3_two)) fin3_zero (hs fin3_two) (refl wedge_cycle_map p2) in
    let p1 : Id (Fin three) (ψ fin3_one) fin3_one
      ≔ concat (Fin three) (ψ fin3_one) (wedge_cycle_map (ψ fin3_zero)) fin3_one (hs fin3_zero) (refl wedge_cycle_map p0) in
    k ↦ match k [
    | inr. star. ↦ p0
    | inl. (inr. star.) ↦ p1
    | inl. (inl. (inr. star.)) ↦ p2
    | inl. (inl. (inl. e)) ↦ match e [] ]

{` Transfer along E: a self-map φ of a type S ≃ Fin 3 commuting with maps
   corresponding to s and t is the identity. `}
def wedge_conjugate_commutes (S : Type) (E : Equiv S (Fin three)) (T φ : S → S) (σ : Fin three → Fin three)
  (c : (x : S) → Id (Fin three) (E .map (T x)) (σ (E .map x)))
  (n : (x : S) → Id S (φ (T x)) (T (φ x))) (k : Fin three)
  : Id (Fin three) (E .map (φ (equiv_inverse_map S (Fin three) E (σ k))))
      (σ (E .map (φ (equiv_inverse_map S (Fin three) E k))))
  ≔ let Ei ≔ equiv_inverse_map S (Fin three) E in
    let y ≔ Ei k in
    let q : Id S (Ei (σ k)) (T y)
      ≔ concat S (Ei (σ k)) (Ei (E .map (T y))) (T y)
          (refl Ei (inverse (Fin three) (E .map (T y)) (σ k)
            (concat (Fin three) (E .map (T y)) (σ (E .map y)) (σ k) (c y) (refl σ (equiv_counit S (Fin three) E k)))))
          (equiv_retraction S (Fin three) E (T y)) in
    calc
      E .map (φ (Ei (σ k)))
      = E .map (φ (T y)) by refl ((u ↦ E .map (φ u)) : S → Fin three) q
      = E .map (T (φ y)) by refl (E .map) (n y)
      = σ (E .map (φ y)) by c (φ y) ∎

def wedge_rigid_transfer (S : Type) (E : Equiv S (Fin three)) (T1 T2 φ : S → S)
  (c1 : (x : S) → Id (Fin three) (E .map (T1 x)) (wedge_cycle_map (E .map x)))
  (c2 : (x : S) → Id (Fin three) (E .map (T2 x)) (fin3_swap01 (E .map x)))
  (n1 : (x : S) → Id S (φ (T1 x)) (T1 (φ x)))
  (n2 : (x : S) → Id S (φ (T2 x)) (T2 (φ x)))
  (x : S) : Id S (φ x) x
  ≔ let Ei ≔ equiv_inverse_map S (Fin three) E in
    let ψ : Fin three → Fin three ≔ k ↦ E .map (φ (Ei k)) in
    let r ≔ wedge_fin3_rigid ψ (wedge_conjugate_commutes S E T1 φ wedge_cycle_map c1 n1)
      (wedge_conjugate_commutes S E T2 φ fin3_swap01 c2 n2) in
    equivalence_injective S (Fin three) E (φ x) x
      (concat (Fin three) (E .map (φ x)) (ψ (E .map x)) (E .map x)
        (refl ((u ↦ E .map (φ u)) : S → Fin three)
          (inverse S (Ei (E .map x)) x (equiv_retraction S (Fin three) E x)))
        (r (E .map x)))

{` The G-set X of fig:not-normal. `}
def wedge_gset (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) : GSet (circle_wedge_group W hW)
  ≔ wedge_family W

{` xca:not-normal: every symmetry e : X = X acts as the identity on every
   X(z) (it commutes with both monodromies at base, by rem:map-of-Gsets). `}
def wedge_gset_symmetry_trivial (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier))
  (e : Id (GSet (circle_wedge_group W hW)) (wedge_gset W hW) (wedge_gset W hW))
  (z : W .carrier) (x : wedge_family W z .fst)
  : Id (wedge_family W z .fst) (gset_path_transport (circle_wedge_group W hW) (wedge_gset W hW) (wedge_gset W hW) e z x) x
  ≔ let G ≔ circle_wedge_group W hW in
    let X ≔ wedge_gset W hW in
    let f ≔ gset_path_to_hom G X X e in
    let b ≔ W .base in
    connected_based_elim native_truncation (W .carrier) (circle_wedge_connected W) b
      (w ↦ (y : wedge_family W w .fst) → Id (wedge_family W w .fst) (f w y) y)
      (w ↦ pi_prop (wedge_family W w .fst) (y ↦ Id (wedge_family W w .fst) (f w y) y)
        (y ↦ wedge_family W w .snd (f w y) y))
      (wedge_rigid_transfer (wedge_family W b .fst) (wedge_identify W)
        (wedge_monodromy W (W .loop1)) (wedge_monodromy W (W .loop2)) (f b)
        (wedge_monodromy1 W) (wedge_monodromy2 W)
        (gset_hom_natural G X X f b b (W .loop1)) (gset_hom_natural G X X f b b (W .loop2)))
      z x

{` xca:not-normal: X = X is contractible (center refl). `}
def wedge_gset_symmetries_contractible (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier))
  : BookIsContr (Id (GSet (circle_wedge_group W hW)) (wedge_gset W hW) (wedge_gset W hW))
  ≔ let G ≔ circle_wedge_group W hW in
    let X ≔ wedge_gset W hW in
    (refl X, e ↦ gset_path_to_hom_reflects G X X (refl X) e
      (gset_hom_ext G X X (gset_path_to_hom G X X (refl X)) (gset_path_to_hom G X X e)
        (z x ↦ concat (wedge_family W z .fst) (gset_path_transport G X X (refl X) z x) x (gset_path_transport G X X e z x)
          (transport_refl (GSet G) (V ↦ V z .fst) X x)
          (inverse (wedge_family W z .fst) (gset_path_transport G X X e z x) x (wedge_gset_symmetry_trivial W hW e z x)))))

{` xca:lagrange-if-subgr-not-normal: the choice map. Index the points of
   X(sh) by k : Fin 3 via E (X(sh) is Fin 3 only up to E): for k = 0 take
   e, for k = 1 take loop₁ · loop₁ (s(s(1)) = 0), for k = 2 take loop₁
   (s(2) = 0). `}
def wedge_gset_point (W : CircleWedgeSignature) (k : Fin three) : wedge_family W (W .base) .fst
  ≔ equiv_inverse_map (wedge_family W (W .base) .fst) (Fin three) (wedge_identify W) k

def wedge_gset_point_by_index (W : CircleWedgeSignature) (y : wedge_family W (W .base) .fst) (k : Fin three)
  (h : Id (Fin three) (wedge_identify W .map y) k) : Id (wedge_family W (W .base) .fst) y (wedge_gset_point W k)
  ≔ equivalence_injective (wedge_family W (W .base) .fst) (Fin three) (wedge_identify W) y (wedge_gset_point W k)
      (concat (Fin three) (wedge_identify W .map y) k (wedge_identify W .map (wedge_gset_point W k)) h
        (inverse (Fin three) (wedge_identify W .map (wedge_gset_point W k)) k
          (equiv_counit (wedge_family W (W .base) .fst) (Fin three) (wedge_identify W) k)))

def wedge_monodromy1_point (W : CircleWedgeSignature) (k : Fin three)
  : Id (Fin three) (wedge_identify W .map (wedge_monodromy W (W .loop1) (wedge_gset_point W k))) (wedge_cycle_map k)
  ≔ concat (Fin three) (wedge_identify W .map (wedge_monodromy W (W .loop1) (wedge_gset_point W k)))
      (wedge_cycle_map (wedge_identify W .map (wedge_gset_point W k))) (wedge_cycle_map k)
      (wedge_monodromy1 W (wedge_gset_point W k))
      (refl wedge_cycle_map (equiv_counit (wedge_family W (W .base) .fst) (Fin three) (wedge_identify W) k))

def WedgeChoice (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) (y : wedge_family W (W .base) .fst) : Type
  ≔ Σ (USym (circle_wedge_group W hW))
      (g ↦ Id (wedge_family W (W .base) .fst) (gset_usym_act (circle_wedge_group W hW) (wedge_gset W hW) g y) (wedge_gset_point W fin3_zero))

def wedge_choice_index (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) (k : Fin three)
  : WedgeChoice W hW (wedge_gset_point W k)
  ≔ let G ≔ circle_wedge_group W hW in
    let X ≔ wedge_gset W hW in
    let S ≔ wedge_family W (W .base) .fst in
    let l1 ≔ W .loop1 in
    let T ≔ wedge_monodromy W l1 in
    match k [
    | inr. star. ↦ (usym_unit G, gset_act_unit G X (wedge_gset_point W fin3_zero))
    | inl. (inr. star.) ↦ (usym_mul G l1 l1,
        concat S (gset_usym_act G X (usym_mul G l1 l1) (wedge_gset_point W fin3_one)) (T (T (wedge_gset_point W fin3_one)))
          (wedge_gset_point W fin3_zero)
          (gset_act_mul G X l1 l1 (wedge_gset_point W fin3_one))
          (wedge_gset_point_by_index W (T (T (wedge_gset_point W fin3_one))) fin3_zero
            (concat (Fin three) (wedge_identify W .map (T (T (wedge_gset_point W fin3_one))))
              (wedge_cycle_map (wedge_identify W .map (T (wedge_gset_point W fin3_one)))) fin3_zero
              (wedge_monodromy1 W (T (wedge_gset_point W fin3_one)))
              (refl wedge_cycle_map (wedge_monodromy1_point W fin3_one)))))
    | inl. (inl. (inr. star.)) ↦ (l1,
        wedge_gset_point_by_index W (T (wedge_gset_point W fin3_two)) fin3_zero (wedge_monodromy1_point W fin3_two))
    | inl. (inl. (inl. e)) ↦ match e [] ]

{` The book's f : Π_{x : X(sh)} Σ_{g : USym G} (g · x = 0), with 0 ≔ E⁻¹(0). `}
def wedge_choice_map (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) (y : wedge_family W (W .base) .fst)
  : WedgeChoice W hW y
  ≔ transport (wedge_family W (W .base) .fst) (WedgeChoice W hW) (wedge_gset_point W (wedge_identify W .map y)) y
      (equiv_retraction (wedge_family W (W .base) .fst) (Fin three) (wedge_identify W) y)
      (wedge_choice_index W hW (wedge_identify W .map y))

{` X is transitive (from the choice map), so (X, 0) is a subgroup. `}
def wedge_gset_transitive (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier))
  : IsTransitive (circle_wedge_group W hW) (wedge_gset W hW)
  ≔ let G ≔ circle_wedge_group W hW in
    let X ≔ wedge_gset W hW in
    let S ≔ wedge_family W (W .base) .fst in
    let x0 ≔ wedge_gset_point W fin3_zero in
    mere (Σ S (x ↦ (y : S) → Mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y)))))
      (x0, y ↦ mere (Σ (USym G) (g ↦ Id S x0 (gset_usym_act G X g y)))
        (wedge_choice_map W hW y .fst,
         inverse S (gset_usym_act G X (wedge_choice_map W hW y .fst) y) x0 (wedge_choice_map W hW y .snd)))

def wedge_subgroup (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) : Subgroups (circle_wedge_group W hW)
  ≔ (wedge_gset W hW, wedge_gset_point W fin3_zero, wedge_gset_transitive W hW)

{` xca:not-normal, conclusion: ev_x : (X = X) → X(sh) is injective
   (lem:evisinjwhentransitive) but not surjective, for every x : X(sh)
   (in the figure x = n2 = 0); in particular X is not normal. `}
def wedge_eval_injective (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) (x : wedge_family W (W .base) .fst)
  : IsEmbedding (Id (GSet (circle_wedge_group W hW)) (wedge_gset W hW) (wedge_gset W hW)) (wedge_family W (W .base) .fst)
      (gset_path_eval (circle_wedge_group W hW) (wedge_gset W hW) (wedge_gset W hW) (W .base) x)
  ≔ gset_path_eval_injective (circle_wedge_group W hW) (wedge_gset W hW) (wedge_gset W hW) (W .base) x
      (wedge_gset_transitive W hW)

def wedge_eval_not_surjective (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) (x : wedge_family W (W .base) .fst)
  (h : Surjective (Id (GSet (circle_wedge_group W hW)) (wedge_gset W hW) (wedge_gset W hW)) (wedge_family W (W .base) .fst)
        (gset_path_eval (circle_wedge_group W hW) (wedge_gset W hW) (wedge_gset W hW) (W .base) x))
  : Empty
  ≔ let G ≔ circle_wedge_group W hW in
    let X ≔ wedge_gset W hW in
    let P ≔ Id (GSet G) X X in
    let S ≔ wedge_family W (W .base) .fst in
    let E ≔ wedge_identify W in
    let y ≔ wedge_monodromy W (W .loop1) x in
    mere_rec (BookFiber P S (gset_path_eval G X X (W .base) x) y) Empty empty_prop
      (u ↦ wedge_cycle_no_fixed (E .map x)
        (concat (Fin three) (wedge_cycle_map (E .map x)) (E .map y) (E .map x)
          (inverse (Fin three) (E .map y) (wedge_cycle_map (E .map x)) (wedge_monodromy1 W x))
          (refl (E .map)
            (concat S y (gset_path_eval G X X (W .base) x (u .fst)) x (u .snd)
              (wedge_gset_symmetry_trivial W hW (u .fst) (W .base) x)))))
      (h y)

def wedge_gset_not_normal (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier))
  (h : IsNormalGSet (circle_wedge_group W hW) (wedge_gset W hW)) : Empty
  ≔ let G ≔ circle_wedge_group W hW in
    let X ≔ wedge_gset W hW in
    let x ≔ wedge_gset_point W fin3_zero in
    wedge_eval_not_surjective W hW x
      (y ↦ mere (BookFiber (Id (GSet G) X X) (wedge_family W (W .base) .fst) (gset_path_eval G X X (W .base) x) y)
        (h (W .base) x y .center))

{` "The action in fig:not-normal corresponds to the bicycle of
   fig:abnormal-bicycle" (a = s, b = (1 2), module 477): s itself is an
   isomorphism (Fin 3, s, (0 1)) ≅ (Fin 3, s, (1 2)) of sets with two
   permutations: it commutes with s and carries (0 1) to (1 2). `}
def wedge_bicycle_relabel (k : Fin three)
  : Id (Fin three) (wedge_cycle_map (fin3_swap01 k)) (fin3_swap12 (wedge_cycle_map k))
  ≔ match k [
  | inr. u ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inr. u : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]
