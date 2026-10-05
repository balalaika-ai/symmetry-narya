export "414-trivial-and-permutation-groups"

{` Chapter 4, ex:cyclicgroups (group.tex 522-566). `}

{` Every symmetry of a cycle is an integer power of its generating loop
   (s, !) (cycle_generating_loop, module 130), since loops of cycles are
   determined by the image of one point (cycle_automorphisms_evaluation). `}
def cyclic_loop_power_nat_eval (c : Cycles) (l : Id Cycles c c) (m : Nat) (y : c .fst .fst .fst)
  : Id (c .fst .fst .fst) (cycle_path_evaluate c c (loop_power_nat Cycles c l m) y)
      (iterate (c .fst .fst .fst) (u ↦ cycle_path_evaluate c c l u) m y)
  ≔ match m [
  | zero. ↦ transport_refl Type (X ↦ X) (c .fst .fst .fst) y
  | suc. m ↦ concat (c .fst .fst .fst)
      (cycle_path_evaluate c c (concat Cycles c c c (loop_power_nat Cycles c l m) l) y)
      (cycle_path_evaluate c c l (cycle_path_evaluate c c (loop_power_nat Cycles c l m) y))
      (cycle_path_evaluate c c l (iterate (c .fst .fst .fst) (u ↦ cycle_path_evaluate c c l u) m y))
      (carrier_path_evaluate_concat Cycles (d ↦ d .fst .fst .fst) c c c (loop_power_nat Cycles c l m) l y)
      (refl (u ↦ cycle_path_evaluate c c l u) (cyclic_loop_power_nat_eval c l m y)) ]

def cyclic_inverse_generator_eval (c : Cycles) (y : c .fst .fst .fst)
  : Id (c .fst .fst .fst)
      (cycle_path_evaluate c c (inverse Cycles c c (cycle_generating_loop c)) y)
      (equiv_inverse_map (c .fst .fst .fst) (c .fst .fst .fst) (c .fst .snd) y)
  ≔ let X ≔ c .fst .fst .fst in let e ≔ c .fst .snd in
    let g ≔ cycle_generating_loop c in
    let back ≔ ((u ↦ cycle_path_evaluate c c (inverse Cycles c c g) u) : X → X) in
    let y' ≔ equiv_inverse_map X X e y in
    calc
      back y = back (cycle_path_evaluate c c g y')
        by refl back (inverse X (cycle_path_evaluate c c g y') y
          (concat X (cycle_path_evaluate c c g y') (e .map y') y (cycle_generating_loop_action c y')
            (equiv_counit X X e y)))
      = y' by transport_inverse_roundtrip Cycles (d ↦ d .fst .fst .fst) c c g y' ∎

def iterate_commuting_map (A : Type) (f k : A → A) (comm : (x : A) → Id A (k (f x)) (f (k x))) (n : Nat) (x : A)
  : Id A (k (iterate A f n x)) (iterate A f n (k x))
  ≔ match n [
  | zero. ↦ refl (k x)
  | suc. n ↦ concat A (k (f (iterate A f n x))) (f (k (iterate A f n x))) (f (iterate A f n (k x)))
      (comm (iterate A f n x)) (refl f (iterate_commuting_map A f k comm n x)) ]

def cycle_generator_power_eval (c : Cycles) (z : Int) (x : c .fst .fst .fst)
  : Id (c .fst .fst .fst)
      (cycle_path_evaluate c c (loop_power Cycles c (cycle_generating_loop c) z) x)
      (permutation_power (c .fst .fst .fst) (c .fst .snd) z x)
  ≔ match z [
    | pos. n ↦ concat (c .fst .fst .fst) (cycle_path_evaluate c c (loop_power_nat Cycles c (cycle_generating_loop c) n) x)
        (iterate (c .fst .fst .fst) (u ↦ cycle_path_evaluate c c (cycle_generating_loop c) u) n x)
        (iterate (c .fst .fst .fst) (c .fst .snd .map) n x)
        (cyclic_loop_power_nat_eval c (cycle_generating_loop c) n x)
        (iterate_pointwise (c .fst .fst .fst) (u ↦ cycle_path_evaluate c c (cycle_generating_loop c) u)
          (c .fst .snd .map) (cycle_generating_loop_action c) n x)
    | neg. n ↦ concat (c .fst .fst .fst)
        (cycle_path_evaluate c c (loop_power_nat Cycles c (inverse Cycles c c (cycle_generating_loop c)) (suc. n)) x)
        (iterate (c .fst .fst .fst) (u ↦ cycle_path_evaluate c c (inverse Cycles c c (cycle_generating_loop c)) u) (suc. n) x)
        (iterate (c .fst .fst .fst) (equiv_inverse_map (c .fst .fst .fst) (c .fst .fst .fst) (c .fst .snd)) (suc. n) x)
        (cyclic_loop_power_nat_eval c (inverse Cycles c c (cycle_generating_loop c)) (suc. n) x)
        (iterate_pointwise (c .fst .fst .fst) (u ↦ cycle_path_evaluate c c (inverse Cycles c c (cycle_generating_loop c)) u)
          (equiv_inverse_map (c .fst .fst .fst) (c .fst .fst .fst) (c .fst .snd)) (cyclic_inverse_generator_eval c) (suc. n) x) ]

def cycle_loops_are_powers (c : Cycles) (p : Id Cycles c c)
  : Mere (Σ Int (z ↦ Id (Id Cycles c c) (loop_power Cycles c (cycle_generating_loop c) z) p))
  ≔ let X ≔ c .fst .fst .fst in let s ≔ c .fst .snd in
    let T ≔ Σ Int (z ↦ Id (Id Cycles c c) (loop_power Cycles c (cycle_generating_loop c) z) p) in
    mere_rec X (Mere T) (mere_isprop T)
      (x0 ↦ mere_rec (OrbitWitness X s x0 (cycle_path_evaluate c c p x0)) (Mere T) (mere_isprop T)
        (w ↦ mere T (w .fst,
          equivalence_injective (Id Cycles c c) X
            (native_equivalence (Id Cycles c c) X (cycle_automorphisms_evaluation c x0))
            (loop_power Cycles c (cycle_generating_loop c) (w .fst)) p
            (concat X (cycle_path_evaluate c c (loop_power Cycles c (cycle_generating_loop c) (w .fst)) x0)
              (permutation_power X s (w .fst) x0) (cycle_path_evaluate c c p x0)
              (cycle_generator_power_eval c (w .fst) x0)
              (inverse X (cycle_path_evaluate c c p x0) (permutation_power X s (w .fst) x0) (w .snd)))))
        (c .snd .snd x0 (cycle_path_evaluate c c p x0)))
      (c .snd .fst)

{` The generating symmetry of Aut_Cyc(c), and: every symmetry of Aut_Cyc(c)
   is merely a power of it ("all symmetries are obtained from 1"). `}
def cycle_group_generator (c : Cycles) : USym (automorphism_group Cycles cycles_groupoid c)
  ≔ component_path Cycles c (component_point Cycles c) (component_point Cycles c) (cycle_generating_loop c)

def cycle_group_power (c : Cycles) (z : Int) : USym (automorphism_group Cycles cycles_groupoid c)
  ≔ loop_power (NativeComponent Cycles c) (component_point Cycles c) (cycle_group_generator c) z

def cycle_group_symmetries_are_powers (c : Cycles) (g : USym (automorphism_group Cycles cycles_groupoid c))
  : Mere (Σ Int (z ↦ Id (USym (automorphism_group Cycles cycles_groupoid c)) (cycle_group_power c z) g))
  ≔ let G ≔ automorphism_group Cycles cycles_groupoid c in
    let T ≔ Σ Int (z ↦ Id (USym G) (cycle_group_power c z) g) in
    mere_rec (Σ Int (z ↦ Id (Id Cycles c c) (loop_power Cycles c (cycle_generating_loop c) z) (g .fst)))
      (Mere T) (mere_isprop T)
      (w ↦ mere T (w .fst,
        equivalence_injective (USym G) (Id Cycles c c) (automorphism_group_usym_equiv Cycles cycles_groupoid c)
          (cycle_group_power c (w .fst)) g
          (concat (Id Cycles c c) (cycle_group_power c (w .fst) .fst)
            (loop_power Cycles c (cycle_generating_loop c) (w .fst)) (g .fst)
            (map_loop_power (NativeComponent Cycles c) Cycles (u ↦ u .fst) (component_point Cycles c)
              (cycle_group_generator c) (w .fst))
            (w .snd))))
      (cycle_loops_are_powers c (g .fst))

{` cor:id-m-cycle in group form, on the standard m-cycle (ℤ/m, s) = (Remainder m,
   modular successor), m = n+1: the symmetries are identified with
   0, 1, ..., m-1 by the image of 0, and composition corresponds to addition
   modulo m, a ⊕ b ≔ s^b(a), with 0 the identity. `}
def modular_zero (n : Nat) : Remainder (suc. n) ≔ remainder_at n zero. star.

def modular_add (n : Nat) (a b : Remainder (suc. n)) : Remainder (suc. n)
  ≔ iterate (Remainder (suc. n)) (modular_successor n) (b .fst) a

def modular_add_zero_right (n : Nat) (a : Remainder (suc. n)) : Id (Remainder (suc. n)) (modular_add n a (modular_zero n)) a
  ≔ refl a

def modular_add_zero_left (n : Nat) (b : Remainder (suc. n)) : Id (Remainder (suc. n)) (modular_add n (modular_zero n) b) b
  ≔ concat (Remainder (suc. n)) (modular_add n (modular_zero n) b)
      (remainder_at n (b .fst) (lt_from_book (b .fst) (suc. n) (b .snd))) b
      (modular_successor_iterate n (b .fst) (lt_from_book (b .fst) (suc. n) (b .snd)))
      (remainder_equal (suc. n) (remainder_at n (b .fst) (lt_from_book (b .fst) (suc. n) (b .snd))) b (refl (b .fst)))

{` Litmus: 1 ⊕ 1 = 2 modulo 3, and 2 ⊕ 1 = 0 modulo 3. `}
def modular_add_litmus_two
  : Id Nat (modular_add (suc. (suc. zero.)) (remainder_at (suc. (suc. zero.)) (suc. zero.) star.)
      (remainder_at (suc. (suc. zero.)) (suc. zero.) star.) .fst) (suc. (suc. zero.))
  ≔ refl (suc. (suc. zero.) : Nat)

def modular_add_litmus_wrap
  : Id Nat (modular_add (suc. (suc. zero.)) (remainder_at (suc. (suc. zero.)) (suc. (suc. zero.)) star.)
      (remainder_at (suc. (suc. zero.)) (suc. zero.) star.) .fst) zero.
  ≔ refl (zero. : Nat)

def cyclic_group_eval (n : Nat) (g : USym (cyclic_group (suc. n))) : Remainder (suc. n)
  ≔ cycle_path_evaluate (principal_cycle (suc. n)) (principal_cycle (suc. n)) (g .fst) (modular_zero n)

def cyclic_group_eval_equiv (n : Nat) : Equiv (USym (cyclic_group (suc. n))) (Remainder (suc. n))
  ≔ compose_equiv (USym (cyclic_group (suc. n))) (Id Cycles (principal_cycle (suc. n)) (principal_cycle (suc. n)))
      (Remainder (suc. n))
      (automorphism_group_usym_equiv Cycles cycles_groupoid (principal_cycle (suc. n)))
      (native_equivalence (Id Cycles (principal_cycle (suc. n)) (principal_cycle (suc. n))) (Remainder (suc. n))
        (cycle_automorphisms_evaluation (principal_cycle (suc. n)) (modular_zero n)))

def cyclic_group_eval_equiv_map (n : Nat) (g : USym (cyclic_group (suc. n)))
  : Id (Remainder (suc. n)) (cyclic_group_eval_equiv n .map g) (cyclic_group_eval n g)
  ≔ refl (cyclic_group_eval n g)

def cyclic_group_eval_unit (n : Nat)
  : Id (Remainder (suc. n)) (cyclic_group_eval n (usym_unit (cyclic_group (suc. n)))) (modular_zero n)
  ≔ cycle_automorphisms_identity_beta (principal_cycle (suc. n)) (modular_zero n)

def cyclic_group_eval_generator (n : Nat)
  : Id (Remainder (suc. n)) (cyclic_group_eval n (cycle_group_generator (principal_cycle (suc. n))))
      (modular_successor n (modular_zero n))
  ≔ cycle_generating_loop_action (principal_cycle (suc. n)) (modular_zero n)

def cyclic_cycle_eval (n : Nat) (p : Id Cycles (principal_cycle (suc. n)) (principal_cycle (suc. n)))
  (x : Remainder (suc. n)) : Remainder (suc. n)
  ≔ cycle_path_evaluate (principal_cycle (suc. n)) (principal_cycle (suc. n)) p x

def cyclic_cycle_eval_at_zero (n : Nat) (p : Id Cycles (principal_cycle (suc. n)) (principal_cycle (suc. n)))
  : Remainder (suc. n)
  ≔ cyclic_cycle_eval n p (modular_zero n)

def cyclic_group_eval_mul (n : Nat) (g h : USym (cyclic_group (suc. n)))
  : Id (Remainder (suc. n)) (cyclic_group_eval n (usym_mul (cyclic_group (suc. n)) g h))
      (modular_add n (cyclic_group_eval n g) (cyclic_group_eval n h))
  ≔ calc
      cyclic_group_eval n (usym_mul (cyclic_group (suc. n)) g h)
      = cyclic_cycle_eval_at_zero n (concat Cycles (principal_cycle (suc. n)) (principal_cycle (suc. n))
          (principal_cycle (suc. n)) (h .fst) (g .fst))
        by refl (cyclic_cycle_eval_at_zero n)
          (map_path_concat (CycleComponent (suc. n)) Cycles (u ↦ u .fst)
            (component_point Cycles (principal_cycle (suc. n))) (component_point Cycles (principal_cycle (suc. n)))
            (component_point Cycles (principal_cycle (suc. n))) h g)
      = cyclic_cycle_eval n (g .fst) (cyclic_group_eval n h)
        by cycle_path_evaluation_concat (principal_cycle (suc. n)) (principal_cycle (suc. n)) (principal_cycle (suc. n))
          (h .fst) (g .fst) (modular_zero n)
      = cyclic_cycle_eval n (g .fst)
          (iterate (Remainder (suc. n)) (modular_successor n) (cyclic_group_eval n h .fst) (modular_zero n))
        by refl (cyclic_cycle_eval n (g .fst))
          (inverse (Remainder (suc. n)) (modular_add n (modular_zero n) (cyclic_group_eval n h)) (cyclic_group_eval n h)
            (modular_add_zero_left n (cyclic_group_eval n h)))
      = iterate (Remainder (suc. n)) (modular_successor n) (cyclic_group_eval n h .fst) (cyclic_group_eval n g)
        by iterate_commuting_map (Remainder (suc. n)) (modular_successor n) (cyclic_cycle_eval n (g .fst))
          (cycle_paths_equiv (principal_cycle (suc. n)) (principal_cycle (suc. n)) .map (g .fst) .snd)
          (cyclic_group_eval n h .fst) (modular_zero n) ∎

{` ex:cyclicgroups, footnote: C_1 is the trivial group. `}
def fin_one_contractible : BookIsContr (Fin (suc. zero.)) ≔ (inr. star., y ↦ fin_one_type_prop (inr. star.) y)

def cyclic_group_one_trivial : Id Group (cyclic_group_fin zero.) trivial_group
  ≔ usym_contractible_trivial (cyclic_group_fin zero.)
      (book_contractibility_equiv (Fin (suc. zero.)) (USym (cyclic_group_fin zero.))
        (canonical_inverse_equiv (USym (cyclic_group_fin zero.)) (Fin (suc. zero.)) (cyclic_group_fin_usym_equiv zero.))
        .map fin_one_contractible)

{` ex:cyclicgroups, chain of identifications, for every circle C and m = n+1:
   C_m = Aut_Cyc(m, s) = Aut_{Σ(X:Set)(X ≃ X)}(m, s) = Aut_{SetBundle(S¹)}(S¹, dg_m)
   = Aut_{S¹→Set}(R_m) =: ℤ/mℤ, from the subtype Cyc ⊆ Σ(X:Set)(X ≃ X) and
   the equivalences f, g of thm:coveringsofS1perms (circle_coverings_permutations,
   coverings_setfamilies_equiv), with (S¹, dg_m) sent to (m, s) and to R_m
   (power_degree_connected_cover_path, power_circle_monodromy, setfamilies_coverings_beta). `}
def set_hlevel_three (A : Type) (hA : isSet A) : HLevel (suc. (suc. (suc. zero.))) A
  ≔ x y ↦ set_to_hlevel_two (Id A x y) (prop_is_set (Id A x y) (hA x y))

def permutations_groupoid : isGroupoid Permutations
  ≔ hlevel_to_groupoid Permutations
      (hlevel_sigma (suc. (suc. (suc. zero.))) SetTypes (S ↦ Equiv (S .fst) (S .fst))
        (groupoid_to_hlevel SetTypes sets_groupoid)
        (S ↦ set_hlevel_three (Equiv (S .fst) (S .fst)) (equivalences_set (S .fst) (S .fst) (S .snd))))

def set_families_groupoid (B : Type) : isGroupoid (B → SetTypes)
  ≔ hlevel_to_groupoid (B → SetTypes)
      (hlevel_function (suc. (suc. (suc. zero.))) B SetTypes (groupoid_to_hlevel SetTypes sets_groupoid))

def cycle_permutation_automorphism_path (c : Cycles)
  : Id Group (automorphism_group Cycles cycles_groupoid c) (automorphism_group Permutations permutations_groupoid (c .fst))
  ≔ automorphism_group_subtype_path Permutations cyclic_permutation (p ↦ cyclic_prop (p .fst .fst) (p .snd))
      cycles_groupoid permutations_groupoid c

def circle_degree_standard_cover (C : CircleSignature) (n : Nat) : Coverings (C .carrier)
  ≔ circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.)

def power_degree_cover_path (C : CircleSignature) (n : Nat)
  : Id (Coverings (C .carrier)) (power_bundle_cover C n) (circle_degree_standard_cover C n)
  ≔ power_degree_connected_cover_path C n .fst

def circle_family_monodromy_map (C : CircleSignature) (S : C .carrier → SetTypes) : Permutations
  ≔ circle_setfamilies_permutations C .map S

def circle_covering_monodromy_map (C : CircleSignature) (c : Coverings (C .carrier)) : Permutations
  ≔ circle_coverings_permutations C .map c

def covering_set_family_map (C : CircleSignature) (c : Coverings (C .carrier)) : C .carrier → SetTypes
  ≔ coverings_setfamilies_equiv (C .carrier) .map c

def power_bundle_permutation (C : CircleSignature) (n : Nat)
  : Id Permutations (circle_coverings_permutations C .map (power_bundle_cover C n)) (finite_fin_cycle n .fst)
  ≔ concat Permutations (circle_coverings_permutations C .map (power_bundle_cover C n))
      (circle_setfamilies_permutations C .map (power_circle_family C n))
      (power_fiber_set n, finite_fin_successor n)
      (refl (circle_family_monodromy_map C)
        (setfamilies_coverings_beta (C .carrier) (power_circle_family C n)))
      (power_circle_monodromy C n)

def degree_cover_permutation (C : CircleSignature) (n : Nat)
  : Id Permutations (circle_coverings_permutations C .map (circle_degree_standard_cover C n)) (finite_fin_cycle n .fst)
  ≔ concat Permutations (circle_coverings_permutations C .map (circle_degree_standard_cover C n))
      (circle_coverings_permutations C .map (power_bundle_cover C n)) (finite_fin_cycle n .fst)
      (refl (circle_covering_monodromy_map C)
        (inverse (Coverings (C .carrier)) (power_bundle_cover C n) (circle_degree_standard_cover C n)
          (power_degree_cover_path C n)))
      (power_bundle_permutation C n)

def degree_cover_set_family (C : CircleSignature) (n : Nat)
  : Id (C .carrier → SetTypes) (coverings_setfamilies_equiv (C .carrier) .map (circle_degree_standard_cover C n))
      (power_circle_family C n)
  ≔ concat (C .carrier → SetTypes) (coverings_setfamilies_equiv (C .carrier) .map (circle_degree_standard_cover C n))
      (coverings_setfamilies_equiv (C .carrier) .map (power_bundle_cover C n)) (power_circle_family C n)
      (refl (covering_set_family_map C)
        (inverse (Coverings (C .carrier)) (power_bundle_cover C n) (circle_degree_standard_cover C n)
          (power_degree_cover_path C n)))
      (setfamilies_coverings_beta (C .carrier) (power_circle_family C n))

{` ℤ/mℤ ≔ Aut_{S¹→Set}(R_m). `}
def integers_mod_group (C : CircleSignature) (n : Nat) : Group
  ≔ automorphism_group (C .carrier → SetTypes) (set_families_groupoid (C .carrier)) (power_circle_family C n)

def cyclic_permutation_group_path (n : Nat)
  : Id Group (cyclic_group_fin n) (automorphism_group Permutations permutations_groupoid (finite_fin_cycle n .fst))
  ≔ cycle_permutation_automorphism_path (finite_fin_cycle n)

def degree_cover_permutation_group_path (C : CircleSignature) (n : Nat)
  : Id Group (automorphism_group (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) (circle_degree_standard_cover C n))
      (automorphism_group Permutations permutations_groupoid (finite_fin_cycle n .fst))
  ≔ automorphism_group_equiv_path_at (Coverings (C .carrier)) Permutations (coverings_groupoid (C .carrier))
      permutations_groupoid (circle_coverings_permutations C) (circle_degree_standard_cover C n)
      (finite_fin_cycle n .fst) (degree_cover_permutation C n)

def degree_cover_integers_mod_path (C : CircleSignature) (n : Nat)
  : Id Group (automorphism_group (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) (circle_degree_standard_cover C n))
      (integers_mod_group C n)
  ≔ automorphism_group_equiv_path_at (Coverings (C .carrier)) (C .carrier → SetTypes) (coverings_groupoid (C .carrier))
      (set_families_groupoid (C .carrier)) (coverings_setfamilies_equiv (C .carrier)) (circle_degree_standard_cover C n)
      (power_circle_family C n) (degree_cover_set_family C n)

def cyclic_integers_mod_path (C : CircleSignature) (n : Nat) : Id Group (cyclic_group_fin n) (integers_mod_group C n)
  ≔ let P ≔ automorphism_group Permutations permutations_groupoid (finite_fin_cycle n .fst) in
    let D ≔ automorphism_group (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) (circle_degree_standard_cover C n) in
    concat Group (cyclic_group_fin n) P (integers_mod_group C n) (cyclic_permutation_group_path n)
      (concat Group P D (integers_mod_group C n)
        (inverse Group D P (degree_cover_permutation_group_path C n)) (degree_cover_integers_mod_path C n))
