export "451-sign-parity-relation"
export "403-abstract-groups"

{` Chapter 4, sec:sign-homomorphism: the set {±1} with multiplication, the
   sign of a self-identification of a two-element set (whether it swaps the
   two elements), and the identification of USym Σ_2 with {±1} (footnote to
   "the self-identifications of a 2-element set T can be identified with
   {±1}"). `}

def Sign : Type ≔ data [ plus. | minus. ]

def sign_mul (s t : Sign) : Sign
  ≔ match s [ plus. ↦ t | minus. ↦ match t [ plus. ↦ minus. | minus. ↦ plus. ] ]

def bool_sign (b : Bool) : Sign ≔ match b [ false. ↦ plus. | true. ↦ minus. ]

def sign_is_minus (s : Sign) : Bool ≔ match s [ plus. ↦ false. | minus. ↦ true. ]

def sign_bool_equiv : Equiv Sign Bool
  ≔ quasi_inverse_equiv Sign Bool sign_is_minus bool_sign
      [ plus. ↦ refl (plus. : Sign) | minus. ↦ refl (minus. : Sign) ]
      [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ]

def sign_set : isSet Sign
  ≔ hlevel_two_to_set Sign
      (hlevel_equiv (suc. (suc. zero.)) Bool Sign (canonical_inverse_equiv Sign Bool sign_bool_equiv)
        (set_to_hlevel_two Bool bool_set))

def sign_bool_roundtrip (s : Sign) : Id Sign (bool_sign (sign_is_minus s)) s
  ≔ match s [ plus. ↦ refl (plus. : Sign) | minus. ↦ refl (minus. : Sign) ]

def bool_sign_xor (a b : Bool) : Id Sign (bool_sign (bool_xor a b)) (sign_mul (bool_sign a) (bool_sign b))
  ≔ match a, b [
  | false., false. ↦ refl (plus. : Sign)
  | false., true. ↦ refl (minus. : Sign)
  | true., false. ↦ refl (minus. : Sign)
  | true., true. ↦ refl (plus. : Sign) ]

def sign_mul_comm (s t : Sign) : Id Sign (sign_mul s t) (sign_mul t s)
  ≔ match s, t [
  | plus., plus. ↦ refl (plus. : Sign)
  | plus., minus. ↦ refl (minus. : Sign)
  | minus., plus. ↦ refl (minus. : Sign)
  | minus., minus. ↦ refl (plus. : Sign) ]

def sign_mul_assoc (s t u : Sign) : Id Sign (sign_mul s (sign_mul t u)) (sign_mul (sign_mul s t) u)
  ≔ match s, t, u [
  | plus., _, _ ↦ refl (sign_mul t u)
  | minus., plus., _ ↦ refl (sign_mul minus. u)
  | minus., minus., plus. ↦ refl (plus. : Sign)
  | minus., minus., minus. ↦ refl (minus. : Sign) ]

def sign_mul_plus_right (s : Sign) : Id Sign (sign_mul s plus.) s
  ≔ match s [ plus. ↦ refl (plus. : Sign) | minus. ↦ refl (minus. : Sign) ]

def sign_mul_self (s : Sign) : Id Sign (sign_mul s s) plus.
  ≔ match s [ plus. ↦ refl (plus. : Sign) | minus. ↦ refl (plus. : Sign) ]

{` {±1} as an abstract group under multiplication (each element is its own inverse). `}
def sign_abstract_group : AbstractGroup
  ≔ (Sign, plus., sign_mul, s ↦ s,
      (sign_set, sign_mul_plus_right, s ↦ refl s, sign_mul_assoc, sign_mul_self))

def plus_ne_minus (p : Id Sign plus. minus.) : Empty
  ≔ bool_encode false. true. (refl sign_is_minus p)

{` Self-identifications of points of BΣ_2 and the equivalences they induce. `}
def bsigma_two_transport (T U : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T U)
  : Equiv (T .fst .fst) (U .fst .fst)
  ≔ transport_equiv (T .fst .fst) (U .fst .fst) (q .fst .fst)

{` Loops of BΣ_n are determined by their action on the underlying set. `}
def bsigma_path_ext (n : Nat) (T U : BookFiniteSetsAt n) (q r : Id (BookFiniteSetsAt n) T U)
  (h : (x : T .fst .fst) → Id (U .fst .fst) (q .fst .fst .trr x) (r .fst .fst .trr x))
  : Id (Id (BookFiniteSetsAt n) T U) q r
  ≔ equiv_injective_path (Id (BookFiniteSetsAt n) T U) (Id SetTypes (T .fst) (U .fst))
      (component_path_equiv SetTypes (Fin n, fin_set n) T U) q r
      (equiv_injective_path (Id SetTypes (T .fst) (U .fst)) (Equiv (T .fst .fst) (U .fst .fst))
        (set_paths_equiv (T .fst) (U .fst)) (q .fst) (r .fst)
        (equiv_homotopy (T .fst .fst) (U .fst .fst)
          (id_to_equiv (T .fst .fst) (U .fst .fst) (q .fst .fst)) (id_to_equiv (T .fst .fst) (U .fst .fst) (r .fst .fst))
          (x ↦ calc id_to_equiv (T .fst .fst) (U .fst .fst) (q .fst .fst) .map x
              = q .fst .fst .trr x by id_to_equiv_transport (T .fst .fst) (U .fst .fst) (q .fst .fst) x
            = r .fst .fst .trr x by h x
            = id_to_equiv (T .fst .fst) (U .fst .fst) (r .fst .fst) .map x
              by inverse (U .fst .fst) (id_to_equiv (T .fst .fst) (U .fst .fst) (r .fst .fst) .map x) (r .fst .fst .trr x)
                (id_to_equiv_transport (T .fst .fst) (U .fst .fst) (r .fst .fst) x) ∎)))

{` Whether a self-identification q of T swaps the two elements. `}
def two_loop_moves (T : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T T) : Bool
  ≔ two_moves (T .fst .fst) (two_set_two_element T) (bsigma_two_transport T T q)

def two_loop_moves_concat (T : BookFiniteSetsAt two) (q r : Id (BookFiniteSetsAt two) T T)
  : Id Bool (two_loop_moves T (concat (BookFiniteSetsAt two) T T T q r)) (bool_xor (two_loop_moves T q) (two_loop_moves T r))
  ≔ let A ≔ T .fst .fst in let h ≔ two_set_two_element T in
    concat Bool (two_loop_moves T (concat (BookFiniteSetsAt two) T T T q r))
      (two_moves A h (compose_equiv A A A (bsigma_two_transport T T q) (bsigma_two_transport T T r)))
      (bool_xor (two_loop_moves T q) (two_loop_moves T r))
      (two_moves_homotopy A h (bsigma_two_transport T T (concat (BookFiniteSetsAt two) T T T q r))
        (compose_equiv A A A (bsigma_two_transport T T q) (bsigma_two_transport T T r))
        (x ↦ transport_concat (BookFiniteSetsAt two) (U ↦ U .fst .fst) T T T q r x))
      (two_moves_compose A h (bsigma_two_transport T T q) (bsigma_two_transport T T r))

def two_loop_moves_refl (T : BookFiniteSetsAt two) : Id Bool (two_loop_moves T (refl T)) false.
  ≔ let A ≔ T .fst .fst in let h ≔ two_set_two_element T in
    concat Bool (two_loop_moves T (refl T)) (two_moves A h (identity_equiv A)) false.
      (two_moves_homotopy A h (bsigma_two_transport T T (refl T)) (identity_equiv A)
        (x ↦ transport_refl (BookFiniteSetsAt two) (U ↦ U .fst .fst) T x))
      (two_moves_identity A h)

{` Conjugation invariance: for c : T = U and a loop q at U, the loop
   c · q · c⁻¹ at T swaps iff q does. `}
def two_loop_moves_conjugate (T U : BookFiniteSetsAt two) (c : Id (BookFiniteSetsAt two) T U) (q : Id (BookFiniteSetsAt two) U U)
  : Id Bool (two_loop_moves T (pointed_loop_conjugate (BookFiniteSetsAt two) T U c q)) (two_loop_moves U q)
  ≔ let B ≔ BookFiniteSetsAt two in
    J B T (U c ↦ (q : Id B U U) → Id Bool (two_loop_moves T (pointed_loop_conjugate B T U c q)) (two_loop_moves U q))
      (q ↦ refl (two_loop_moves T)
        (calc pointed_loop_conjugate B T T (refl T) q
          = concat B T T T q (inverse B T T (refl T)) by concat_1p B T T (concat B T T T q (inverse B T T (refl T)))
          = concat B T T T q (refl T) by refl (concat B T T T q) (inverse_refl B T)
          = q by concat_p1 B T T q ∎))
      U c q

def bool_xor_false_eq (a b : Bool) (q : Id Bool (bool_xor a b) false.) : Id Bool a b
  ≔ match a, b [
  | false., false. ↦ refl (false. : Bool)
  | true., true. ↦ refl (true. : Bool)
  | false., true. ↦ absurd (Id Bool false. true.) (bool_encode true. false. q)
  | true., false. ↦ absurd (Id Bool true. false.) (bool_encode true. false. q) ]

def two_loop_moves_inverse (T : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T T)
  : Id Bool (two_loop_moves T (inverse (BookFiniteSetsAt two) T T q)) (two_loop_moves T q)
  ≔ let B ≔ BookFiniteSetsAt two in
    inverse Bool (two_loop_moves T q) (two_loop_moves T (inverse B T T q))
      (bool_xor_false_eq (two_loop_moves T q) (two_loop_moves T (inverse B T T q))
        (calc bool_xor (two_loop_moves T q) (two_loop_moves T (inverse B T T q))
          = two_loop_moves T (concat B T T T q (inverse B T T q))
            by inverse Bool (two_loop_moves T (concat B T T T q (inverse B T T q)))
              (bool_xor (two_loop_moves T q) (two_loop_moves T (inverse B T T q)))
              (two_loop_moves_concat T q (inverse B T T q))
          = two_loop_moves T (refl T) by refl (two_loop_moves T) (concat_inverse_right B T T q)
          = false. by two_loop_moves_refl T ∎))

{` The swap of a two-element type (each point goes to the other one). `}
def two_element_other_other (A : Type) (h : TwoElement A) (x : A)
  : Id A (two_element_other A h (two_element_other A h x)) x
  ≔ inverse A x (two_element_other A h (two_element_other A h x))
      (two_element_other_unique A h (two_element_other A h x) x
        (p ↦ two_element_other_ne A h x (inverse A x (two_element_other A h x) p)))

def two_element_swap (A : Type) (h : TwoElement A) : Equiv A A
  ≔ quasi_inverse_equiv A A (two_element_other A h) (two_element_other A h)
      (two_element_other_other A h) (two_element_other_other A h)

def two_set_swap_loop (T : BookFiniteSetsAt two) : Id (BookFiniteSetsAt two) T T
  ≔ component_path SetTypes (Fin two, fin_set two) T T
      (set_types_path (T .fst) (T .fst) (two_element_swap (T .fst .fst) (two_set_two_element T)))

def two_set_swap_loop_moves (T : BookFiniteSetsAt two) : Id Bool (two_loop_moves T (two_set_swap_loop T)) true.
  ≔ let A ≔ T .fst .fst in let h ≔ two_set_two_element T in
    two_element_point_elim A h (Id Bool (two_loop_moves T (two_set_swap_loop T)) true.)
      (bool_set (two_loop_moves T (two_set_swap_loop T)) true.)
      (x ↦ concat Bool (two_loop_moves T (two_set_swap_loop T)) (two_differ A h x (two_element_other A h x)) true.
        (two_moves_value A h (bsigma_two_transport T T (two_set_swap_loop T)) x)
        (two_differ_ne A h x (two_element_other A h x)
          (p ↦ two_element_other_ne A h x (inverse A x (two_element_other A h x) p))))

{` The sign of a self-identification of a two-element set, and the
   identification (T = T) ≃ {±1} (footnote, xca:2-element-sets). `}
def two_loop_sign (T : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T T) : Sign ≔ bool_sign (two_loop_moves T q)

def two_loop_of_sign (T : BookFiniteSetsAt two) : Sign → Id (BookFiniteSetsAt two) T T
  ≔ [ plus. ↦ refl T | minus. ↦ two_set_swap_loop T ]

def two_loop_sign_section (T : BookFiniteSetsAt two) (q : Id (BookFiniteSetsAt two) T T) (b : Bool)
  (e : Id Bool (two_loop_moves T q) b)
  : Id (Id (BookFiniteSetsAt two) T T) (two_loop_of_sign T (bool_sign b)) q
  ≔ let A ≔ T .fst .fst in let h ≔ two_set_two_element T in
    let tq ≔ bsigma_two_transport T T q in
    match b [
    | false. ↦ bsigma_path_ext two T T (refl T) q
        (x ↦ concat A ((refl T) .fst .fst .trr x) x (q .fst .fst .trr x)
          (transport_refl (BookFiniteSetsAt two) (U ↦ U .fst .fst) T x)
          (inverse A (tq .map x) x (two_moves_false_fixed A h tq e x)))
    | true. ↦ bsigma_path_ext two T T (two_set_swap_loop T) q
        (x ↦ two_element_ne_ne A h (two_element_other A h x) x (tq .map x)
          (two_element_other_ne A h x)
          (p ↦ two_moves_true_moved A h tq e x (inverse A (tq .map x) x p))) ]

def two_loops_sign_equiv (T : BookFiniteSetsAt two) : Equiv (Id (BookFiniteSetsAt two) T T) Sign
  ≔ quasi_inverse_equiv (Id (BookFiniteSetsAt two) T T) Sign (two_loop_sign T) (two_loop_of_sign T)
      (q ↦ two_loop_sign_section T q (two_loop_moves T q) (refl (two_loop_moves T q)))
      [ plus. ↦ refl bool_sign (two_loop_moves_refl T)
      | minus. ↦ refl bool_sign (two_set_swap_loop_moves T) ]

def two_loop_sign_concat (T : BookFiniteSetsAt two) (q r : Id (BookFiniteSetsAt two) T T)
  : Id Sign (two_loop_sign T (concat (BookFiniteSetsAt two) T T T q r)) (sign_mul (two_loop_sign T q) (two_loop_sign T r))
  ≔ concat Sign (two_loop_sign T (concat (BookFiniteSetsAt two) T T T q r))
      (bool_sign (bool_xor (two_loop_moves T q) (two_loop_moves T r)))
      (sign_mul (two_loop_sign T q) (two_loop_sign T r))
      (refl bool_sign (two_loop_moves_concat T q r))
      (bool_sign_xor (two_loop_moves T q) (two_loop_moves T r))

{` Footnote: USym Σ_2 is identified with {±1}; usym_mul corresponds to multiplication. `}
def sign_sigma_two : Group ≔ symmetric_group two

def sigma_two_sign (g : USym sign_sigma_two) : Sign ≔ two_loop_sign (shape sign_sigma_two) g

def sigma_two_sign_equiv : Equiv (USym sign_sigma_two) Sign ≔ two_loops_sign_equiv (shape sign_sigma_two)

def sigma_two_sign_mul (g h : USym sign_sigma_two)
  : Id Sign (sigma_two_sign (usym_mul sign_sigma_two g h)) (sign_mul (sigma_two_sign g) (sigma_two_sign h))
  ≔ concat Sign (sigma_two_sign (usym_mul sign_sigma_two g h)) (sign_mul (sigma_two_sign h) (sigma_two_sign g))
      (sign_mul (sigma_two_sign g) (sigma_two_sign h))
      (two_loop_sign_concat (shape sign_sigma_two) h g)
      (sign_mul_comm (sigma_two_sign h) (sigma_two_sign g))

def sigma_two_sign_abstract_hom : AbstractHom (abstr sign_sigma_two) sign_abstract_group
  ≔ (sigma_two_sign, sigma_two_sign_mul)

def sigma_two_sign_unit : Id Sign (sigma_two_sign (usym_unit sign_sigma_two)) plus.
  ≔ refl bool_sign (two_loop_moves_refl (shape sign_sigma_two))

{` Litmus: the transposition of Fin 2 has sign −1. `}
def fin_two_swap_loop_sign : Id Sign (sigma_two_sign (two_set_swap_loop (shape sign_sigma_two))) minus.
  ≔ refl bool_sign (two_set_swap_loop_moves (shape sign_sigma_two))

{` The sign of a loop conjugated by any path into the shape. `}
def two_loop_sign_conjugate (T U : BookFiniteSetsAt two) (c : Id (BookFiniteSetsAt two) T U) (q : Id (BookFiniteSetsAt two) U U)
  : Id Sign (two_loop_sign T (pointed_loop_conjugate (BookFiniteSetsAt two) T U c q)) (two_loop_sign U q)
  ≔ refl bool_sign (two_loop_moves_conjugate T U c q)
