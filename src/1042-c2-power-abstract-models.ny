export "1041-decidable-subgroups-finite"
export "702-abstract-group-identity"
export "729-pointwise-hom-products"
export "450-sign-parity-basics"

{` Chapter 10, rem:noofsubgps (fingp.tex 35-40): computational
   models of the abstract groups of C_2^n = power_group (Fin n) C_2 for
   n = 0, 1, 2 (C_2 = cyclic_group 2, module 407 / 1012):
   - abstr(C_2^0) ≅ the trivial abstract group on Unit (c2pow_zero_iso);
   - abstr(C_2^1) ≅ (Bool, xor) (c2pow_one_iso);
   - abstr(C_2^2) ≅ (Bool × Bool, componentwise xor) (c2pow_two_iso).
   The key lemma (order_two_iso) is that an equivalence of an abstract group
   with Bool, normalised to send the unit to false, preserves
   multiplication (the table of a group of order 2 is forced). For n = 2 the
   symmetries of C_2^2 are pairs of symmetries of C_2 (function
   extensionality; happly turns concatenation into pointwise concatenation).
   Isomorphic abstract groups have equivalent types of Bool-valued abstract
   subgroups (closed_bool_subsets_iso_equiv, by univalence for abstract
   groups, module 702). `}

def c2pow_group (n : Nat) : Group ≔ power_group (Fin n) (fin_is_finite n) (cyclic_group two)

{` Transfer along isomorphisms. `}
def closed_bool_subsets_iso_equiv (G H : AbstractGroup) (φ : AbstractIso G H)
  : Equiv (ClosedBoolSubsets G) (ClosedBoolSubsets H)
  ≔ transport_equiv (ClosedBoolSubsets G) (ClosedBoolSubsets H)
      (map_path AbstractGroup Type ClosedBoolSubsets G H (abstract_group_path_from_iso G H φ))

{` (Bool, xor), the abstract group C_2. `}
def c2abs_bool_laws : AbstractGroupLaws Bool false. bool_xor (x ↦ x)
  ≔ (carrier_set ≔ bool_set,
     unit_right ≔ bool_xor_false_right,
     unit_left ≔ g ↦ refl g,
     assoc ≔ a b c ↦ inverse Bool (bool_xor (bool_xor a b) c) (bool_xor a (bool_xor b c)) (bool_xor_assoc a b c),
     inv_right ≔ bool_xor_self)

def c2abs_bool : AbstractGroup ≔ (Bool, false., bool_xor, x ↦ x, c2abs_bool_laws)

{` (Bool × Bool, componentwise xor), the abstract group C_2 × C_2. `}
def c2sq_mul (x y : Product Bool Bool) : Product Bool Bool ≔ (bool_xor (x .fst) (y .fst), bool_xor (x .snd) (y .snd))

def c2sq_laws : AbstractGroupLaws (Product Bool Bool) (false., false.) c2sq_mul (x ↦ x)
  ≔ (carrier_set ≔ product_set Bool Bool bool_set bool_set,
     unit_right ≔ g ↦ (bool_xor_false_right (g .fst), bool_xor_false_right (g .snd)),
     unit_left ≔ g ↦ refl g,
     assoc ≔ a b c ↦
       (inverse Bool (bool_xor (bool_xor (a .fst) (b .fst)) (c .fst)) (bool_xor (a .fst) (bool_xor (b .fst) (c .fst)))
          (bool_xor_assoc (a .fst) (b .fst) (c .fst)),
        inverse Bool (bool_xor (bool_xor (a .snd) (b .snd)) (c .snd)) (bool_xor (a .snd) (bool_xor (b .snd) (c .snd)))
          (bool_xor_assoc (a .snd) (b .snd) (c .snd))),
     inv_right ≔ g ↦ (bool_xor_self (g .fst), bool_xor_self (g .snd)))

def c2sq_abstract : AbstractGroup ≔ (Product Bool Bool, (false., false.), c2sq_mul, x ↦ x, c2sq_laws)

{` Groups of order 2. Shifting an equivalence with Bool so that the unit
   goes to false. `}
def c2abs_xor_invol (c k : Bool) : Id Bool (bool_xor (bool_xor c k) k) c
  ≔ match c, k [
    | false., false. ↦ refl (false. : Bool)
    | false., true. ↦ refl (false. : Bool)
    | true., false. ↦ refl (true. : Bool)
    | true., true. ↦ refl (true. : Bool) ]

def c2abs_shift_equiv (k : Bool) : Equiv Bool Bool
  ≔ quasi_inverse_equiv Bool Bool (c ↦ bool_xor c k) (c ↦ bool_xor c k) (c ↦ c2abs_xor_invol c k) (c ↦ c2abs_xor_invol c k)

def order_two_normalize (H : AbstractGroup) (ψ : Equiv (H .carrier) Bool) : Equiv (H .carrier) Bool
  ≔ compose_equiv (H .carrier) Bool Bool ψ (c2abs_shift_equiv (ψ .map (H .unit)))

def order_two_hom_tt (H : AbstractGroup) (f : Equiv (H .carrier) Bool) (h0 : Id Bool (f .map (H .unit)) false.)
  (s t : H .carrier) (ea : Id Bool (f .map s) true.) (st : Id (H .carrier) s t) (c : Bool)
  (ec : Id Bool (f .map (H .mul s t)) c)
  : Id Bool (f .map (H .mul s t)) false.
  ≔ let S ≔ H .carrier in let F ≔ f .map in
    match c [
    | false. ↦ ec
    | true. ↦
      let ss : Id S (H .mul s s) s
        ≔ concat S (H .mul s s) (H .mul s t) s (map_path S S (H .mul s) s t st)
            (equivalence_injective S Bool f (H .mul s t) s (concat Bool (F (H .mul s t)) true. (F s) ec (inverse Bool (F s) true. ea))) in
      let se : Id S s (H .unit) ≔ ag_idempotent_unit H s ss in
      absurd (Id Bool (F (H .mul s t)) false.)
        (bool_encode false. true.
          (concat Bool false. (F (H .unit)) true. (inverse Bool (F (H .unit)) false. h0)
            (concat Bool (F (H .unit)) (F s) true. (map_path S Bool F (H .unit) s (inverse S s (H .unit) se)) ea))) ]

def order_two_hom_at (H : AbstractGroup) (f : Equiv (H .carrier) Bool) (h0 : Id Bool (f .map (H .unit)) false.)
  (s t : H .carrier) (a b : Bool) (ea : Id Bool (f .map s) a) (eb : Id Bool (f .map t) b)
  : Id Bool (f .map (H .mul s t)) (bool_xor a b)
  ≔ let S ≔ H .carrier in let F ≔ f .map in
    match a [
    | false. ↦
      let se : Id S s (H .unit)
        ≔ equivalence_injective S Bool f s (H .unit) (concat Bool (F s) false. (F (H .unit)) ea (inverse Bool (F (H .unit)) false. h0)) in
      concat Bool (F (H .mul s t)) (F (H .mul (H .unit) t)) b
        (map_path S Bool F (H .mul s t) (H .mul (H .unit) t) (map_path S S (x ↦ H .mul x t) s (H .unit) se))
        (concat Bool (F (H .mul (H .unit) t)) (F t) b (map_path S Bool F (H .mul (H .unit) t) t (H .laws .unit_left t)) eb)
    | true. ↦ match b [
      | false. ↦
        let te : Id S t (H .unit)
          ≔ equivalence_injective S Bool f t (H .unit) (concat Bool (F t) false. (F (H .unit)) eb (inverse Bool (F (H .unit)) false. h0)) in
        concat Bool (F (H .mul s t)) (F (H .mul s (H .unit))) true.
          (map_path S Bool F (H .mul s t) (H .mul s (H .unit)) (map_path S S (H .mul s) t (H .unit) te))
          (concat Bool (F (H .mul s (H .unit))) (F s) true. (map_path S Bool F (H .mul s (H .unit)) s (H .laws .unit_right s)) ea)
      | true. ↦
        order_two_hom_tt H f h0 s t ea
          (equivalence_injective S Bool f s t (concat Bool (F s) true. (F t) ea (inverse Bool (F t) true. eb)))
          (F (H .mul s t)) (refl (F (H .mul s t))) ] ]

def order_two_hom (H : AbstractGroup) (f : Equiv (H .carrier) Bool) (h0 : Id Bool (f .map (H .unit)) false.)
  : IsAbstractHom H c2abs_bool (f .map)
  ≔ s t ↦ order_two_hom_at H f h0 s t (f .map s) (f .map t) (refl (f .map s)) (refl (f .map t))

{` An abstract group equivalent to Bool is isomorphic to (Bool, xor). `}
def order_two_iso (H : AbstractGroup) (ψ : Equiv (H .carrier) Bool) : AbstractIso H c2abs_bool
  ≔ (order_two_normalize H ψ, order_two_hom H (order_two_normalize H ψ) (bool_xor_self (ψ .map (H .unit))))

{` C_2 and C_2^1. `}
def c2_usym_bool_equiv : Equiv (USym (cyclic_group two)) Bool
  ≔ compose_equiv (USym (cyclic_group two)) (Fin two) Bool (cyclic_group_usym_fin_equiv (suc. zero.)) fin_two_equiv

def c2_iso : AbstractIso (abstr (cyclic_group two)) c2abs_bool
  ≔ order_two_iso (abstr (cyclic_group two)) c2_usym_bool_equiv

def c2abs_fin_one_functions_equiv (B : Type) : Equiv (Fin (suc. zero.) → B) B
  ≔ quasi_inverse_equiv (Fin (suc. zero.) → B) B (f ↦ f (inr. star.)) (b _ ↦ b)
      (f ↦ funext (Fin (suc. zero.)) (_ ↦ B) (_ ↦ f (inr. star.)) f
        (x ↦ match x [ inl. e ↦ match e [] | inr. u ↦ match u [ star. ↦ refl (f (inr. star.)) ] ]))
      (b ↦ refl b)

def c2pow_one_bool_equiv : Equiv (USym (c2pow_group (suc. zero.))) Bool
  ≔ let C ≔ cyclic_group two in
    compose_equiv (USym (c2pow_group (suc. zero.))) (Fin (suc. zero.) → USym C) Bool
      (power_group_usym_equiv (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) C)
      (compose_equiv (Fin (suc. zero.) → USym C) (USym C) Bool (c2abs_fin_one_functions_equiv (USym C)) c2_usym_bool_equiv)

def c2pow_one_iso : AbstractIso (abstr (c2pow_group (suc. zero.))) c2abs_bool
  ≔ order_two_iso (abstr (c2pow_group (suc. zero.))) c2pow_one_bool_equiv

{` C_2^0 is trivial. `}
def c2pow_zero_unit_equiv : Equiv (USym (c2pow_group zero.)) Unit
  ≔ let C ≔ cyclic_group two in
    compose_equiv (USym (c2pow_group zero.)) (Fin zero. → USym C) Unit
      (power_group_usym_equiv (Fin zero.) (fin_is_finite zero.) C)
      (compose_equiv (Fin zero. → USym C) (Fin (suc. zero.)) Unit (fingp_fin_zero_functions_equiv (USym C)) fin_one_equiv)

def c2pow_zero_iso : AbstractIso (abstr (c2pow_group zero.)) unit_abstract_group
  ≔ (c2pow_zero_unit_equiv, s t ↦ unit_prop (c2pow_zero_unit_equiv .map (usym_mul (c2pow_group zero.) s t)) star.)

{` C_2^2: symmetries are pairs of symmetries of C_2. `}
def c2pow_happly_concat (I X : Type) (f g h : I → X) (p : Id (I → X) f g) (q : Id (I → X) g h) (i : I)
  : Id (Id X (f i) (h i)) (happly I (_ ↦ X) f h (concat (I → X) f g h p q) i)
      (concat X (f i) (g i) (h i) (happly I (_ ↦ X) f g p i) (happly I (_ ↦ X) g h q i))
  ≔ J (I → X) g
      (h q ↦ Id (Id X (f i) (h i)) (happly I (_ ↦ X) f h (concat (I → X) f g h p q) i)
          (concat X (f i) (g i) (h i) (happly I (_ ↦ X) f g p i) (happly I (_ ↦ X) g h q i)))
      (concat (Id X (f i) (g i)) (happly I (_ ↦ X) f g (concat (I → X) f g g p (refl g)) i) (happly I (_ ↦ X) f g p i)
        (concat X (f i) (g i) (g i) (happly I (_ ↦ X) f g p i) (refl (g i)))
        (refl ((r ↦ happly I (_ ↦ X) f g r i) : Id (I → X) f g → Id X (f i) (g i)) (concat_p1 (I → X) f g p))
        (inverse (Id X (f i) (g i)) (concat X (f i) (g i) (g i) (happly I (_ ↦ X) f g p i) (refl (g i)))
          (happly I (_ ↦ X) f g p i) (concat_p1 X (f i) (g i) (happly I (_ ↦ X) f g p i))))
      h q

def c2abs_fin_two_function (B : Type) (p : Product B B) (x : Fin two) : B
  ≔ match x [ inr. _ ↦ p .fst | inl. (inr. _) ↦ p .snd | inl. (inl. e) ↦ match e [] ]

def c2abs_fin_two_functions_equiv (B : Type) : Equiv (Fin two → B) (Product B B)
  ≔ quasi_inverse_equiv (Fin two → B) (Product B B) (f ↦ (f (inr. star.), f (inl. (inr. star.))))
      (c2abs_fin_two_function B)
      (f ↦ funext (Fin two) (_ ↦ B) (c2abs_fin_two_function B (f (inr. star.), f (inl. (inr. star.)))) f
        (x ↦ match x [
          | inr. u ↦ match u [ star. ↦ refl (f (inr. star.)) ]
          | inl. (inr. u) ↦ match u [ star. ↦ refl (f (inl. (inr. star.))) ]
          | inl. (inl. e) ↦ match e [] ]))
      (p ↦ refl p)

def c2pow_two_equiv : Equiv (USym (c2pow_group two)) (Product Bool Bool)
  ≔ let C ≔ cyclic_group two in
    let φ ≔ c2_iso .fst in
    compose_equiv (USym (c2pow_group two)) (Fin two → USym C) (Product Bool Bool)
      (power_group_usym_equiv (Fin two) (fin_is_finite two) C)
      (compose_equiv (Fin two → USym C) (Product (USym C) (USym C)) (Product Bool Bool)
        (c2abs_fin_two_functions_equiv (USym C)) (product_equiv (USym C) (USym C) Bool Bool φ φ))

def c2pow_two_component (s : USym (c2pow_group two)) (i : Fin two) : USym (cyclic_group two)
  ≔ happly (Fin two) (_ ↦ BG (cyclic_group two) .carrier) (_ ↦ shape (cyclic_group two)) (_ ↦ shape (cyclic_group two)) s i

def c2pow_two_component_mul (s t : USym (c2pow_group two)) (i : Fin two)
  : Id Bool (c2_iso .fst .map (c2pow_two_component (usym_mul (c2pow_group two) s t) i))
      (bool_xor (c2_iso .fst .map (c2pow_two_component s i)) (c2_iso .fst .map (c2pow_two_component t i)))
  ≔ let C ≔ cyclic_group two in
    let o : Fin two → BG C .carrier ≔ _ ↦ shape C in
    concat Bool (c2_iso .fst .map (c2pow_two_component (usym_mul (c2pow_group two) s t) i))
      (c2_iso .fst .map (usym_mul C (c2pow_two_component s i) (c2pow_two_component t i)))
      (bool_xor (c2_iso .fst .map (c2pow_two_component s i)) (c2_iso .fst .map (c2pow_two_component t i)))
      (map_path (USym C) Bool (c2_iso .fst .map)
        (c2pow_two_component (usym_mul (c2pow_group two) s t) i)
        (usym_mul C (c2pow_two_component s i) (c2pow_two_component t i))
        (c2pow_happly_concat (Fin two) (BG C .carrier) o o o t s i))
      (c2_iso .snd (c2pow_two_component s i) (c2pow_two_component t i))

def c2pow_two_iso : AbstractIso (abstr (c2pow_group two)) c2sq_abstract
  ≔ (c2pow_two_equiv,
     s t ↦ (c2pow_two_component_mul s t (inr. star.), c2pow_two_component_mul s t (inl. (inr. star.))))
