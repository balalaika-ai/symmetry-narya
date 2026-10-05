export "807-generalized-dihedral-groups"

{` Chapter 8, con:bidirectional-bicycle (congp.tex:109) and its
   implementation, first part: the map φ : BD_n → Bicyc, the standard
   dihedral bicycle of degree n, and the identification of φ(sh) with it.

   Everything is stated for a subgroup (H, h) of Z (Z/~_n = SubgroupQuotient H h
   for H = order_periods n). BD_n is judgmentally
   DihedralClassifyingType (order_periods n) (order_subgroup_laws n), i.e.
   Σ_{S : BΣ_2} (T_S)_{(X_S, f)} with T_S = Σ_{X:Set} (S → X → X)
   (dihedral_classifying_type_path is refl).

   φ(S, X, f) ≔ (S × X, a, b) with a(s, x) = (s, f_s x) and
   b(s, x) = (swap s, x). The inverse of a is (s, x) ↦ (s, f_{swap s} x): for
   (X, f) in the component of the bidirectional cycle (X_S, f), f_{swap s} is
   a two-sided inverse of f_s (a proposition, transported from
   dihedral_point_inverse_pair). The connectivity condition of def:bicycle is
   a proposition; it holds at the base point because φ(sh) is isomorphic to the
   standard dihedral bicycle, and everywhere since BD_n is connected.

   The standard dihedral bicycle of degree n is (Z/~_n ⊔ Z/~_n, a, b) with
   a(inl [z]) = inl [z+1], a(inr [z]) = inr [z−1], b(inl [z]) = inr [z],
   b(inr [z]) = inl [z] (judgmentally on classes, see the litmus checks).
   The base point (Fin 2, X_{Fin 2}, f) of BD_n is sent to (Fin 2 × X, a, b),
   identified with the standard bicycle by inl q ↦ (yes, ι q), inr q ↦ (no, ι q)
   where ι q = [(yes, q)] (dihedral_insert, the inverse of the evaluation
   X ≅ Z/~_n of module 806); this is the book's "(+1, x) ↦ inl x and
   (−1, x) ↦ inr x" with yes = +1 the forward direction. `}

def DihedralClassifyingType (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type
  ≔ Σ TwoElementSets (S ↦ NativeComponent (S2C3Type S) (dihedral_point S H h))

def dihedral_two_shape : TwoElementSets ≔ shape (symmetric_group two)

def dihedral_classifying_base (H : Subtypes Int) (h : IntegerSubgroupLaws H) : DihedralClassifyingType H h
  ≔ (dihedral_two_shape, component_point (S2C3Type dihedral_two_shape) (dihedral_point dihedral_two_shape H h))

def dihedral_classifying_connected (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Connected (DihedralClassifyingType H h)
  ≔ native_connected_sigma TwoElementSets (S ↦ NativeComponent (S2C3Type S) (dihedral_point S H h))
      (bg_connected (symmetric_group two)) (S ↦ native_component_connected (S2C3Type S) (dihedral_point S H h))

{` BD_n and its shape are the above (judgmentally). `}
def dihedral_classifying_type_path (n : Order)
  : Id Type (DihedralClassifyingType (order_periods n) (order_subgroup_laws n)) (BG (generalized_dihedral_group n) .carrier)
  ≔ refl (DihedralClassifyingType (order_periods n) (order_subgroup_laws n))

def dihedral_classifying_base_path (n : Order)
  : Id (BG (generalized_dihedral_group n) .carrier)
      (dihedral_classifying_base (order_periods n) (order_subgroup_laws n)) (shape (generalized_dihedral_group n))
  ≔ refl (shape (generalized_dihedral_group n))

{` For (X, f) in the component, f_{swap s} is inverse to f_s. `}
def dbc_inverse_pair (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (s : two_set_carrier (x .fst)) : DihedralInversePair (x .fst) s (x .snd .fst)
  ≔ mere_rec (Id (S2C3Type (x .fst)) (dihedral_point (x .fst) H h) (x .snd .fst))
      (DihedralInversePair (x .fst) s (x .snd .fst)) (dihedral_inverse_pair_prop (x .fst) s (x .snd .fst))
      (p ↦ transport (S2C3Type (x .fst)) (DihedralInversePair (x .fst) s) (dihedral_point (x .fst) H h) (x .snd .fst) p
        (dihedral_point_inverse_pair (x .fst) H h s))
      (x .snd .snd)

{` swap (swap s) = s. `}
def dbc_swap_swap (S : TwoElementSets) (s : two_set_carrier S)
  : Id (two_set_carrier S) (two_set_swap S (two_set_swap S s)) s
  ≔ inverse (two_set_carrier S) s (two_set_swap S (two_set_swap S s))
      (two_set_other_is_swap S (two_set_swap S s) s
        (q ↦ two_set_swap_ne S s (inverse (two_set_carrier S) s (two_set_swap S s) q)))

{` a(s, x) = (s, f_s x), with inverse (s, x) ↦ (s, f_{swap s} x). `}
def dbc_a_map (S : TwoElementSets) (t : S2C3Type S) (u : Product (two_set_carrier S) (t .fst .fst))
  : Product (two_set_carrier S) (t .fst .fst)
  ≔ (u .fst, t .snd (u .fst) (u .snd))

def dbc_a_inverse_map (S : TwoElementSets) (t : S2C3Type S) (u : Product (two_set_carrier S) (t .fst .fst))
  : Product (two_set_carrier S) (t .fst .fst)
  ≔ (u .fst, t .snd (two_set_swap S (u .fst)) (u .snd))

def dbc_pair_at (A X : Type) (a : A) (x : X) : Product A X ≔ (a, x)

def dbc_a_equiv (S : TwoElementSets) (t : S2C3Type S) (l : (s : two_set_carrier S) → DihedralInversePair S s t)
  : Equiv (Product (two_set_carrier S) (t .fst .fst)) (Product (two_set_carrier S) (t .fst .fst))
  ≔ quasi_inverse_equiv (Product (two_set_carrier S) (t .fst .fst)) (Product (two_set_carrier S) (t .fst .fst))
      (dbc_a_map S t) (dbc_a_inverse_map S t)
      (u ↦ refl (dbc_pair_at (two_set_carrier S) (t .fst .fst) (u .fst)) (l (u .fst) .fst (u .snd)))
      (u ↦ refl (dbc_pair_at (two_set_carrier S) (t .fst .fst) (u .fst)) (l (u .fst) .snd (u .snd)))

{` b(s, x) = (swap s, x), an involution. `}
def dbc_b_map (S : TwoElementSets) (X : Type) (u : Product (two_set_carrier S) X) : Product (two_set_carrier S) X
  ≔ (two_set_swap S (u .fst), u .snd)

def dbc_pair_with (A X : Type) (x : X) (a : A) : Product A X ≔ (a, x)

def dbc_b_involutive (S : TwoElementSets) (X : Type) (u : Product (two_set_carrier S) X)
  : Id (Product (two_set_carrier S) X) (dbc_b_map S X (dbc_b_map S X u)) u
  ≔ refl (dbc_pair_with (two_set_carrier S) X (u .snd)) (dbc_swap_swap S (u .fst))

def dbc_b_equiv (S : TwoElementSets) (X : Type) : Equiv (Product (two_set_carrier S) X) (Product (two_set_carrier S) X)
  ≔ quasi_inverse_equiv (Product (two_set_carrier S) X) (Product (two_set_carrier S) X)
      (dbc_b_map S X) (dbc_b_map S X) (dbc_b_involutive S X) (dbc_b_involutive S X)

{` The pieces of φ(x) for x : BD_n. `}
def dbc_carrier (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : SetTypes
  ≔ (Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst),
     product_set (two_set_carrier (x .fst)) (x .snd .fst .fst .fst) (x .fst .fst .snd) (x .snd .fst .fst .snd))

def dbc_a (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Equiv (Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst)) (Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst))
  ≔ dbc_a_equiv (x .fst) (x .snd .fst) (s ↦ dbc_inverse_pair H h x s)

def dbc_b (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Equiv (Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst)) (Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst))
  ≔ dbc_b_equiv (x .fst) (x .snd .fst .fst .fst)

def DihedralBicycleConnected (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : Type
  ≔ BicycleConnected (Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst)) (dbc_a H h x) (dbc_b H h x)

{` The standard dihedral bicycle of degree n: (Z/~_n ⊔ Z/~_n, a, b). `}
def DihedralStandardCarrier (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type
  ≔ Sum (SubgroupQuotient H h) (SubgroupQuotient H h)

def dihedral_standard_a_map (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : DihedralStandardCarrier H h → DihedralStandardCarrier H h
  ≔ [ inl. q ↦ inl. (subgroup_translation H h (pos. (suc. zero.)) q)
    | inr. q ↦ inr. (subgroup_translation H h (neg. zero.) q) ]

def dihedral_standard_a_inverse_map (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : DihedralStandardCarrier H h → DihedralStandardCarrier H h
  ≔ [ inl. q ↦ inl. (subgroup_translation H h (neg. zero.) q)
    | inr. q ↦ inr. (subgroup_translation H h (pos. (suc. zero.)) q) ]

def dihedral_standard_a_retraction (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u : DihedralStandardCarrier H h)
  : Id (DihedralStandardCarrier H h) (dihedral_standard_a_inverse_map H h (dihedral_standard_a_map H h u)) u
  ≔ match u [
  | inl. q ↦ inl. (subgroup_translation_inverse H h (pos. (suc. zero.)) (refl q))
  | inr. q ↦ inr. (subgroup_translation_inverse_other H h (pos. (suc. zero.)) (refl q)) ]

def dihedral_standard_a_section (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u : DihedralStandardCarrier H h)
  : Id (DihedralStandardCarrier H h) (dihedral_standard_a_map H h (dihedral_standard_a_inverse_map H h u)) u
  ≔ match u [
  | inl. q ↦ inl. (subgroup_translation_inverse_other H h (pos. (suc. zero.)) (refl q))
  | inr. q ↦ inr. (subgroup_translation_inverse H h (pos. (suc. zero.)) (refl q)) ]

def dihedral_standard_a (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (DihedralStandardCarrier H h) (DihedralStandardCarrier H h)
  ≔ quasi_inverse_equiv (DihedralStandardCarrier H h) (DihedralStandardCarrier H h)
      (dihedral_standard_a_map H h) (dihedral_standard_a_inverse_map H h)
      (dihedral_standard_a_retraction H h) (dihedral_standard_a_section H h)

def dihedral_standard_b_map (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : DihedralStandardCarrier H h → DihedralStandardCarrier H h
  ≔ [ inl. q ↦ inr. q | inr. q ↦ inl. q ]

def dihedral_standard_b_involutive (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u : DihedralStandardCarrier H h)
  : Id (DihedralStandardCarrier H h) (dihedral_standard_b_map H h (dihedral_standard_b_map H h u)) u
  ≔ match u [
  | inl. q ↦ refl (inl. q : DihedralStandardCarrier H h)
  | inr. q ↦ refl (inr. q : DihedralStandardCarrier H h) ]

def dihedral_standard_b (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (DihedralStandardCarrier H h) (DihedralStandardCarrier H h)
  ≔ quasi_inverse_equiv (DihedralStandardCarrier H h) (DihedralStandardCarrier H h)
      (dihedral_standard_b_map H h) (dihedral_standard_b_map H h)
      (dihedral_standard_b_involutive H h) (dihedral_standard_b_involutive H h)

def dihedral_standard_set (H : Subtypes Int) (h : IntegerSubgroupLaws H) : SetTypes
  ≔ (DihedralStandardCarrier H h,
     sum_set (SubgroupQuotient H h) (SubgroupQuotient H h) (subgroup_quotient_set H h) (subgroup_quotient_set H h))

{` Litmus: the defining equations of the book hold judgmentally on classes. `}
def dihedral_standard_a_litmus (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  : Id (Product (DihedralStandardCarrier H h) (DihedralStandardCarrier H h))
      (dihedral_standard_a (H) h .map (inl. (subgroup_class H h z)), dihedral_standard_a H h .map (inr. (subgroup_class H h z)))
      (inl. (subgroup_class H h (int_add z (pos. (suc. zero.)))), inr. (subgroup_class H h (int_sub z (pos. (suc. zero.)))))
  ≔ refl ((inl. (subgroup_class H h (int_succ z)), inr. (subgroup_class H h (int_pred z)))
          : Product (DihedralStandardCarrier H h) (DihedralStandardCarrier H h))

def dihedral_standard_b_litmus (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  : Id (Product (DihedralStandardCarrier H h) (DihedralStandardCarrier H h))
      (dihedral_standard_b H h .map (inl. (subgroup_class H h z)), dihedral_standard_b H h .map (inr. (subgroup_class H h z)))
      (inr. (subgroup_class H h z), inl. (subgroup_class H h z))
  ≔ refl ((inr. (subgroup_class H h z), inl. (subgroup_class H h z))
          : Product (DihedralStandardCarrier H h) (DihedralStandardCarrier H h))

{` Connectivity: inl [z] = a^z(inl [0]) and inr [z] = b(a^z(inl [0])). `}
def dihedral_standard_power_left (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  : Id (DihedralStandardCarrier H h) (inl. (subgroup_class H h z))
      (permutation_power (DihedralStandardCarrier H h) (dihedral_standard_a H h) z (inl. (subgroup_class H h int_zero)))
  ≔ concat (DihedralStandardCarrier H h) (inl. (subgroup_class H h z))
      (inl. (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) z (subgroup_class H h int_zero)))
      (permutation_power (DihedralStandardCarrier H h) (dihedral_standard_a H h) z (inl. (subgroup_class H h int_zero)))
      (inl. (subgroup_power_zero H h z))
      (permutation_power_intertwine (SubgroupQuotient H h) (DihedralStandardCarrier H h)
        (subgroup_successor H h) (dihedral_standard_a H h) (q ↦ inl. q)
        (q ↦ refl (inl. (subgroup_translation H h (pos. (suc. zero.)) q) : DihedralStandardCarrier H h))
        z (subgroup_class H h int_zero))

def dihedral_standard_word_at (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u : DihedralStandardCarrier H h)
  (z : Int) (side : Id (DihedralStandardCarrier H h) u (inl. (subgroup_class H h z)))
  : Product (BicycleWordFrom (DihedralStandardCarrier H h) (dihedral_standard_a H h) (dihedral_standard_b H h)
              (inl. (subgroup_class H h int_zero)) u)
            (BicycleWordFrom (DihedralStandardCarrier H h) (dihedral_standard_a H h) (dihedral_standard_b H h)
              (inl. (subgroup_class H h int_zero)) (dihedral_standard_b_map H h u))
  ≔ let p : Id (DihedralStandardCarrier H h) u
              (permutation_power (DihedralStandardCarrier H h) (dihedral_standard_a H h) z (inl. (subgroup_class H h int_zero)))
          ≔ concat (DihedralStandardCarrier H h) u (inl. (subgroup_class H h z))
              (permutation_power (DihedralStandardCarrier H h) (dihedral_standard_a H h) z (inl. (subgroup_class H h int_zero)))
              side (dihedral_standard_power_left H h z) in
    ((cons. (inl. z) nil., p),
     (cons. (inr. (pos. (suc. zero.))) (cons. (inl. z) nil.), refl (dihedral_standard_b_map H h) p))

def dihedral_standard_word_from_origin (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u : DihedralStandardCarrier H h)
  : Mere (BicycleWordFrom (DihedralStandardCarrier H h) (dihedral_standard_a H h) (dihedral_standard_b H h)
      (inl. (subgroup_class H h int_zero)) u)
  ≔ let W : DihedralStandardCarrier H h → Type
          ≔ v ↦ BicycleWordFrom (DihedralStandardCarrier H h) (dihedral_standard_a H h) (dihedral_standard_b H h)
              (inl. (subgroup_class H h int_zero)) v in
    match u [
    | inl. q ↦ mere_rec (BookFiber Int (SubgroupQuotient H h) (subgroup_class H h) q) (Mere (W (inl. q)))
        (mere_isprop (W (inl. q)))
        (w ↦ mere (W (inl. q)) (dihedral_standard_word_at H h (inl. q) (w .fst) (inl. (w .snd)) .fst))
        (quotient_surjective Int (subgroup_relation H h) q)
    | inr. q ↦ mere_rec (BookFiber Int (SubgroupQuotient H h) (subgroup_class H h) q) (Mere (W (inr. q)))
        (mere_isprop (W (inr. q)))
        (w ↦ mere (W (inr. q)) (dihedral_standard_word_at H h (inl. q) (w .fst) (inl. (w .snd)) .snd))
        (quotient_surjective Int (subgroup_relation H h) q) ]

def dihedral_standard_connected (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : BicycleConnected (DihedralStandardCarrier H h) (dihedral_standard_a H h) (dihedral_standard_b H h)
  ≔ bicycle_connected_from_point (DihedralStandardCarrier H h) (dihedral_standard_a H h) (dihedral_standard_b H h)
      (inl. (subgroup_class H h int_zero)) (dihedral_standard_word_from_origin H h)

{` The standard dihedral bicycle of degree n (for H = order_periods n). `}
def dihedral_standard_bicycle (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Bicycles
  ≔ mkbicycle (dihedral_standard_set H h) (dihedral_standard_a H h) (dihedral_standard_b H h)
      (dihedral_standard_connected H h)

def standard_dihedral_bicycle (n : Order) : Bicycles
  ≔ dihedral_standard_bicycle (order_periods n) (order_subgroup_laws n)

{` The identification of φ(sh) with the standard bicycle. X₀ = X_{Fin 2},
   ι = dihedral_insert at yes, ev = dihedral_eval at yes. `}
def DihedralBaseSet (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type ≔ DihedralCycleSet dihedral_two_shape H h

def DihedralBaseProduct (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type
  ≔ Product (two_set_carrier dihedral_two_shape) (DihedralBaseSet H h)

def dihedral_base_iso_map (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : DihedralStandardCarrier H h → DihedralBaseProduct H h
  ≔ [ inl. q ↦ (s2c3_fin2_yes, dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q)
    | inr. q ↦ (s2c3_fin2_no, dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q) ]

def dbc_side (Q : Type) (s : Fin two) (q : Q) : Sum Q Q
  ≔ match s [ inr. _ ↦ inl. q | inl. (inr. _) ↦ inr. q | inl. (inl. e) ↦ match e [] ]

def dihedral_base_iso_inverse (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u : DihedralBaseProduct H h)
  : DihedralStandardCarrier H h
  ≔ dbc_side (SubgroupQuotient H h) (u .fst) (dihedral_eval dihedral_two_shape H h s2c3_fin2_yes (u .snd))

def dihedral_base_iso_retraction (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u : DihedralStandardCarrier H h)
  : Id (DihedralStandardCarrier H h) (dihedral_base_iso_inverse H h (dihedral_base_iso_map H h u)) u
  ≔ match u [
  | inl. q ↦ inl. (dihedral_eval_insert dihedral_two_shape H h s2c3_fin2_yes q)
  | inr. q ↦ inr. (dihedral_eval_insert dihedral_two_shape H h s2c3_fin2_yes q) ]

def dihedral_base_iso_section_at (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : Fin two) (x : DihedralBaseSet H h)
  : Id (DihedralBaseProduct H h) (dihedral_base_iso_map H h (dihedral_base_iso_inverse H h (s, x))) (s, x)
  ≔ match s [
  | inr. star. ↦ refl (dbc_pair_at (Fin two) (DihedralBaseSet H h) s2c3_fin2_yes)
      (dihedral_insert_eval dihedral_two_shape H h s2c3_fin2_yes x)
  | inl. (inr. star.) ↦ refl (dbc_pair_at (Fin two) (DihedralBaseSet H h) s2c3_fin2_no)
      (dihedral_insert_eval dihedral_two_shape H h s2c3_fin2_yes x)
  | inl. (inl. e) ↦ match e [] ]

def dihedral_base_iso_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (DihedralStandardCarrier H h) (DihedralBaseProduct H h)
  ≔ quasi_inverse_equiv (DihedralStandardCarrier H h) (DihedralBaseProduct H h)
      (dihedral_base_iso_map H h) (dihedral_base_iso_inverse H h)
      (dihedral_base_iso_retraction H h) (u ↦ dihedral_base_iso_section_at H h (u .fst) (u .snd))

{` ι(q + 1) = f_yes(ι q) and ι(q − 1) = f_no(ι q). `}
def dihedral_insert_succ (H : Subtypes Int) (h : IntegerSubgroupLaws H) (q : SubgroupQuotient H h)
  : Id (DihedralBaseSet H h)
      (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes (subgroup_translation H h (pos. (suc. zero.)) q))
      (dihedral_move dihedral_two_shape H h s2c3_fin2_yes (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q))
  ≔ quotient_prop_induction Int (subgroup_relation H h)
      (q ↦ Id (DihedralBaseSet H h)
        (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes (subgroup_translation H h (pos. (suc. zero.)) q))
        (dihedral_move dihedral_two_shape H h s2c3_fin2_yes (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q)))
      (q ↦ dihedral_cycle_set_set dihedral_two_shape H h
        (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes (subgroup_translation H h (pos. (suc. zero.)) q))
        (dihedral_move dihedral_two_shape H h s2c3_fin2_yes (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q)))
      (z ↦ inverse (DihedralBaseSet H h)
        (dihedral_move dihedral_two_shape H h s2c3_fin2_yes (dihedral_class dihedral_two_shape H h s2c3_fin2_yes z))
        (dihedral_class dihedral_two_shape H h s2c3_fin2_yes (int_succ z))
        (dihedral_move_self dihedral_two_shape H h s2c3_fin2_yes z))
      q

def dihedral_insert_pred (H : Subtypes Int) (h : IntegerSubgroupLaws H) (q : SubgroupQuotient H h)
  : Id (DihedralBaseSet H h)
      (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes (subgroup_translation H h (neg. zero.) q))
      (dihedral_move dihedral_two_shape H h s2c3_fin2_no (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q))
  ≔ quotient_prop_induction Int (subgroup_relation H h)
      (q ↦ Id (DihedralBaseSet H h)
        (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes (subgroup_translation H h (neg. zero.) q))
        (dihedral_move dihedral_two_shape H h s2c3_fin2_no (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q)))
      (q ↦ dihedral_cycle_set_set dihedral_two_shape H h
        (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes (subgroup_translation H h (neg. zero.) q))
        (dihedral_move dihedral_two_shape H h s2c3_fin2_no (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q)))
      (z ↦ inverse (DihedralBaseSet H h)
        (dihedral_move dihedral_two_shape H h s2c3_fin2_no (dihedral_class dihedral_two_shape H h s2c3_fin2_yes z))
        (dihedral_class dihedral_two_shape H h s2c3_fin2_yes (int_pred z))
        (dihedral_move_other dihedral_two_shape H h s2c3_fin2_no s2c3_fin2_yes s2c3_fin2_yes_not_no z))
      q

def dihedral_base_iso_commutes_a (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Commutes (DihedralStandardCarrier H h) (DihedralBaseProduct H h) (dihedral_standard_a H h)
      (dbc_a H h (dihedral_classifying_base H h)) (dihedral_base_iso_map H h)
  ≔ [ inl. q ↦ refl (dbc_pair_at (Fin two) (DihedralBaseSet H h) s2c3_fin2_yes) (dihedral_insert_succ H h q)
    | inr. q ↦ refl (dbc_pair_at (Fin two) (DihedralBaseSet H h) s2c3_fin2_no) (dihedral_insert_pred H h q) ]

def dihedral_base_iso_commutes_b (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Commutes (DihedralStandardCarrier H h) (DihedralBaseProduct H h) (dihedral_standard_b H h)
      (dbc_b H h (dihedral_classifying_base H h)) (dihedral_base_iso_map H h)
  ≔ [ inl. q ↦ refl (dbc_pair_with (Fin two) (DihedralBaseSet H h) (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q))
        (two_set_other_is_swap dihedral_two_shape s2c3_fin2_yes s2c3_fin2_no s2c3_fin2_no_not_yes)
    | inr. q ↦ refl (dbc_pair_with (Fin two) (DihedralBaseSet H h) (dihedral_insert dihedral_two_shape H h s2c3_fin2_yes q))
        (two_set_other_is_swap dihedral_two_shape s2c3_fin2_no s2c3_fin2_yes s2c3_fin2_yes_not_no) ]

{` Connectivity of φ(x): at the base point by transfer from the standard
   bicycle, everywhere by connectedness of BD_n. `}
def dihedral_base_bicycle_connected (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : DihedralBicycleConnected H h (dihedral_classifying_base H h)
  ≔ bicycle_connected_transfer (DihedralStandardCarrier H h) (DihedralBaseProduct H h)
      (dihedral_standard_a H h) (dihedral_standard_b H h)
      (dbc_a H h (dihedral_classifying_base H h)) (dbc_b H h (dihedral_classifying_base H h))
      (dihedral_base_iso_equiv H h) (dihedral_base_iso_commutes_a H h) (dihedral_base_iso_commutes_b H h)
      (dihedral_standard_connected H h)

def dihedral_phi_connected (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : DihedralBicycleConnected H h x
  ≔ mere_transport native_truncation (DihedralClassifyingType H h) (DihedralBicycleConnected H h)
      (y ↦ bicycle_connected_prop (Product (two_set_carrier (y .fst)) (y .snd .fst .fst .fst)) (dbc_a H h y) (dbc_b H h y))
      (dihedral_classifying_base H h) x
      (dihedral_classifying_connected H h .snd (dihedral_classifying_base H h) x)
      (dihedral_base_bicycle_connected H h)

{` φ(S, X, f) ≔ (S × X, a, b). `}
def dihedral_bicycle (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : Bicycles
  ≔ mkbicycle (dbc_carrier H h x) (dbc_a H h x) (dbc_b H h x) (dihedral_phi_connected H h x)

{` Litmus: a(s, x) = (s, f_s x), b(s, x) = (swap s, x) judgmentally. `}
def dihedral_bicycle_a_litmus (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (s : two_set_carrier (x .fst)) (y : x .snd .fst .fst .fst)
  : Id (Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst)) (bicycle_a (dihedral_bicycle H h x) .map (s, y))
      (s, x .snd .fst .snd s y)
  ≔ refl ((s, x .snd .fst .snd s y) : Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst))

def dihedral_bicycle_b_litmus (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (s : two_set_carrier (x .fst)) (y : x .snd .fst .fst .fst)
  : Id (Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst)) (bicycle_b (dihedral_bicycle H h x) .map (s, y))
      (two_set_swap (x .fst) s, y)
  ≔ refl ((two_set_swap (x .fst) s, y) : Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst))

{` φ(sh) is isomorphic to, hence identified with, the standard bicycle. `}
def dihedral_bicycle_base_iso (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : BicycleIsomorphisms (dihedral_standard_bicycle H h) (dihedral_bicycle H h (dihedral_classifying_base H h))
  ≔ (dihedral_base_iso_equiv H h, (dihedral_base_iso_commutes_a H h, dihedral_base_iso_commutes_b H h))

def dihedral_bicycle_base_path (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Id Bicycles (dihedral_standard_bicycle H h) (dihedral_bicycle H h (dihedral_classifying_base H h))
  ≔ bicycle_path_from_iso (dihedral_standard_bicycle H h) (dihedral_bicycle H h (dihedral_classifying_base H h))
      (dihedral_bicycle_base_iso H h)

{` The component of Bicyc at the standard dihedral bicycle, and φ as a map
   into it. `}
def DihedralBicycleComponent (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type
  ≔ NativeComponent Bicycles (dihedral_standard_bicycle H h)

def dihedral_bicycle_mere_path (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Mere (Id Bicycles (dihedral_standard_bicycle H h) (dihedral_bicycle H h x))
  ≔ mere_rec (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) x)
      (Mere (Id Bicycles (dihedral_standard_bicycle H h) (dihedral_bicycle H h x)))
      (mere_isprop (Id Bicycles (dihedral_standard_bicycle H h) (dihedral_bicycle H h x)))
      (p ↦ mere (Id Bicycles (dihedral_standard_bicycle H h) (dihedral_bicycle H h x))
        (concat Bicycles (dihedral_standard_bicycle H h) (dihedral_bicycle H h (dihedral_classifying_base H h))
          (dihedral_bicycle H h x) (dihedral_bicycle_base_path H h) (refl (dihedral_bicycle H h) p)))
      (dihedral_classifying_connected H h .snd (dihedral_classifying_base H h) x)

def dihedral_bicycle_map (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : DihedralBicycleComponent H h
  ≔ (dihedral_bicycle H h x, dihedral_bicycle_mere_path H h x)

def dihedral_bicycle_map_point (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Id (DihedralBicycleComponent H h) (component_point Bicycles (dihedral_standard_bicycle H h))
      (dihedral_bicycle_map H h (dihedral_classifying_base H h))
  ≔ subtype_equal Bicycles (B ↦ Mere (Id Bicycles (dihedral_standard_bicycle H h) B))
      (B ↦ mere_isprop (Id Bicycles (dihedral_standard_bicycle H h) B))
      (component_point Bicycles (dihedral_standard_bicycle H h)) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
      (dihedral_bicycle_base_path H h)

{` φ as a pointed map BD_n →* Bicyc_(standard) (book convention pt = φ(pt)). `}
def dihedral_bicycle_pointed_map (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : BookPointedMap (DihedralClassifyingType H h, dihedral_classifying_base H h)
      (DihedralBicycleComponent H h, component_point Bicycles (dihedral_standard_bicycle H h))
  ≔ (dihedral_bicycle_map H h, dihedral_bicycle_map_point H h)
