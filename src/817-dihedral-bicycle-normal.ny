export "816-dihedral-bicycle-loops"

{` congp.tex 191-193: "since we easily verify that the standard dihedral
   bicycles are normal (def:normal-bicycle), we see that if n is finite, then
   D_n has the same cardinality as n ⊔ n".

   The symmetries used: rotations R_k (inl [r] ↦ inl [r+k], inr [r] ↦ inr [r+k])
   and reflections T_k (inl [r] ↦ inr [k−r], inr [r] ↦ inl [k−r]); R_k sends
   inl [0] to inl [k] and T_k sends inl [0] to inr [k], so every element is
   reached from inl [0] and the bicycle is normal
   (normal_bicycle_from_point_surjective, xca:normal-bicycle-equiv).
   Through φ (module 816), USym D_n ≃ (B = B) ≃ Z/~n ⊔ Z/~n for the standard
   dihedral bicycle B (evaluation at inl [0]); for finite n this has 2n elements
   (module 808 computes |D_n| = 2n directly). As a by-product, D_n is
   isomorphic to Aut_Bicyc of its standard dihedral bicycle. `}

{` Negation on Z/~n. `}
def dbn_negation (H : Subtypes Int) (h : IntegerSubgroupLaws H) : SubgroupQuotient H h → SubgroupQuotient H h
  ≔ quotient_rec Int (SubgroupQuotient H h) (subgroup_relation H h) (subgroup_quotient_set H h)
      (r ↦ subgroup_class H h (int_neg r))
      (x y p ↦ quotient_encode Int (subgroup_relation H h) (int_neg x) (int_neg y)
        (refl (SubgroupMember H) (int_neg_additive x (int_neg y)) .trr (h .snd .snd (int_sub x y) p)))

{` (r + c) + k = (r + k) + c and -(r + c) + k = (-r + k) + (-c). `}
def dbn_int_swap (r c k : Int) : Id Int (int_add (int_add r c) k) (int_add (int_add r k) c)
  ≔ calc
      int_add (int_add r c) k = int_add r (int_add c k) by int_add_assoc r c k
      = int_add r (int_add k c) by refl (int_add r) (int_add_comm c k)
      = int_add (int_add r k) c by inverse Int (int_add (int_add r k) c) (int_add r (int_add k c)) (int_add_assoc r k c) ∎

def dbn_int_reflect (r c k : Int)
  : Id Int (int_add (int_neg (int_add r c)) k) (int_add (int_add (int_neg r) k) (int_neg c))
  ≔ calc
      int_add (int_neg (int_add r c)) k = int_add (int_add (int_neg r) (int_neg c)) k
        by refl ((z ↦ int_add z k) : Int → Int) (int_neg_additive r c)
      = int_add (int_add (int_neg r) k) (int_neg c) by dbn_int_swap (int_neg r) (int_neg c) k ∎

def dbn_int_reflect_twice (r k : Int) : Id Int (int_add (int_neg (int_add (int_neg r) k)) k) r
  ≔ calc
      int_add (int_neg (int_add (int_neg r) k)) k = int_add (int_add (int_neg (int_neg r)) (int_neg k)) k
        by refl ((z ↦ int_add z k) : Int → Int) (int_neg_additive (int_neg r) k)
      = int_add (int_add r (int_neg k)) k by refl ((z ↦ int_add (int_add z (int_neg k)) k) : Int → Int) (int_neg_neg r)
      = r by int_sub_add r k ∎

{` Rotations. `}
def dbn_rotation_map (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int)
  : DihedralStandardCarrier H h → DihedralStandardCarrier H h
  ≔ [ inl. q ↦ inl. (subgroup_translation H h k q) | inr. q ↦ inr. (subgroup_translation H h k q) ]

def dbn_rotation_retraction (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int) (u : DihedralStandardCarrier H h)
  : Id (DihedralStandardCarrier H h) (dbn_rotation_map H h (int_neg k) (dbn_rotation_map H h k u)) u
  ≔ match u [
  | inl. q ↦ inl. (subgroup_translation_inverse H h k (refl q))
  | inr. q ↦ inr. (subgroup_translation_inverse H h k (refl q)) ]

def dbn_rotation_section (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int) (u : DihedralStandardCarrier H h)
  : Id (DihedralStandardCarrier H h) (dbn_rotation_map H h k (dbn_rotation_map H h (int_neg k) u)) u
  ≔ match u [
  | inl. q ↦ inl. (subgroup_translation_inverse_other H h k (refl q))
  | inr. q ↦ inr. (subgroup_translation_inverse_other H h k (refl q)) ]

def dbn_translations_commute (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c k : Int) (q : SubgroupQuotient H h)
  : Id (SubgroupQuotient H h) (subgroup_translation H h k (subgroup_translation H h c q))
      (subgroup_translation H h c (subgroup_translation H h k q))
  ≔ quotient_prop_induction Int (subgroup_relation H h)
      (q ↦ Id (SubgroupQuotient H h) (subgroup_translation H h k (subgroup_translation H h c q))
        (subgroup_translation H h c (subgroup_translation H h k q)))
      (q ↦ subgroup_quotient_set H h (subgroup_translation H h k (subgroup_translation H h c q))
        (subgroup_translation H h c (subgroup_translation H h k q)))
      (r ↦ refl (subgroup_class H h) (dbn_int_swap r c k)) q

def dbn_rotation (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int)
  : BicycleIsomorphisms (dihedral_standard_bicycle H h) (dihedral_standard_bicycle H h)
  ≔ (quasi_inverse_equiv (DihedralStandardCarrier H h) (DihedralStandardCarrier H h)
       (dbn_rotation_map H h k) (dbn_rotation_map H h (int_neg k)) (dbn_rotation_retraction H h k) (dbn_rotation_section H h k),
     ([ inl. q ↦ inl. (dbn_translations_commute H h (pos. (suc. zero.)) k q)
      | inr. q ↦ inr. (dbn_translations_commute H h (neg. zero.) k q) ],
      [ inl. q ↦ refl (inr. (subgroup_translation H h k q) : DihedralStandardCarrier H h)
      | inr. q ↦ refl (inl. (subgroup_translation H h k q) : DihedralStandardCarrier H h) ]))

{` Reflections. `}
def dbn_reflect (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int) (q : SubgroupQuotient H h) : SubgroupQuotient H h
  ≔ subgroup_translation H h k (dbn_negation H h q)

def dbn_reflection_map (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int)
  : DihedralStandardCarrier H h → DihedralStandardCarrier H h
  ≔ [ inl. q ↦ inr. (dbn_reflect H h k q) | inr. q ↦ inl. (dbn_reflect H h k q) ]

def dbn_reflect_twice (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int) (q : SubgroupQuotient H h)
  : Id (SubgroupQuotient H h) (dbn_reflect H h k (dbn_reflect H h k q)) q
  ≔ quotient_prop_induction Int (subgroup_relation H h)
      (q ↦ Id (SubgroupQuotient H h) (dbn_reflect H h k (dbn_reflect H h k q)) q)
      (q ↦ subgroup_quotient_set H h (dbn_reflect H h k (dbn_reflect H h k q)) q)
      (r ↦ refl (subgroup_class H h) (dbn_int_reflect_twice r k)) q

def dbn_reflection_involutive (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int) (u : DihedralStandardCarrier H h)
  : Id (DihedralStandardCarrier H h) (dbn_reflection_map H h k (dbn_reflection_map H h k u)) u
  ≔ match u [
  | inl. q ↦ inl. (dbn_reflect_twice H h k q)
  | inr. q ↦ inr. (dbn_reflect_twice H h k q) ]

def dbn_reflect_step (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c k : Int) (q : SubgroupQuotient H h)
  : Id (SubgroupQuotient H h) (dbn_reflect H h k (subgroup_translation H h c q))
      (subgroup_translation H h (int_neg c) (dbn_reflect H h k q))
  ≔ quotient_prop_induction Int (subgroup_relation H h)
      (q ↦ Id (SubgroupQuotient H h) (dbn_reflect H h k (subgroup_translation H h c q))
        (subgroup_translation H h (int_neg c) (dbn_reflect H h k q)))
      (q ↦ subgroup_quotient_set H h (dbn_reflect H h k (subgroup_translation H h c q))
        (subgroup_translation H h (int_neg c) (dbn_reflect H h k q)))
      (r ↦ refl (subgroup_class H h) (dbn_int_reflect r c k)) q

def dbn_reflection (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : Int)
  : BicycleIsomorphisms (dihedral_standard_bicycle H h) (dihedral_standard_bicycle H h)
  ≔ (quasi_inverse_equiv (DihedralStandardCarrier H h) (DihedralStandardCarrier H h)
       (dbn_reflection_map H h k) (dbn_reflection_map H h k) (dbn_reflection_involutive H h k) (dbn_reflection_involutive H h k),
     ([ inl. q ↦ inr. (dbn_reflect_step H h (pos. (suc. zero.)) k q)
      | inr. q ↦ inl. (dbn_reflect_step H h (neg. zero.) k q) ],
      [ inl. q ↦ refl (inl. (dbn_reflect H h k q) : DihedralStandardCarrier H h)
      | inr. q ↦ refl (inr. (dbn_reflect H h k q) : DihedralStandardCarrier H h) ]))

{` Every element is reached from inl [0] by a symmetry. `}
def dbn_reach (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u : DihedralStandardCarrier H h)
  : Mere (BookFiber (Id Bicycles (dihedral_standard_bicycle H h) (dihedral_standard_bicycle H h)) (DihedralStandardCarrier H h)
      (bicycle_evaluation (dihedral_standard_bicycle H h) (inl. (subgroup_class H h int_zero))) u)
  ≔ let B ≔ dihedral_standard_bicycle H h in
    let F : DihedralStandardCarrier H h → Type
          ≔ v ↦ BookFiber (Id Bicycles B B) (DihedralStandardCarrier H h)
              (bicycle_evaluation B (inl. (subgroup_class H h int_zero))) v in
    match u [
    | inl. q ↦ mere_rec (BookFiber Int (SubgroupQuotient H h) (subgroup_class H h) q) (Mere (F (inl. q))) (mere_isprop (F (inl. q)))
        (w ↦ mere (F (inl. q)) (bicycle_path_from_iso B B (dbn_rotation H h (w .fst)),
          inl. (concat (SubgroupQuotient H h) q (subgroup_class H h (w .fst)) (subgroup_class H h (int_add int_zero (w .fst)))
            (w .snd) (refl (subgroup_class H h) (inverse Int (int_add int_zero (w .fst)) (w .fst) (int_add_zero_left (w .fst)))))))
        (quotient_surjective Int (subgroup_relation H h) q)
    | inr. q ↦ mere_rec (BookFiber Int (SubgroupQuotient H h) (subgroup_class H h) q) (Mere (F (inr. q))) (mere_isprop (F (inr. q)))
        (w ↦ mere (F (inr. q)) (bicycle_path_from_iso B B (dbn_reflection H h (w .fst)),
          inr. (concat (SubgroupQuotient H h) q (subgroup_class H h (w .fst)) (subgroup_class H h (int_add int_zero (w .fst)))
            (w .snd) (refl (subgroup_class H h) (inverse Int (int_add int_zero (w .fst)) (w .fst) (int_add_zero_left (w .fst)))))))
        (quotient_surjective Int (subgroup_relation H h) q) ]

{` "The standard dihedral bicycles are normal." `}
def dihedral_standard_bicycle_normal (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : IsNormalBicycle (dihedral_standard_bicycle H h)
  ≔ normal_bicycle_from_point_surjective (dihedral_standard_bicycle H h) (inl. (subgroup_class H h int_zero)) (dbn_reach H h)

def standard_dihedral_bicycle_normal (n : Order) : IsNormalBicycle (standard_dihedral_bicycle n)
  ≔ dihedral_standard_bicycle_normal (order_periods n) (order_subgroup_laws n)

{` USym D_n ≃ Z/~n ⊔ Z/~n (so |D_n| = |n ⊔ n|): Ωφ, then conjugation by
   the identification of φ(sh) with the standard bicycle B, then evaluation
   at inl [0] (B is normal). `}
def dihedral_loops_standard_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
      (DihedralStandardCarrier H h)
  ≔ let L ≔ Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h) in
    let B0 ≔ dbl_bicycle H h in
    let B ≔ dihedral_standard_bicycle H h in
    let P0 ≔ inverse Bicycles B B0 (dihedral_bicycle_base_path H h) in
    compose_equiv L (Id Bicycles B0 B0) (DihedralStandardCarrier H h)
      (compose_equiv L (BicycleIsomorphisms B0 B0) (Id Bicycles B0 B0) (dihedral_loops_bicycle_isos_equiv H h)
        (canonical_inverse_equiv (Id Bicycles B0 B0) (BicycleIsomorphisms B0 B0) (bicycle_paths_equiv B0 B0)))
      (compose_equiv (Id Bicycles B0 B0) (Id Bicycles B B) (DihedralStandardCarrier H h)
        (dbc_path_endpoints_equiv Bicycles B0 B P0 B0 B P0)
        (native_equivalence (Id Bicycles B B) (DihedralStandardCarrier H h)
          (bicycle_evaluation_equiv B (dihedral_standard_bicycle_normal H h) (inl. (subgroup_class H h int_zero)))))

def generalized_dihedral_usym_standard_equiv (n : Order)
  : Equiv (USym (generalized_dihedral_group n)) (Sum (SubgroupQuotient (order_periods n) (order_subgroup_laws n))
      (SubgroupQuotient (order_periods n) (order_subgroup_laws n)))
  ≔ dihedral_loops_standard_equiv (order_periods n) (order_subgroup_laws n)

{` D_n ≅ Aut_Bicyc(standard dihedral bicycle of degree n): the pointed
   equivalence of con:bidirectional-bicycle as a group isomorphism. `}
def dihedral_bicycle_group_iso (n : Order)
  : GroupIso (generalized_dihedral_group n) (bicycle_automorphism_group (standard_dihedral_bicycle n))
  ≔ book_pointed_equiv_group_iso_equiv (generalized_dihedral_group n) (bicycle_automorphism_group (standard_dihedral_bicycle n))
      .map (bidirectional_bicycle_pointed_equiv n)

{` congp.tex 103-108 ("remedy the potential clash with def:Dinfty-Q"): for the
   infinite order the standard dihedral bicycle is the infinite dihedral
   bicycle (Z ⊔ Z, a, b) of chapter 4 (Z/~∞ ≅ Z, the only period of the infinite
   cycle being 0), so D_∞ of def:gen-dihedral is identified with
   D_∞ = Aut_Bicyc(Z ⊔ Z, a, b) of def:Dinfty-Q. `}
def dbn_infinite_member_zero (n : Int) (m : SubgroupMember (order_periods infinite_order) n) : Id Int n int_zero
  ≔ concat Int n (int_add int_zero n) int_zero (inverse Int (int_add int_zero n) n (int_add_zero_left n)) (m (refl int_zero))

def DbnInfiniteQuotient : Type ≔ SubgroupQuotient (order_periods infinite_order) (order_subgroup_laws infinite_order)

def dbn_infinite_quotient_equiv : Equiv DbnInfiniteQuotient Int
  ≔ let H ≔ order_periods infinite_order in
    let h ≔ order_subgroup_laws infinite_order in
    quotient_presentation_equiv Int Int (subgroup_relation H h) int_set (z ↦ z)
      (x y r ↦ calc
        x = int_add (int_sub x y) y by inverse Int (int_add (int_sub x y) y) x (int_sub_add x y)
        = int_add int_zero y by refl ((z ↦ int_add z y) : Int → Int) (dbn_infinite_member_zero (int_sub x y) r)
        = y by int_add_zero_left y ∎)
      (x y q ↦ transport Int (z ↦ SubgroupMember H (int_sub x z)) x y q (subgroup_relation H h .reflexive x))
      (z ↦ mere (BookFiber Int Int (w ↦ w) z) (z, refl z))

def dbn_infinite_class_section (q : DbnInfiniteQuotient)
  : Id DbnInfiniteQuotient (subgroup_class (order_periods infinite_order) (order_subgroup_laws infinite_order)
      (dbn_infinite_quotient_equiv .map q)) q
  ≔ quotient_prop_induction Int (subgroup_relation (order_periods infinite_order) (order_subgroup_laws infinite_order))
      (q ↦ Id DbnInfiniteQuotient (subgroup_class (order_periods infinite_order) (order_subgroup_laws infinite_order)
        (dbn_infinite_quotient_equiv .map q)) q)
      (q ↦ subgroup_quotient_set (order_periods infinite_order) (order_subgroup_laws infinite_order)
        (subgroup_class (order_periods infinite_order) (order_subgroup_laws infinite_order) (dbn_infinite_quotient_equiv .map q)) q)
      (z ↦ refl (subgroup_class (order_periods infinite_order) (order_subgroup_laws infinite_order) z)) q

def dbn_infinite_map : Sum Int Int → Sum DbnInfiniteQuotient DbnInfiniteQuotient
  ≔ [ inl. z ↦ inl. (subgroup_class (order_periods infinite_order) (order_subgroup_laws infinite_order) z)
    | inr. z ↦ inr. (subgroup_class (order_periods infinite_order) (order_subgroup_laws infinite_order) z) ]

def dbn_infinite_inverse : Sum DbnInfiniteQuotient DbnInfiniteQuotient → Sum Int Int
  ≔ [ inl. q ↦ inl. (dbn_infinite_quotient_equiv .map q) | inr. q ↦ inr. (dbn_infinite_quotient_equiv .map q) ]

def dbn_infinite_iso : BicycleIsomorphisms infinite_dihedral_bicycle (standard_dihedral_bicycle infinite_order)
  ≔ (quasi_inverse_equiv (Sum Int Int) (Sum DbnInfiniteQuotient DbnInfiniteQuotient) dbn_infinite_map dbn_infinite_inverse
       [ inl. z ↦ refl (inl. z : Sum Int Int) | inr. z ↦ refl (inr. z : Sum Int Int) ]
       [ inl. q ↦ inl. (dbn_infinite_class_section q) | inr. q ↦ inr. (dbn_infinite_class_section q) ],
     ([ inl. z ↦ refl (dbn_infinite_map (inl. (int_succ z))) | inr. z ↦ refl (dbn_infinite_map (inr. (int_pred z))) ],
      [ inl. z ↦ refl (dbn_infinite_map (inr. z)) | inr. z ↦ refl (dbn_infinite_map (inl. z)) ]))

def infinite_standard_dihedral_bicycle_path : Id Bicycles infinite_dihedral_bicycle (standard_dihedral_bicycle infinite_order)
  ≔ bicycle_path_from_iso infinite_dihedral_bicycle (standard_dihedral_bicycle infinite_order) dbn_infinite_iso

{` D_∞ (def:gen-dihedral, infinite order) = D_∞ (def:Dinfty-Q). `}
def generalized_dihedral_infinite_path : Id Group (generalized_dihedral_group infinite_order) infinite_dihedral_group
  ≔ concat Group (generalized_dihedral_group infinite_order) (bicycle_automorphism_group (standard_dihedral_bicycle infinite_order))
      infinite_dihedral_group
      (group_path_from_iso (generalized_dihedral_group infinite_order) (bicycle_automorphism_group (standard_dihedral_bicycle infinite_order))
        (dihedral_bicycle_group_iso infinite_order))
      (automorphism_group_point_path Bicycles bicycles_groupoid (standard_dihedral_bicycle infinite_order) infinite_dihedral_bicycle
        (inverse Bicycles infinite_dihedral_bicycle (standard_dihedral_bicycle infinite_order) infinite_standard_dihedral_bicycle_path))
