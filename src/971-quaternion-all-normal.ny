export "970-conjugation-closed-subgroups"
export "812-dihedral-quaternion"

{` Chapter 9 (subgroups.tex), rem:typeofsubgpstrivifab (line 1268), part
   (c): the remark claims that Mono(G) (equivalently the abstr(G)-set of
   lem:conj-abstract) is trivial if and only if G is abelian. The direction
   "abelian ⇒ trivial" is module 970. The converse is FALSE: Mono(G) is
   trivial exactly when every subgroup of G is normal, and the quaternion
   group Q_8 (chapter 4's quaternion_group, Aut of the quaternion bicycle)
   is a non-abelian group all of whose subgroups are normal.

   Proof: symmetries of Q_8 are determined by their value at 0 in Fin 8
   (quaternion_eval, module 812), and the value of a product is computed
   by q8_mul from the values of the factors (quaternion_eval_usym_mul).
   The 64 cases of the multiplication table (q8_table, by computation)
   show that for all g, k either gk = kg or k(gk) = g, i.e. g k g⁻¹ is k
   or k⁻¹ (q8_conj_cases). Since the symmetries of a subgroup are closed
   under inverses, every subgroup is closed under conjugation, hence
   normal (module 970). Q_8 is not abelian: (ij)(0) = 7, (ji)(0) = 3. `}

{` The value of a product: (g · k)(0) = ⟦w_{k(0)}⟧(g(0)) where w_y is the
   word reaching y from 0 (quaternion_word_from_zero). `}
def q8_mul (x y : Fin eight) : Fin eight
  ≔ bicycle_meaning (Fin eight) quaternion_a_equiv quaternion_b_equiv (quaternion_word_from_zero y .fst) .map x

def quaternion_eval_usym_mul (g k : USym quaternion_group)
  : Id (Fin eight) (quaternion_eval (usym_mul quaternion_group g k)) (q8_mul (quaternion_eval g) (quaternion_eval k))
  ≔ let qb ≔ quaternion_bicycle in
    let ev ≔ bicycle_path_evaluate qb qb in
    let y ≔ quaternion_eval k in
    let w ≔ quaternion_word_from_zero y in
    calc
      quaternion_eval (usym_mul quaternion_group g k)
      = ev (concat Bicycles qb qb qb (k .fst) (g .fst)) quaternion_zero
        by refl ((p ↦ ev p quaternion_zero) : Id Bicycles qb qb → Fin eight)
             (map_path_concat (NativeComponent Bicycles qb) Bicycles (u ↦ u .fst)
               (component_point Bicycles qb) (component_point Bicycles qb) (component_point Bicycles qb) k g)
      = ev (g .fst) y by bicycle_path_evaluate_concat qb qb qb (k .fst) (g .fst) quaternion_zero
      = ev (g .fst) (bicycle_meaning (Fin eight) quaternion_a_equiv quaternion_b_equiv (w .fst) .map quaternion_zero)
        by refl (ev (g .fst)) (w .snd)
      = q8_mul (quaternion_eval g) y by bicycle_path_evaluate_meaning qb qb (g .fst) (w .fst) quaternion_zero ∎

{` The multiplication table of Q_8 on values at 0: for all x, y either
   xy = yx or y(xy) = x (64 cases by computation). `}
def q8_table (x y : Fin eight)
  : Sum (Id (Fin eight) (q8_mul x y) (q8_mul y x)) (Id (Fin eight) (q8_mul y (q8_mul x y)) x)
  ≔ match x [
  | inr. star. ↦ match y [
    | inr. star. ↦ inl. (refl (inr. star. : Fin eight))
    | inl. (inr. star.) ↦ inl. (refl (inl. (inr. star.) : Fin eight))
    | inl. (inl. (inr. star.)) ↦ inl. (refl (inl. (inl. (inr. star.)) : Fin eight))
    | inl. (inl. (inl. (inr. star.))) ↦ inl. (refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
    | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]
  | inl. (inr. star.) ↦ match y [
    | inr. star. ↦ inl. (refl (inl. (inr. star.) : Fin eight))
    | inl. (inr. star.) ↦ inl. (refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
    | inl. (inl. (inr. star.)) ↦ inr. (refl (inl. (inr. star.) : Fin eight))
    | inl. (inl. (inl. (inr. star.))) ↦ inr. (refl (inl. (inr. star.) : Fin eight))
    | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inl. (refl (inr. star. : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inr. (refl (inl. (inr. star.) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inr. (refl (inl. (inr. star.) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]
  | inl. (inl. (inr. star.)) ↦ match y [
    | inr. star. ↦ inl. (refl (inl. (inl. (inr. star.)) : Fin eight))
    | inl. (inr. star.) ↦ inr. (refl (inl. (inl. (inr. star.)) : Fin eight))
    | inl. (inl. (inr. star.)) ↦ inl. (refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
    | inl. (inl. (inl. (inr. star.))) ↦ inr. (refl (inl. (inl. (inr. star.)) : Fin eight))
    | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inr. (refl (inl. (inl. (inr. star.)) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inl. (refl (inr. star. : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inr. (refl (inl. (inl. (inr. star.)) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]
  | inl. (inl. (inl. (inr. star.))) ↦ match y [
    | inr. star. ↦ inl. (refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
    | inl. (inr. star.) ↦ inr. (refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
    | inl. (inl. (inr. star.)) ↦ inr. (refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
    | inl. (inl. (inl. (inr. star.))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
    | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inr. (refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inr. (refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inl. (refl (inr. star. : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ match y [
    | inr. star. ↦ inl. (refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
    | inl. (inr. star.) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
    | inl. (inl. (inr. star.)) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
    | inl. (inl. (inl. (inr. star.))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (refl (inr. star. : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inl. (refl (inl. (inr. star.) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inl. (refl (inl. (inl. (inr. star.)) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inl. (refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ match y [
    | inr. star. ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
    | inl. (inr. star.) ↦ inl. (refl (inr. star. : Fin eight))
    | inl. (inl. (inr. star.)) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
    | inl. (inl. (inl. (inr. star.))) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (refl (inl. (inr. star.) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ match y [
    | inr. star. ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
    | inl. (inr. star.) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
    | inl. (inl. (inr. star.)) ↦ inl. (refl (inr. star. : Fin eight))
    | inl. (inl. (inl. (inr. star.))) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (refl (inl. (inl. (inr. star.)) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ match y [
    | inr. star. ↦ inl. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
    | inl. (inr. star.) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
    | inl. (inl. (inr. star.)) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
    | inl. (inl. (inl. (inr. star.))) ↦ inl. (refl (inr. star. : Fin eight))
    | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inr. (refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inl. (refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
    | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. v))))))) ↦ match v [] ]

def q8_commute_or_flip (g k : USym quaternion_group)
  : Sum (Id (USym quaternion_group) (usym_mul quaternion_group g k) (usym_mul quaternion_group k g))
      (Id (USym quaternion_group) (usym_mul quaternion_group k (usym_mul quaternion_group g k)) g)
  ≔ let Q ≔ quaternion_group in
    let F ≔ Fin eight in
    let eg ≔ quaternion_eval g in
    let ek ≔ quaternion_eval k in
    match q8_table eg ek [
    | inl. e ↦ inl. (quaternion_eval_injective (usym_mul Q g k) (usym_mul Q k g)
        (calc
          quaternion_eval (usym_mul Q g k) = q8_mul eg ek by quaternion_eval_usym_mul g k
          = q8_mul ek eg by e
          = quaternion_eval (usym_mul Q k g)
            by inverse F (quaternion_eval (usym_mul Q k g)) (q8_mul ek eg) (quaternion_eval_usym_mul k g) ∎))
    | inr. e ↦ inr. (quaternion_eval_injective (usym_mul Q k (usym_mul Q g k)) g
        (calc
          quaternion_eval (usym_mul Q k (usym_mul Q g k)) = q8_mul ek (quaternion_eval (usym_mul Q g k))
            by quaternion_eval_usym_mul k (usym_mul Q g k)
          = q8_mul ek (q8_mul eg ek) by refl (q8_mul ek) (quaternion_eval_usym_mul g k)
          = eg by e ∎)) ]

{` In Q_8 every conjugate g k g⁻¹ is k or k⁻¹. `}
def q8_conj_cases (g k : USym quaternion_group)
  : Sum (Id (USym quaternion_group) (abstract_conj (abstr quaternion_group) g k) k)
      (Id (USym quaternion_group) (abstract_conj (abstr quaternion_group) g k) (usym_inv quaternion_group k))
  ≔ let Q ≔ quaternion_group in
    let AQ ≔ abstr Q in
    let m ≔ usym_mul Q in
    let ig ≔ usym_inv Q g in
    match q8_commute_or_flip g k [
    | inl. e ↦ inl. (concat (USym Q) (m (m g k) ig) (m (m k g) ig) k
        (refl ((t ↦ m t ig) : USym Q → USym Q) e) (ag_mul_inv_cancel_right AQ k g))
    | inr. e ↦ inr. (ag_inv_unique_right AQ k (m (m g k) ig)
        (calc
          m k (m (m g k) ig) = m (m k (m g k)) ig by AQ .laws .assoc k (m g k) ig
          = m g ig by refl ((t ↦ m t ig) : USym Q → USym Q) e
          = usym_unit Q by AQ .laws .inv_right g ∎)) ]

{` The symmetries of a subgroup are closed under inverses. `}
def subgroup_symmetry_inverse (G : Group) (S : Subgroups G) (k : USym G) (r : SubgroupHasSymmetry G S k)
  : SubgroupHasSymmetry G S (usym_inv G k)
  ≔ let X ≔ S .gset in
    let Y ≔ gset_underlying G X in
    let x ≔ S .point in
    calc
      gset_usym_act G X (usym_inv G k) x
      = gset_usym_act G X (usym_inv G k) (gset_usym_act G X k x)
        by refl (gset_usym_act G X (usym_inv G k)) (inverse Y (gset_usym_act G X k x) x r)
      = x by gset_act_inverse_left G X (shape G) (shape G) k x ∎

def q8_conj_closed (S : Subgroups quaternion_group) : SubgroupConjClosed quaternion_group S
  ≔ g k r ↦
    let Q ≔ quaternion_group in
    let c ≔ abstract_conj (abstr Q) g k in
    match q8_conj_cases g k [
    | inl. e ↦ transport (USym Q) (SubgroupHasSymmetry Q S) k c (inverse (USym Q) c k e) r
    | inr. e ↦ transport (USym Q) (SubgroupHasSymmetry Q S) (usym_inv Q k) c (inverse (USym Q) c (usym_inv Q k) e)
        (subgroup_symmetry_inverse Q S k r) ]

{` Every subgroup of Q_8 is normal; hence Sub(Q_8), Mono(Q_8) and the
   abstr(Q_8)-set of lem:conj-abstract are trivial. `}
def quaternion_subgroup_normal (S : Subgroups quaternion_group) : IsNormalSubgroup quaternion_group S
  ≔ conj_closed_normal quaternion_group S (q8_conj_closed S)

def quaternion_subgroups_trivial : GSetActionTrivial quaternion_group (subgroups_gset quaternion_group)
  ≔ all_normal_subgroups_trivial quaternion_group quaternion_subgroup_normal

def quaternion_monos_trivial : GSetActionTrivial quaternion_group (monos_gset quaternion_group)
  ≔ monos_trivial_of_subgroups quaternion_group quaternion_subgroups_trivial

def quaternion_conj_abstract_trivial : AGSetActionTrivial (abstr quaternion_group) (conj_abstract_agset quaternion_group)
  ≔ conj_abstract_trivial_of_monos quaternion_group quaternion_monos_trivial

{` Q_8 is not abelian: with i, j the symmetries with values 1, 2 at 0,
   (ij)(0) = 7 and (ji)(0) = 3. `}
def q8_element (y : Fin eight) : USym quaternion_group
  ≔ equiv_inverse_map (USym quaternion_group) (Fin eight) quaternion_usym_equiv y

def q8_element_eval (y : Fin eight) : Id (Fin eight) (quaternion_eval (q8_element y)) y
  ≔ equiv_counit (USym quaternion_group) (Fin eight) quaternion_usym_equiv y

def q8_product_value (x y : Fin eight)
  : Id (Fin eight) (quaternion_eval (usym_mul quaternion_group (q8_element x) (q8_element y))) (q8_mul x y)
  ≔ let F ≔ Fin eight in
    calc
      quaternion_eval (usym_mul quaternion_group (q8_element x) (q8_element y))
      = q8_mul (quaternion_eval (q8_element x)) (quaternion_eval (q8_element y))
        by quaternion_eval_usym_mul (q8_element x) (q8_element y)
      = q8_mul x (quaternion_eval (q8_element y))
        by refl ((t ↦ q8_mul t (quaternion_eval (q8_element y))) : F → F) (q8_element_eval x)
      = q8_mul x y by refl (q8_mul x) (q8_element_eval y) ∎

def quaternion_not_abelian (hab : IsAbelian quaternion_group) : Empty
  ≔ let F ≔ Fin eight in
    let one : F ≔ inl. (inr. star.) in
    let two : F ≔ inl. (inl. (inr. star.)) in
    let seven : F ≔ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) in
    let three' : F ≔ inl. (inl. (inl. (inr. star.))) in
    let Q ≔ quaternion_group in
    let i ≔ q8_element one in
    let j ≔ q8_element two in
    nat_decision_false_reflect (Id F seven three') (fin_decidable_equality eight seven three') (refl (false. : Bool))
      (calc
        seven = quaternion_eval (usym_mul Q i j)
          by inverse F (quaternion_eval (usym_mul Q i j)) seven (q8_product_value one two)
        = quaternion_eval (usym_mul Q j i) by refl quaternion_eval (hab i j)
        = three' by q8_product_value two one ∎)

{` rem:typeofsubgpstrivifab, the printed converse refuted: there is a
   group whose G-set Mono(G) (resp. the abstract version, resp. Sub(G)) is
   trivial but which is not abelian. `}
def monos_trivial_not_abelian (h : (G : Group) → GSetActionTrivial G (monos_gset G) → IsAbelian G) : Empty
  ≔ quaternion_not_abelian (h quaternion_group quaternion_monos_trivial)

def abstract_monos_trivial_not_abelian
  (h : (G : Group) → AGSetActionTrivial (abstr G) (conj_abstract_agset G) → IsAbelian G) : Empty
  ≔ quaternion_not_abelian (h quaternion_group quaternion_conj_abstract_trivial)

def subgroups_trivial_not_abelian (h : (G : Group) → GSetActionTrivial G (subgroups_gset G) → IsAbelian G) : Empty
  ≔ quaternion_not_abelian (h quaternion_group quaternion_subgroups_trivial)
