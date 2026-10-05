export "1204-double-delooping"
export "418-cyclic-group-images"

{` Chapter 13 (fields.tex 1177-1219), the explicit data of the example
   after def:ring, for an arbitrary circle C (ℤ = circle_group C, so
   BG ℤ÷ is C .carrier and BBℤ = Σ (X : Type) ‖S¹ = X‖₀).

   Footnote: s : id = id with s(base) = loop is book_integer_twist
   (s(z) is the loop at z with winding number 1, module 88); e_z : S¹ ≃ S¹
   with e_z(base) = z, e_z(loop) = s(z) is circle_translation C z of
   module 88 (xca:general-winding; base and loop laws circle_translation_base
   and circle_rec_beta), and e_base = id (book_integer_rotation_base).
   The loop (e_z, !) : sh = sh in BBℤ is book_integer_mu_loop: first
   component ua(e_z), and "!" holds because e_z is merely the identity
   (S¹ is connected). Bμ(z) ≔ ve(sh, (e_z, !)) is book_integer_mu z
   (ve = pointed circle recursion, module 129). Stated computations:
   Ω(Bμ(z))(loop^k) = (e_z, !)^k with first component ua(e_z)^k, the
   evaluation of (e_z, !) at sh_ℤ is z, and Bμ(base) is the constant map
   (the shape of Hom(ℤ, ℤ)). The two-dimensional computation
   Bμ(loop^j, loop^k) = s^{jk} is formalized on symmetries in module 1351
   (integer_concrete_mul_powers). `}

def book_integer_twist (C : CircleSignature) (z : C .carrier) : Id (C .carrier) z z
  ≔ circle_coordinate_loop_equiv C z .map (C .loop)

def book_integer_twist_base (C : CircleSignature)
  : Id (Id (C .carrier) (C .base) (C .base)) (book_integer_twist C (C .base)) (C .loop)
  ≔ equivalence_injective (Id (C .carrier) (C .base) (C .base)) Int (circle_general_winding_equiv C (C .base))
      (book_integer_twist C (C .base)) (C .loop)
      (concat Int (circle_general_winding C (C .base) (book_integer_twist C (C .base))) (circle_winding C (C .loop))
        (circle_general_winding C (C .base) (C .loop))
        (circle_coordinate_loop_winding C (C .base) (C .loop))
        (inverse Int (circle_general_winding C (C .base) (C .loop)) (circle_winding C (C .loop))
          (circle_general_winding_base_value C (C .loop))))

{` e_base = id_S¹, as maps and as equivalences. `}
def book_integer_rotation_base_map (C : CircleSignature)
  : Id (C .carrier → C .carrier) (circle_translation C (C .base) .map) (identity (C .carrier))
  ≔ let S ≔ C .carrier in
    calc
      circle_rec C S (C .base, book_integer_twist C (C .base)) = circle_rec C S (C .base, C .loop)
        by refl ((l ↦ circle_rec C S (C .base, l)) : Id S (C .base) (C .base) → S → S) (book_integer_twist_base C)
      = identity S by circle_rec_eta C S (identity S) ∎

def book_integer_rotation_base (C : CircleSignature)
  : Id (Equiv (C .carrier) (C .carrier)) (native_equivalence (C .carrier) (C .carrier) (circle_translation C (C .base)))
      (identity_equiv (C .carrier))
  ≔ let S ≔ C .carrier in
    equiv_inverse_map (Id (Equiv S S) (native_equivalence S S (circle_translation C (C .base))) (identity_equiv S))
      (Id (S → S) (circle_translation C (C .base) .map) (identity S))
      (equiv_map_path_equiv S S (native_equivalence S S (circle_translation C (C .base))) (identity_equiv S))
      (book_integer_rotation_base_map C)

{` e_z as an identification S¹ = S¹ (univalence). `}
def book_integer_rotation_path (C : CircleSignature) (z : C .carrier) : Id Type (C .carrier) (C .carrier)
  ≔ ua (C .carrier) (C .carrier) (native_equivalence (C .carrier) (C .carrier) (circle_translation C z))

def book_integer_rotation_path_base (C : CircleSignature)
  : Id (Id Type (C .carrier) (C .carrier)) (book_integer_rotation_path C (C .base)) (refl (C .carrier))
  ≔ let S ≔ C .carrier in
    concat (Id Type S S) (book_integer_rotation_path C (C .base)) (ua S S (identity_equiv S)) (refl S)
      (refl (ua S S) (book_integer_rotation_base C)) (ua_identity S)

{` The "!": ‖refl · ua(e_z) = refl‖, hence |ua(e_z)| ∘ |refl| = |refl| in
   the set truncation, for every z (S¹ is connected and e_base = id). `}
def book_integer_rotation_merely_trivial (C : CircleSignature) (z : C .carrier)
  : Mere (Id (Id Type (C .carrier) (C .carrier))
      (concat Type (C .carrier) (C .carrier) (C .carrier) (refl (C .carrier)) (book_integer_rotation_path C z))
      (refl (C .carrier)))
  ≔ let S ≔ C .carrier in
    let P : S → Type
      ≔ x ↦ Mere (Id (Id Type S S) (concat Type S S S (refl S) (book_integer_rotation_path C x)) (refl S)) in
    mere_rec (Id S (C .base) z) (P z)
      (mere_isprop (Id (Id Type S S) (concat Type S S S (refl S) (book_integer_rotation_path C z)) (refl S)))
      (p ↦ transport S P (C .base) z p
        (mere (Id (Id Type S S) (concat Type S S S (refl S) (book_integer_rotation_path C (C .base))) (refl S))
          (concat (Id Type S S) (concat Type S S S (refl S) (book_integer_rotation_path C (C .base)))
            (book_integer_rotation_path C (C .base)) (refl S)
            (concat_1p Type S S (book_integer_rotation_path C (C .base))) (book_integer_rotation_path_base C))))
      (native_circle_connected C .snd (C .base) z)

def book_integer_trunc_condition (C : CircleSignature) (z : C .carrier)
  : Id (SetTrunc (Id Type (C .carrier) (C .carrier)))
      (set_trunc (Id Type (C .carrier) (C .carrier))
        (concat Type (C .carrier) (C .carrier) (C .carrier) (refl (C .carrier)) (book_integer_rotation_path C z)))
      (set_trunc (Id Type (C .carrier) (C .carrier)) (refl (C .carrier)))
  ≔ let S ≔ C .carrier in let T ≔ Id Type S S in
    equiv_inverse_map
      (Id (SetTrunc T) (set_trunc T (concat Type S S S (refl S) (book_integer_rotation_path C z))) (set_trunc T (refl S)))
      (Mere (Id T (concat Type S S S (refl S) (book_integer_rotation_path C z)) (refl S)))
      (set_trunc_paths T (concat Type S S S (refl S) (book_integer_rotation_path C z)) (refl S))
      (book_integer_rotation_merely_trivial C z)

{` The loop (e_z, !) : sh_BBℤ = sh_BBℤ. `}
def book_integer_mu_loop (C : CircleSignature) (z : C .carrier) : Loop (BB (circle_group C))
  ≔ let S ≔ C .carrier in let pt ≔ univ_cover_point Type S in
    equiv_inverse_map (Id (UnivCover Type S) pt pt) (UnivCoverPath Type S pt pt) (univ_cover_path_equiv Type S pt pt)
      (book_integer_rotation_path C z, book_integer_trunc_condition C z)

def book_integer_mu_loop_fst (C : CircleSignature) (z : C .carrier)
  : Id (Id Type (C .carrier) (C .carrier)) (book_integer_mu_loop C z .fst) (book_integer_rotation_path C z)
  ≔ let S ≔ C .carrier in let pt ≔ univ_cover_point Type S in
    refl ((w ↦ w .fst) : UnivCoverPath Type S pt pt → Id Type S S)
      (equiv_counit (Id (UnivCover Type S) pt pt) (UnivCoverPath Type S pt pt) (univ_cover_path_equiv Type S pt pt)
        (book_integer_rotation_path C z, book_integer_trunc_condition C z))

{` Under Ω(BBℤ) ≃ BZ (evaluation at sh_ℤ), (e_z, !) corresponds to z. `}
def book_integer_mu_loop_evaluation (C : CircleSignature) (z : C .carrier)
  : Id (C .carrier) (bb_loops_evaluation (circle_group C) (book_integer_mu_loop C z)) z
  ≔ let S ≔ C .carrier in
    calc
      bb_loops_evaluation (circle_group C) (book_integer_mu_loop C z) = book_integer_mu_loop C z .fst .trr (C .base)
        by bb_loops_evaluation_value (circle_group C) (book_integer_mu_loop C z)
      = circle_translation C z .map (C .base)
        by refl ((q ↦ q .trr (C .base)) : Id Type S S → S) (book_integer_mu_loop_fst C z)
      = z by circle_translation_base C z ∎

{` Bμ(z) ≔ ve_BBℤ(sh_BBℤ, (e_z, !)). `}
def book_integer_mu (C : CircleSignature) (z : C .carrier) : BookPointedMap (circle_pointed C) (BB (circle_group C))
  ≔ pointed_circle_loop_rec C (BB (circle_group C) .carrier) (bb_point (circle_group C)) (book_integer_mu_loop C z)

{` Bμ(z, loop^k) = (e_z, !)^k … `}
def book_integer_mu_powers (C : CircleSignature) (z : C .carrier) (k : Int)
  : Id (Loop (BB (circle_group C)))
      (loops_map (circle_pointed C) (BB (circle_group C)) (book_integer_mu C z) (circle_power C k))
      (loop_power (BB (circle_group C) .carrier) (bb_point (circle_group C)) (book_integer_mu_loop C z) k)
  ≔ let B ≔ BB (circle_group C) in
    concat (Loop B)
      (loops_map (circle_pointed C) B (book_integer_mu C z) (circle_power C k))
      (loop_power (B .carrier) (B .point) (loops_map (circle_pointed C) B (book_integer_mu C z) (C .loop)) k)
      (loop_power (B .carrier) (B .point) (book_integer_mu_loop C z) k)
      (loops_map_power (circle_pointed C) B (book_integer_mu C z) (C .loop) k)
      (refl ((x ↦ loop_power (B .carrier) (B .point) x k) : Loop B → Loop B)
        (pointed_circle_loop_rec_beta C (B .carrier) (B .point) (book_integer_mu_loop C z)))

{` … whose first component is ua(e_z)^k. `}
def book_integer_mu_powers_fst (C : CircleSignature) (z : C .carrier) (k : Int)
  : Id (Id Type (C .carrier) (C .carrier))
      (loop_power (BB (circle_group C) .carrier) (bb_point (circle_group C)) (book_integer_mu_loop C z) k .fst)
      (loop_power Type (C .carrier) (book_integer_rotation_path C z) k)
  ≔ let S ≔ C .carrier in let B ≔ BB (circle_group C) in let T ≔ Id Type S S in
    let r ≔ book_integer_mu_loop C z in
    let pr ≔ univ_cover_projection Type S in
    calc
      loop_power (B .carrier) (B .point) r k .fst
      = loops_map B (Type, S) pr (loop_power (B .carrier) (B .point) r k)
        by inverse T (loops_map B (Type, S) pr (loop_power (B .carrier) (B .point) r k))
          (loop_power (B .carrier) (B .point) r k .fst)
          (loop_conjugate_at_refl Type S (loop_power (B .carrier) (B .point) r k .fst))
      = loop_power Type S (loops_map B (Type, S) pr r) k by loops_map_power B (Type, S) pr r k
      = loop_power Type S (r .fst) k
        by refl ((x ↦ loop_power Type S x k) : T → T) (loop_conjugate_at_refl Type S (r .fst))
      = loop_power Type S (book_integer_rotation_path C z) k
        by refl ((x ↦ loop_power Type S x k) : T → T) (book_integer_mu_loop_fst C z) ∎

{` Bμ(base) is the constant map at sh_BBℤ (pointed by reflexivity), the
   shape of Hom(ℤ, ℤ): (e_base, !) = refl since e_base = id. `}
def book_integer_mu_loop_base (C : CircleSignature)
  : Id (Loop (BB (circle_group C))) (book_integer_mu_loop C (C .base)) (refl (bb_point (circle_group C)))
  ≔ let S ≔ C .carrier in let pt ≔ univ_cover_point Type S in let T ≔ Id Type S S in
    let E ≔ univ_cover_path_equiv Type S pt pt in
    let P : T → Type
      ≔ q ↦ Id (SetTrunc T) (trunc_path_compose Type S S S (set_trunc T q) (set_trunc T (refl S))) (set_trunc T (refl S)) in
    let w : UnivCoverPath Type S pt pt
      ≔ (book_integer_rotation_path C (C .base), book_integer_trunc_condition C (C .base)) in
    equivalence_injective (Id (UnivCover Type S) pt pt) (UnivCoverPath Type S pt pt) E
      (book_integer_mu_loop C (C .base)) (refl pt)
      (concat (UnivCoverPath Type S pt pt) (E .map (book_integer_mu_loop C (C .base))) w (E .map (refl pt))
        (equiv_counit (Id (UnivCover Type S) pt pt) (UnivCoverPath Type S pt pt) E w)
        (subtype_equal T P (q ↦ set_trunc_set T (trunc_path_compose Type S S S (set_trunc T q) (set_trunc T (refl S)))
            (set_trunc T (refl S)))
          w (E .map (refl pt)) (book_integer_rotation_path_base C)))

def book_integer_mu_base (C : CircleSignature)
  : Id (BookPointedMap (circle_pointed C) (BB (circle_group C))) (book_integer_mu C (C .base))
      (book_pointed_constant (circle_pointed C) (BB (circle_group C)))
  ≔ let B ≔ BB (circle_group C) in let A ≔ B .carrier in let a ≔ B .point in
    let K ≔ book_pointed_constant (circle_pointed C) B in
    calc
      book_integer_mu C (C .base) = pointed_circle_loop_rec C A a (refl a)
        by refl (pointed_circle_loop_rec C A a) (book_integer_mu_loop_base C)
      = pointed_circle_loop_rec C A a (pointed_circle_loop_eval C A a K)
        by refl (pointed_circle_loop_rec C A a)
          (inverse (Id A a a) (pointed_circle_loop_eval C A a K) (refl a) (loop_conjugate_at_refl A a (refl a)))
      = K by pointed_circle_loop_rec_eta C A a K ∎
