export "1411-gram-schmidt"

{` Chapter 14, thm:GramSchmidt (geometry.tex 34-44), conclusion. For a
   basis b of V (free on Fin n): the coordinate map δ : V → Kⁿ with
   δ(b_i) = e_i shows that b is independent and spans V; Gram–Schmidt gives
   an orthonormal u with b ⊆ span(u); then ψ(a) = Σ_i a_i u_i is a linear
   isometry 𝕍ⁿ ≅ V with inverse v ↦ (H(v, u_j))_j. `}

{` The linear isometry 𝕍ⁿ ≅ V. `}
def gram_schmidt_isometry (K : EuclideanField) (n : Nat) (V : InnerProductSpace K)
  (b : Fin n → ip_carrier K V) (hb : IsFreeVectorSpace (K .field) (standard_set n) (V .space) b)
  : LinearIsometry K (standard_inner_product_space K n) V
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let W ≔ V .space in let T ≔ W .carrier in
    let M ≔ ring_self_module R in
    let gd ≔ gram_schmidt_family K V n b (basis_independent (K .field .fst) n (V .space) b hb) in
    let u ≔ gd .fst in let on ≔ gd .snd .fst in let bu ≔ gd .snd .snd .fst in
    let ψ ≔ standard_module_extension R n W u in
    let ψf ≔ ψ .fst .fst in
    let κ : T → Fin n → S ≔ v j ↦ V .form v (u j) in
    let κψ : (a : Fin n → S) → Id (Fin n → S) (κ (ψf a)) a
      ≔ a ↦ funext (Fin n) (_ ↦ S) (κ (ψf a)) a (j ↦ ip_lc_orthonormal K V n u on a j) in
    let ψκ : (v : T) → Id T (ψf (κ v)) v
      ≔ v ↦
        let sb ≔ basis_spans (K .field .fst) n (V .space) b hb v in
        let su ≔ span_combination R W n u n b bu (sb .fst) in
        let sp : InLinearSpan R W n u v
          ≔ (su .fst, concat T v (fin_linear_combination R W n (sb .fst) b) (fin_linear_combination R W n (su .fst) u)
                       (sb .snd) (su .snd)) in
        let kv : Id (Fin n → S) (κ v) (sp .fst)
          ≔ funext (Fin n) (_ ↦ S) (κ v) (sp .fst)
              (j ↦ concat S (V .form v (u j)) (V .form (fin_linear_combination R W n (sp .fst) u) (u j)) (sp .fst j)
                     (refl ((x ↦ V .form x (u j)) : T → S) (sp .snd)) (ip_lc_orthonormal K V n u on (sp .fst) j)) in
        concat T (ψf (κ v)) (ψf (sp .fst)) v (refl ψf kv)
          (inverse T v (fin_linear_combination R W n (sp .fst) u) (sp .snd)) in
    let iso : IsIsometry K (standard_inner_product_space K n) V ψf
      ≔ a a' ↦
        inverse S (V .form (ψf a) (ψf a')) (dot_product K n a a')
          (concat S (V .form (ψf a) (ψf a'))
             (fin_module_sum R M n (i ↦ R .mul (a i) (V .form (u i) (ψf a'))))
             (dot_product K n a a')
             (ip_lc_left K V n a u (ψf a'))
             (refl (fin_module_sum R M n)
               (funext (Fin n) (_ ↦ S) (i ↦ R .mul (a i) (V .form (u i) (ψf a')))
                 (i ↦ R .mul (a i) (a' i))
                 (i ↦ refl (R .mul (a i))
                   (concat S (V .form (u i) (ψf a')) (V .form (ψf a') (u i)) (a' i)
                      (V .inner .symmetric (u i) (ψf a')) (ip_lc_orthonormal K V n u on a' i)))))) in
    ((quasi_inverse_equiv (Fin n → S) T ψf κ κψ ψκ, (ψ .fst .snd, ψ .snd)), iso)

{` thm:GramSchmidt, for OS: if V has dimension n then V = 𝕍ⁿ merely. `}
def gram_schmidt_theorem_os (K : EuclideanField) (n : Nat) (V : InnerProductSpace K)
  (h : HasDimension (K .field) n (V .space))
  : Mere (Id (InnerProductSpace K) V (standard_inner_product_space K n))
  ≔ let OS ≔ InnerProductSpace K in let E ≔ standard_inner_product_space K n in
    mere_rec (Σ (Fin n → ip_carrier K V) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (V .space) i))
      (Mere (Id OS V E)) (mere_isprop (Id OS V E))
      (bh ↦ mere (Id OS V E)
        (inverse OS E V (ip_space_path_from_isometry K E V (gram_schmidt_isometry K n V (bh .fst) (bh .snd)))))
      h

{` thm:GramSchmidt, for OS_n. `}
def gram_schmidt_theorem (K : EuclideanField) (n : Nat) (V : InnerProductSpaceDim K n)
  : Mere (Id (InnerProductSpaceDim K n) V (standard_inner_product_space_dim K n))
  ≔ let OSn ≔ InnerProductSpaceDim K n in let E ≔ standard_inner_product_space_dim K n in
    mere_rec (Σ (Fin n → ip_carrier K (V .fst)) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (V .fst .space) i))
      (Mere (Id OSn V E)) (mere_isprop (Id OSn V E))
      (bh ↦ mere (Id OSn V E)
        (inverse OSn E V
          (ip_space_dim_path_from_isometry K n E V (gram_schmidt_isometry K n (V .fst) (bh .fst) (bh .snd)))))
      (V .snd)
