export "1521-synthetic-division"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms,
   preliminaries: a polynomial a(0) + a(1)X + ⋯ + a(n)Xⁿ over a field K
   with a(n) ≠ 0 has at most n distinct roots. Formulated with lists: an
   injective r : Fin m → K all of whose values are roots has m ≤ n
   (poly_root_bound). Proof (constructive): by induction on n; divide by
   X − c for the last root c (module 1521); the other roots y satisfy
   (y − c) q(y) = 0 with y − c ≠ 0, so q(y) = 0 (no zero divisors). `}

def poly_root_bound (K : Field) (n : Nat) (a : Fin (suc. n) → K .fst .carrier)
  (lead : Not (Id (K .fst .carrier) (a (inr. star.)) (K .fst .zero)))
  (m : Nat) (r : Fin m → K .fst .carrier) (rinj : PathReflecting (Fin m) (K .fst .carrier) r)
  (rroot : (j : Fin m) → Id (K .fst .carrier) (poly_value (K .fst) (r j) n a) (K .fst .zero))
  : Le m n
  ≔ match n [
  | zero. ↦ match m [ zero. ↦ star. | suc. m ↦ match lead (rroot (inr. star.)) [] ]
  | suc. n ↦ match m [
    | zero. ↦ star.
    | suc. m ↦
      let R ≔ K .fst in let A ≔ R .carrier in let p ≔ R .add in let mu ≔ R .mul in
      let c ≔ r (inr. star.) in
      let q ≔ poly_div R n a c in
      let pa_c ≔ poly_value R c (suc. n) a in
      poly_root_bound K n q
        (e ↦ lead (concat A (a (inr. star.)) (q (inr. star.)) (R .zero)
          (inverse A (q (inr. star.)) (a (inr. star.)) (poly_div_lead R n a c)) e))
        m (j ↦ r (inl. j))
        (j1 j2 e ↦ sum_encode (Fin m) Unit (inl. j1) (inl. j2) (rinj (inl. j1) (inl. j2) e))
        (j ↦
          let y ≔ r (inl. j) in
          let u ≔ p y (R .neg c) in
          let qy ≔ poly_value R y n q in
          let prod : Id A (mu u qy) (R .zero)
            ≔ calc
                mu u qy = p (mu u qy) (R .zero) by inverse A (p (mu u qy) (R .zero)) (mu u qy) (R .add_laws .unit_right (mu u qy))
                = p (mu u qy) pa_c by refl (p (mu u qy)) (inverse A pa_c (R .zero) (rroot (inr. star.)))
                = poly_value R y (suc. n) a by inverse A (poly_value R y (suc. n) a) (p (mu u qy) pa_c)
                    (poly_div_spec R (K .snd .fst .fst) n a c y)
                = R .zero by rroot (inl. j) ∎ in
          field_no_zero_divisors K u qy
            (field_sub_nonzero R y c (e ↦ sum_encode (Fin m) Unit (inl. j) (inr. star.) (rinj (inl. j) (inr. star.) e)))
            prod) ] ]
