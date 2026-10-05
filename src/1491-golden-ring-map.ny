export "1490-integer-ring-maps"
export "1442-icosahedron"

{` Chapter 14: the ring map ℤ[φ] → K, a + bφ ↦ a·1 + b·1·φ
   (φ = golden_ratio K, so φ² = φ + 1 is respected), for the ring ℤ[φ] of
   module 1440 (pairs of integers). It preserves 0, 1, φ, addition,
   negation and multiplication, sends the ℤ[φ] vertex list golden_vertex to
   the vertices of the icosahedron in K, and sends the ℤ[φ] squared distance
   to the squared Euclidean distance in 𝔼³ over K. `}

def golden_to_field (K : EuclideanField) (x : GoldenInt) : ef_carrier K
  ≔ K .field .fst .add (int_to_ring (K .field .fst) (x .fst))
      (K .field .fst .mul (int_to_ring (K .field .fst) (x .snd)) (golden_ratio K))

def ring_add_swap_middle (R : AbstractRing) (a b c d : R .carrier)
  : Id (R .carrier) (R .add (R .add a b) (R .add c d)) (R .add (R .add a c) (R .add b d))
  ≔ let S ≔ R .carrier in let p ≔ R .add in
    calc
      p (p a b) (p c d) = p a (p b (p c d)) by inverse S (p a (p b (p c d))) (p (p a b) (p c d)) (ring_add_assoc R a b (p c d))
      = p a (p (p b c) d) by refl (p a) (ring_add_assoc R b c d)
      = p a (p (p c b) d) by refl ((y ↦ p a (p y d)) : S → S) (ring_add_comm R b c)
      = p a (p c (p b d)) by refl (p a) (inverse S (p c (p b d)) (p (p c b) d) (ring_add_assoc R c b d))
      = p (p a c) (p b d) by ring_add_assoc R a c (p b d) ∎

def golden_to_field_add (K : EuclideanField) (x y : GoldenInt)
  : Id (ef_carrier K) (golden_to_field K (golden_add x y)) (K .field .fst .add (golden_to_field K x) (golden_to_field K y))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let a ≔ R .add in let m ≔ R .mul in
    let f ≔ int_to_ring R in let φ ≔ golden_ratio K in
    calc
      a (f (int_add (x .fst) (y .fst))) (m (f (int_add (x .snd) (y .snd))) φ)
      = a (a (f (x .fst)) (f (y .fst))) (m (a (f (x .snd)) (f (y .snd))) φ)
        by refl ((u v ↦ a u (m v φ)) : S → S → S) (int_to_ring_add R (x .fst) (y .fst)) (int_to_ring_add R (x .snd) (y .snd))
      = a (a (f (x .fst)) (f (y .fst))) (a (m (f (x .snd)) φ) (m (f (y .snd)) φ))
        by refl (a (a (f (x .fst)) (f (y .fst)))) (ring_rdistr R (f (x .snd)) (f (y .snd)) φ)
      = a (a (f (x .fst)) (m (f (x .snd)) φ)) (a (f (y .fst)) (m (f (y .snd)) φ))
        by ring_add_swap_middle R (f (x .fst)) (f (y .fst)) (m (f (x .snd)) φ) (m (f (y .snd)) φ) ∎

def golden_to_field_neg (K : EuclideanField) (x : GoldenInt)
  : Id (ef_carrier K) (golden_to_field K (golden_neg x)) (K .field .fst .neg (golden_to_field K x))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let a ≔ R .add in let m ≔ R .mul in let ng ≔ R .neg in
    let f ≔ int_to_ring R in let φ ≔ golden_ratio K in
    calc
      a (f (int_neg (x .fst))) (m (f (int_neg (x .snd))) φ) = a (ng (f (x .fst))) (m (ng (f (x .snd))) φ)
        by refl ((u v ↦ a u (m v φ)) : S → S → S) (int_to_ring_neg R (x .fst)) (int_to_ring_neg R (x .snd))
      = a (ng (f (x .fst))) (ng (m (f (x .snd)) φ)) by refl (a (ng (f (x .fst)))) (ring_mul_neg_left R (f (x .snd)) φ)
      = ng (a (f (x .fst)) (m (f (x .snd)) φ))
        by inverse S (ng (a (f (x .fst)) (m (f (x .snd)) φ))) (a (ng (f (x .fst))) (ng (m (f (x .snd)) φ)))
             (ring_neg_add R (f (x .fst)) (m (f (x .snd)) φ)) ∎

def golden_to_field_mul (K : EuclideanField) (x y : GoldenInt)
  : Id (ef_carrier K) (golden_to_field K (golden_mul x y)) (K .field .fst .mul (golden_to_field K x) (golden_to_field K y))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let a ≔ R .add in let m ≔ R .mul in
    let f ≔ int_to_ring R in let φ ≔ golden_ratio K in let hc ≔ ef_commutative K in
    let A ≔ f (x .fst) in let B ≔ f (x .snd) in let C ≔ f (y .fst) in let D ≔ f (y .snd) in
    let p ≔ m A C in let t ≔ m B D in let q ≔ m (m A D) φ in let r ≔ m (m B C) φ in let s ≔ m (m B D) φ in
    let N ≔ a (a p t) (a (a q r) s) in
    let f1 : Id S (f (int_add (int_mul (x .fst) (y .fst)) (int_mul (x .snd) (y .snd)))) (a p t)
      ≔ concat S (f (int_add (int_mul (x .fst) (y .fst)) (int_mul (x .snd) (y .snd))))
          (a (f (int_mul (x .fst) (y .fst))) (f (int_mul (x .snd) (y .snd)))) (a p t)
          (int_to_ring_add R (int_mul (x .fst) (y .fst)) (int_mul (x .snd) (y .snd)))
          (refl a (int_to_ring_mul R (x .fst) (y .fst)) (int_to_ring_mul R (x .snd) (y .snd))) in
    let i1 ≔ int_add (int_mul (x .fst) (y .snd)) (int_mul (x .snd) (y .fst)) in
    let f2 : Id S (f (int_add i1 (int_mul (x .snd) (y .snd)))) (a (a (m A D) (m B C)) t)
      ≔ concat S (f (int_add i1 (int_mul (x .snd) (y .snd)))) (a (f i1) (f (int_mul (x .snd) (y .snd))))
          (a (a (m A D) (m B C)) t)
          (int_to_ring_add R i1 (int_mul (x .snd) (y .snd)))
          (refl a
            (concat S (f i1) (a (f (int_mul (x .fst) (y .snd))) (f (int_mul (x .snd) (y .fst)))) (a (m A D) (m B C))
              (int_to_ring_add R (int_mul (x .fst) (y .snd)) (int_mul (x .snd) (y .fst)))
              (refl a (int_to_ring_mul R (x .fst) (y .snd)) (int_to_ring_mul R (x .snd) (y .fst))))
            (int_to_ring_mul R (x .snd) (y .snd))) in
    let lhs : Id S (golden_to_field K (golden_mul x y)) N
      ≔ calc
          golden_to_field K (golden_mul x y) = a (a p t) (m (a (a (m A D) (m B C)) t) φ)
            by refl ((u v ↦ a u (m v φ)) : S → S → S) f1 f2
          = a (a p t) (a (m (a (m A D) (m B C)) φ) s) by refl (a (a p t)) (ring_rdistr R (a (m A D) (m B C)) t φ)
          = N by refl ((u ↦ a (a p t) (a u s)) : S → S) (ring_rdistr R (m A D) (m B C) φ) ∎ in
    let bq : Id S (m A (m D φ)) q ≔ ring_mul_assoc R A D φ in
    let br : Id S (m (m B φ) C) r
      ≔ calc
          m (m B φ) C = m B (m φ C) by inverse S (m B (m φ C)) (m (m B φ) C) (ring_mul_assoc R B φ C)
          = m B (m C φ) by refl (m B) (hc φ C)
          = r by ring_mul_assoc R B C φ ∎ in
    let bst : Id S (m (m B φ) (m D φ)) (a s t)
      ≔ calc
          m (m B φ) (m D φ) = m B (m D (m φ φ)) by inverse S (m B (m D (m φ φ))) (m (m B φ) (m D φ)) (cring_mul_interchange R hc B D φ φ)
          = m (m B D) (m φ φ) by ring_mul_assoc R B D (m φ φ)
          = m (m B D) (a φ (R .one)) by refl (m (m B D)) (golden_ratio_square K)
          = a s (m (m B D) (R .one)) by ring_ldistr R (m B D) φ (R .one)
          = a s t by refl (a s) (ring_mul_one_right R (m B D)) ∎ in
    let rhs : Id S (m (golden_to_field K x) (golden_to_field K y)) N
      ≔ calc
          m (a A (m B φ)) (a C (m D φ)) = a (m A (a C (m D φ))) (m (m B φ) (a C (m D φ)))
            by ring_rdistr R A (m B φ) (a C (m D φ))
          = a (a p (m A (m D φ))) (a (m (m B φ) C) (m (m B φ) (m D φ)))
            by refl a (ring_ldistr R A C (m D φ)) (ring_ldistr R (m B φ) C (m D φ))
          = a (a p q) (a r (a s t)) by refl ((u v w ↦ a (a p u) (a v w)) : S → S → S → S) bq br bst
          = a (a p q) (a (a r s) t) by refl (a (a p q)) (ring_add_assoc R r s t)
          = a (a (a p q) (a r s)) t by ring_add_assoc R (a p q) (a r s) t
          = a (a p (a q (a r s))) t
            by refl ((u ↦ a u t) : S → S) (inverse S (a p (a q (a r s))) (a (a p q) (a r s)) (ring_add_assoc R p q (a r s)))
          = a (a p (a (a q r) s)) t by refl ((u ↦ a (a p u) t) : S → S) (ring_add_assoc R q r s)
          = a p (a (a (a q r) s) t) by inverse S (a p (a (a (a q r) s) t)) (a (a p (a (a q r) s)) t) (ring_add_assoc R p (a (a q r) s) t)
          = a p (a t (a (a q r) s)) by refl (a p) (ring_add_comm R (a (a q r) s) t)
          = N by ring_add_assoc R p t (a (a q r) s) ∎ in
    concat S (golden_to_field K (golden_mul x y)) N (m (golden_to_field K x) (golden_to_field K y))
      lhs (inverse S (m (golden_to_field K x) (golden_to_field K y)) N rhs)

def golden_to_field_nat (K : EuclideanField) (n : Nat)
  : Id (ef_carrier K) (golden_to_field K (pos. n, pos. zero.)) (ring_of_nat (K .field .fst) n)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    concat S (R .add (ring_of_nat R n) (R .mul (R .zero) (golden_ratio K))) (R .add (ring_of_nat R n) (R .zero)) (ring_of_nat R n)
      (refl (R .add (ring_of_nat R n)) (ring_mul_zero_left R (golden_ratio K))) (R .add_laws .unit_right (ring_of_nat R n))

def golden_to_field_zero (K : EuclideanField) : Id (ef_carrier K) (golden_to_field K golden_zero) (K .field .fst .zero)
  ≔ golden_to_field_nat K zero.

def golden_to_field_one (K : EuclideanField) : Id (ef_carrier K) (golden_to_field K golden_one) (K .field .fst .one)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    concat S (golden_to_field K golden_one) (R .add (R .zero) (R .one)) (R .one)
      (golden_to_field_nat K 1) (R .add_laws .unit_left (R .one))

def golden_to_field_phi (K : EuclideanField) : Id (ef_carrier K) (golden_to_field K golden_phi) (golden_ratio K)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let φ ≔ golden_ratio K in
    calc
      R .add (R .zero) (R .mul (R .add (R .zero) (R .one)) φ) = R .mul (R .add (R .zero) (R .one)) φ
        by R .add_laws .unit_left (R .mul (R .add (R .zero) (R .one)) φ)
      = R .mul (R .one) φ by refl ((u ↦ R .mul u φ) : S → S) (R .add_laws .unit_left (R .one))
      = φ by ring_mul_one_left R φ ∎

{` The vertex list commutes with maps preserving 0, 1, negation and φ. `}
def icosa_sign_natural (S T : Type) (h : S → T) (nS : S → S) (nT : T → T)
  (hn : (x : S) → Id T (h (nS x)) (nT (h x))) (b : Bool) (x : S)
  : Id T (h (icosa_sign S nS b x)) (icosa_sign T nT b (h x))
  ≔ match b [ true. ↦ refl (h x) | false. ↦ hn x ]

def icosa_vertex_natural (S T : Type) (h : S → T) (zS oS : S) (nS : S → S) (pS : S) (zT oT : T) (nT : T → T) (pT : T)
  (hz : Id T (h zS) zT) (ho : Id T (h oS) oT) (hn : (x : S) → Id T (h (nS x)) (nT (h x))) (hp : Id T (h pS) pT)
  (k : Fin 3) (b c : Bool) (j : Fin 3)
  : Id T (h (icosa_vertex S zS oS nS pS (k, (b, c)) j)) (icosa_vertex T zT oT nT pT (k, (b, c)) j)
  ≔ let pb : Id T (h (icosa_sign S nS b oS)) (icosa_sign T nT b oT)
      ≔ concat T (h (icosa_sign S nS b oS)) (icosa_sign T nT b (h oS)) (icosa_sign T nT b oT)
          (icosa_sign_natural S T h nS nT hn b oS) (refl (icosa_sign T nT b) ho) in
    let pc : Id T (h (icosa_sign S nS c pS)) (icosa_sign T nT c pT)
      ≔ concat T (h (icosa_sign S nS c pS)) (icosa_sign T nT c (h pS)) (icosa_sign T nT c pT)
          (icosa_sign_natural S T h nS nT hn c pS) (refl (icosa_sign T nT c) hp) in
    match k [
    | inl. u ↦ match u [
      | inl. _ ↦ match j [ inl. v ↦ match v [ inl. _ ↦ hz | inr. _ ↦ pb ] | inr. _ ↦ pc ]
      | inr. _ ↦ match j [ inl. v ↦ match v [ inl. _ ↦ pc | inr. _ ↦ hz ] | inr. _ ↦ pb ] ]
    | inr. _ ↦ match j [ inl. v ↦ match v [ inl. _ ↦ pb | inr. _ ↦ pc ] | inr. _ ↦ hz ] ]

def golden_vertex_to_field (K : EuclideanField) (i : IcosaIndex) (j : Fin 3)
  : Id (ef_carrier K) (golden_to_field K (golden_vertex i j)) (icosahedron_vertex K i j)
  ≔ let R ≔ K .field .fst in
    icosa_vertex_natural GoldenInt (ef_carrier K) (golden_to_field K) golden_zero golden_one golden_neg golden_phi
      (R .zero) (R .one) (R .neg) (golden_ratio K)
      (golden_to_field_zero K) (golden_to_field_one K) (golden_to_field_neg K) (golden_to_field_phi K)
      (i .fst) (i .snd .fst) (i .snd .snd) j

{` The ℤ[φ] squared distance maps to the squared distance in 𝔼³. `}
def golden_sq_distance_to_field (K : EuclideanField) (u v : Fin 3 → GoldenInt)
  : Id (ef_carrier K) (golden_to_field K (golden_sq_distance u v))
      (dot_product K 3 (standard_three_difference K (j ↦ golden_to_field K (u j)) (j ↦ golden_to_field K (v j)))
                       (standard_three_difference K (j ↦ golden_to_field K (u j)) (j ↦ golden_to_field K (v j))))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let a ≔ R .add in let m ≔ R .mul in
    let ψ ≔ golden_to_field K in
    let d ≔ (j : Fin 3) ↦ golden_add (u j) (golden_neg (v j)) in
    let e ≔ (j : Fin 3) ↦ a (ψ (u j)) (R .neg (ψ (v j))) in
    let sq ≔ (j : Fin 3) ↦ golden_square (d j) in
    let psq : (j : Fin 3) → Id S (ψ (sq j)) (m (e j) (e j))
      ≔ j ↦
        let pd : Id S (ψ (d j)) (e j)
          ≔ concat S (ψ (d j)) (a (ψ (u j)) (ψ (golden_neg (v j)))) (e j)
              (golden_to_field_add K (u j) (golden_neg (v j))) (refl (a (ψ (u j))) (golden_to_field_neg K (v j))) in
        concat S (ψ (sq j)) (m (ψ (d j)) (ψ (d j))) (m (e j) (e j)) (golden_to_field_mul K (d j) (d j)) (refl m pd pd) in
    let j0 : Fin 3 ≔ inl. (inl. (inr. star.)) in let j1 : Fin 3 ≔ inl. (inr. star.) in let j2 : Fin 3 ≔ inr. star. in
    calc
      ψ (golden_add (golden_add (sq j0) (sq j1)) (sq j2)) = a (ψ (golden_add (sq j0) (sq j1))) (ψ (sq j2))
        by golden_to_field_add K (golden_add (sq j0) (sq j1)) (sq j2)
      = a (a (ψ (sq j0)) (ψ (sq j1))) (ψ (sq j2)) by refl ((w ↦ a w (ψ (sq j2))) : S → S) (golden_to_field_add K (sq j0) (sq j1))
      = a (a (m (e j0) (e j0)) (m (e j1) (e j1))) (m (e j2) (e j2))
        by refl ((x y w ↦ a (a x y) w) : S → S → S → S) (psq j0) (psq j1) (psq j2)
      = a (a (a (R .zero) (m (e j0) (e j0))) (m (e j1) (e j1))) (m (e j2) (e j2))
        by refl ((w ↦ a (a w (m (e j1) (e j1))) (m (e j2) (e j2))) : S → S)
             (inverse S (a (R .zero) (m (e j0) (e j0))) (m (e j0) (e j0)) (R .add_laws .unit_left (m (e j0) (e j0)))) ∎
