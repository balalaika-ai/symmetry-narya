export "03-geometric-objects"

{` Blind statements, chapter 14 (geometry.tex), section "The icosahedron".
   Standard Euclidean three-space E^3 over the parameter K; its points are
   (definitionally) the vectors Fin 3 → K. Coordinates x, y, z are the
   elements of Fin 3 in summation order. `}

def blind_one (K : BlindEuclideanField) : K .field .fst .carrier ≔ K .field .fst .one

def blind_two (K : BlindEuclideanField) : K .field .fst .carrier
  ≔ K .field .fst .add (K .field .fst .one) (K .field .fst .one)

def blind_four (K : BlindEuclideanField) : K .field .fst .carrier ≔ K .field .fst .add (blind_two K) (blind_two K)

def blind_five (K : BlindEuclideanField) : K .field .fst .carrier ≔ K .field .fst .add (blind_four K) (blind_one K)

def blind_nonneg_one (K : BlindEuclideanField) : K .nonneg (K .field .fst .one)
  ≔ let R ≔ K .field .fst in
    transport (R .carrier) (K .nonneg) (R .mul (R .one) (R .one)) (R .one) (ring_mul_one_left R (R .one))
      (K .nonneg_square (R .one))

def blind_nonneg_two (K : BlindEuclideanField) : K .nonneg (blind_two K)
  ≔ K .nonneg_add (K .field .fst .one) (K .field .fst .one) (blind_nonneg_one K) (blind_nonneg_one K)

def blind_nonneg_five (K : BlindEuclideanField) : K .nonneg (blind_five K)
  ≔ K .nonneg_add (blind_four K) (blind_one K)
      (K .nonneg_add (blind_two K) (blind_two K) (blind_nonneg_two K) (blind_nonneg_two K)) (blind_nonneg_one K)

{` 2 ≠ 0 in an ordered field: 1 + 1 = 0 gives 1 = -1, so 1 ≥ 0 and
   -1 ≥ 0, hence 1 = 0. `}
def blind_two_nonzero (K : BlindEuclideanField) : Not (Id (K .field .fst .carrier) (blind_two K) (K .field .fst .zero))
  ≔ p ↦
    let R ≔ K .field .fst in
    let S ≔ R .carrier in
    let q : Id S (R .one) (R .neg (R .one)) ≔ blind_nonneg_sum_zero_neg K (R .one) (R .one) p in
    let z : Id S (R .one) (R .zero)
      ≔ K .nonneg_antisym (R .one) (blind_nonneg_one K)
          (transport S (K .nonneg) (R .one) (R .neg (R .one)) q (blind_nonneg_one K)) in
    K .field .snd .fst .snd (inverse S (R .one) (R .zero) z)

{` Inverses are unique, so the inverse of an invertible element can be
   extracted from the truncation. `}
def blind_inverse_witness_prop (K : BlindEuclideanField) (x : K .field .fst .carrier)
  : isProp (InverseWitness (K .field .fst) x)
  ≔ u v ↦
    let R ≔ K .field .fst in
    let S ≔ R .carrier in
    let a ≔ u .fst in
    let b ≔ v .fst in
    subtype_equal S (c ↦ Product (Id S (R .mul x c) (R .one)) (Id S (R .mul c x) (R .one)))
      (c ↦ product_prop (Id S (R .mul x c) (R .one)) (Id S (R .mul c x) (R .one))
        (ring_set R (R .mul x c) (R .one)) (ring_set R (R .mul c x) (R .one)))
      u v
      (calc
         a = R .mul a (R .one) by inverse S (R .mul a (R .one)) a (ring_mul_one_right R a)
         = R .mul a (R .mul x b) by refl (R .mul a) (inverse S (R .mul x b) (R .one) (v .snd .fst))
         = R .mul (R .mul a x) b by ring_mul_assoc R a x b
         = R .mul (R .one) b by refl ((w ↦ R .mul w b) : S → S) (u .snd .snd)
         = b by ring_mul_one_left R b ∎)

def blind_half (K : BlindEuclideanField) : K .field .fst .carrier
  ≔ let R ≔ K .field .fst in
    (mere_rec (InverseWitness R (blind_two K)) (InverseWitness R (blind_two K))
       (blind_inverse_witness_prop K (blind_two K)) (w ↦ w)
       (K .nonzero_invertible (blind_two K) (blind_two_nonzero K))) .fst

def blind_sqrt_five (K : BlindEuclideanField) : K .field .fst .carrier
  ≔ K .sqrt (blind_five K) (blind_nonneg_five K) .fst

{` The golden ratio φ = (1 + √5)/2. `}
def blind_phi (K : BlindEuclideanField) : K .field .fst .carrier
  ≔ K .field .fst .mul (K .field .fst .add (K .field .fst .one) (blind_sqrt_five K)) (blind_half K)

def blind_vec3 (K : BlindEuclideanField) (a b c : K .field .fst .carrier) : Fin 3 → K .field .fst .carrier
  ≔ t ↦ match t [ inl. u ↦ match u [ inl. _ ↦ a | inr. _ ↦ b ] | inr. _ ↦ c ]

def blind_sign (K : BlindEuclideanField) (s : Bool) (x : K .field .fst .carrier) : K .field .fst .carrier
  ≔ match s [ false. ↦ x | true. ↦ K .field .fst .neg x ]

{` The three cyclic permutations of a triple (a, b, c): (a, b, c),
   (b, c, a), (c, a, b). `}
def blind_cyclic (K : BlindEuclideanField) (k : Fin 3) (a b c : K .field .fst .carrier) : Fin 3 → K .field .fst .carrier
  ≔ match k [
  | inl. u ↦ match u [ inl. _ ↦ blind_vec3 K a b c | inr. _ ↦ blind_vec3 K b c a ]
  | inr. _ ↦ blind_vec3 K c a b ]

def BlindIcoIndex : Type ≔ Product (Fin 3) (Product Bool Bool)

{` The 12 vertices: cyclic permutations of (0, ±1, ±φ). `}
def blind_ico_vertex (K : BlindEuclideanField) (v : BlindIcoIndex) : Fin 3 → K .field .fst .carrier
  ≔ blind_cyclic K (v .fst) (K .field .fst .zero) (blind_sign K (v .snd .fst) (K .field .fst .one))
      (blind_sign K (v .snd .snd) (blind_phi K))

{` Sums over the 12-element index set, in a module W. `}
def blind_ico_sum (K : BlindEuclideanField) (W : RingModule (K .field .fst)) (f : BlindIcoIndex → W .carrier)
  : W .carrier
  ≔ fin_module_sum (K .field .fst) W 3
      (k ↦ W .add (W .add (f (k, (false., false.))) (f (k, (false., true.))))
                  (W .add (f (k, (true., false.))) (f (k, (true., true.)))))

def blind_e3 (K : BlindEuclideanField) : BlindEuclideanSpace K
  ≔ blind_es_dim_forget K 3 (blind_std_euclidean_space K 3)

{` Definition (geometry.tex 294), the vertex set of the icosahedron as a
   subset of Points E^3. `}
def blind_icosahedron_vertices (K : BlindEuclideanField) : BlindEucObj K blind_prop_set
  ≔ (blind_e3 K,
     P ↦ (Mere (Σ BlindIcoIndex (v ↦ Id (Fin 3 → K .field .fst .carrier) P (blind_ico_vertex K v))),
          mere_isprop (Σ BlindIcoIndex (v ↦ Id (Fin 3 → K .field .fst .carrier) P (blind_ico_vertex K v)))))

{` Definition (geometry.tex 294). The icosahedron (side length 2) as the
   solid with these vertices: their convex hull, as a geometric object in
   E^3 (subset of points). P is in it iff P = Σ_v λ_v v for some weights
   λ_v ≥ 0 with Σ_v λ_v = 1. `}
def BlindIcoHullWitness (K : BlindEuclideanField) (P : Fin 3 → K .field .fst .carrier) : Type
  ≔ let R ≔ K .field .fst in
    Σ (BlindIcoIndex → R .carrier)
      (l ↦ Product ((v : BlindIcoIndex) → K .nonneg (l v))
        (Product (Id (R .carrier) (blind_ico_sum K (ring_self_module R) l) (R .one))
          (Id (Fin 3 → R .carrier) P
            (blind_ico_sum K (standard_module R 3) (v ↦ standard_module R 3 .smul (l v) (blind_ico_vertex K v))))))

def blind_icosahedron (K : BlindEuclideanField) : BlindEucObj K blind_prop_set
  ≔ (blind_e3 K, P ↦ (Mere (BlindIcoHullWitness K P), mere_isprop (BlindIcoHullWitness K P)))

{` Difference of vectors and the Euclidean norm ‖v‖ = √H(v,v). `}
def blind_sub3 (K : BlindEuclideanField) (u w : Fin 3 → K .field .fst .carrier) : Fin 3 → K .field .fst .carrier
  ≔ t ↦ K .field .fst .add (u t) (K .field .fst .neg (w t))

def blind_norm (K : BlindEuclideanField) (V : BlindInnerProductSpace K) (v : V .space .carrier) : K .field .fst .carrier
  ≔ K .sqrt (V .inner v v) (V .laws .pos v) .fst

def blind_norm3 (K : BlindEuclideanField) (v : Fin 3 → K .field .fst .carrier) : K .field .fst .carrier
  ≔ blind_norm K (blind_std_inner_product_space K 3) v

{` Remark (geometry.tex 300), first claim: the four vertices (0, ±1, ±φ)
   form a golden rectangle with short side 2: with a = (0,1,φ),
   b = (0,-1,φ), c = (0,1,-φ), d = (0,-1,-φ): a - b = c - d, the sides
   a - b and a - c are orthogonal, ‖a - b‖ = 2 and ‖a - c‖ = 2φ (ratio φ). `}
def blind_golden_rectangle (K : BlindEuclideanField) : Type
  ≔ let R ≔ K .field .fst in
    let S ≔ R .carrier in
    let a ≔ blind_vec3 K (R .zero) (R .one) (blind_phi K) in
    let b ≔ blind_vec3 K (R .zero) (R .neg (R .one)) (blind_phi K) in
    let c ≔ blind_vec3 K (R .zero) (R .one) (R .neg (blind_phi K)) in
    let d ≔ blind_vec3 K (R .zero) (R .neg (R .one)) (R .neg (blind_phi K)) in
    Product (Id (Fin 3 → S) (blind_sub3 K a b) (blind_sub3 K c d))
      (Product (Id S (blind_dot K 3 (blind_sub3 K a b) (blind_sub3 K a c)) (R .zero))
        (Product (Id S (blind_norm3 K (blind_sub3 K a b)) (blind_two K))
          (Id S (blind_norm3 K (blind_sub3 K a c)) (R .mul (blind_two K) (blind_phi K)))))

{` Remark (geometry.tex 300), the displayed computation: for
   d = (0,1,φ) - (1,φ,0): ‖d‖² = 1 + (φ-1)² + φ², this equals 4, and
   ‖d‖ = √4 = 2. `}
def blind_icosahedron_adjacent_distance (K : BlindEuclideanField) : Type
  ≔ let R ≔ K .field .fst in
    let S ≔ R .carrier in
    let phi ≔ blind_phi K in
    let pm1 ≔ R .add phi (R .neg (R .one)) in
    let d ≔ blind_sub3 K (blind_vec3 K (R .zero) (R .one) phi) (blind_vec3 K (R .one) phi (R .zero)) in
    let total ≔ R .add (R .add (R .one) (R .mul pm1 pm1)) (R .mul phi phi) in
    Product (Id S (blind_dot K 3 d d) total)
      (Product (Id S total (blind_four K))
        (Id S (blind_norm3 K d) (blind_two K)))
