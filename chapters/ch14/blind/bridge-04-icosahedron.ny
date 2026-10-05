export "04-icosahedron"
export "bridge-00-core"
export "../../../src/1442-icosahedron"

{` Bridges for geometry.tex, section "The icosahedron" (blind file
   04-icosahedron): blocks 294 and 300.

   The blind golden ratio is ours: 2⁻¹ is unique, and √5 is the unique
   non-negative square root (ef_sqrt_unique), with 5 = (2+2)+1 written
   differently (ring_of_nat). The blind vertex indexing differs from ours
   (sign false ↦ +, cyclic shifts in the other order): bridge_ico_sigma
   (an involution) matches the two families, and the blind and our
   12-term sums agree after reindexing (bridge_ico_sum). So the blind
   vertex set and the blind convex hull are our objects
   icosahedron_vertex_set and icosahedron. The remark's claims follow from
   ours (golden_rectangle_*, icosahedron_edge_*), after replacing the blind
   φ by ours. `}

def bridge_four (K : BlindEuclideanField)
  : Id (K .field .fst .carrier) (blind_four K) (ring_of_nat (K .field .fst) 4)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let t ≔ blind_two K in
    concat S (R .add t t) (R .mul t t) (ring_of_nat R 4)
      (inverse S (R .mul t t) (R .add t t) (ring_two_mul R t)) (ef_two_square (bridge_ef14 K))

def bridge_five (K : BlindEuclideanField)
  : Id (K .field .fst .carrier) (blind_five K) (ring_of_nat (K .field .fst) 5)
  ≔ let R ≔ K .field .fst in
    refl ((y ↦ R .add y (R .one)) : R .carrier → R .carrier) (bridge_four K)

def bridge_sqrt_five (K : BlindEuclideanField)
  : Id (K .field .fst .carrier) (blind_sqrt_five K) (ef_sqrt_five (bridge_ef14 K))
  ≔ let L ≔ bridge_ef14 K in let R ≔ K .field .fst in let S ≔ R .carrier in
    let w ≔ K .sqrt (blind_five K) (blind_nonneg_five K) in
    inverse S (ef_sqrt_five L) (blind_sqrt_five K)
      (ef_sqrt_unique L (ring_of_nat R 5) (ef_nat_nonneg L 5) (w .fst) (w .snd .fst)
        (concat S (R .mul (w .fst) (w .fst)) (blind_five K) (ring_of_nat R 5) (w .snd .snd) (bridge_five K)))

def bridge_half (K : BlindEuclideanField)
  : Id (K .field .fst .carrier) (blind_half K) (ef_half (bridge_ef14 K))
  ≔ let L ≔ bridge_ef14 K in let R ≔ K .field .fst in
    let W ≔ InverseWitness R (blind_two K) in
    refl ((w ↦ w .fst) : W → R .carrier)
      (inverse_witness_prop R (blind_two K)
        (mere_rec W W (blind_inverse_witness_prop K (blind_two K)) (w ↦ w)
          (K .nonzero_invertible (blind_two K) (blind_two_nonzero K)))
        (ef_half_witness L))

{` Definition at 294: φ. `}
def bridge_phi (K : BlindEuclideanField) : Id (K .field .fst .carrier) (blind_phi K) (golden_ratio (bridge_ef14 K))
  ≔ let R ≔ K .field .fst in
    refl (R .mul) (refl (R .add (R .one)) (bridge_sqrt_five K)) (bridge_half K)

{` Reindexing: blind (k, s₁, s₂) is our (k', ¬s₁, ¬s₂), k' swapping the
   second and third cyclic shift. `}
def bridge_ico_cyc (k : Fin 3) : Fin 3
  ≔ match k [
  | inl. u ↦ match u [ inl. w ↦ inl. (inl. w) | inr. _ ↦ inr. star. ]
  | inr. _ ↦ inl. (inr. star.) ]

def bridge_ico_cyc_invol (k : Fin 3) : Id (Fin 3) (bridge_ico_cyc (bridge_ico_cyc k)) k
  ≔ match k [
  | inl. u ↦ match u [ inl. w ↦ refl (inl. (inl. w) : Fin 3) | inr. star. ↦ refl (inl. (inr. star.) : Fin 3) ]
  | inr. star. ↦ refl (inr. star. : Fin 3) ]

def bridge_ico_sigma (v : BlindIcoIndex) : IcosaIndex
  ≔ (bridge_ico_cyc (v .fst), (bool_not (v .snd .fst), bool_not (v .snd .snd)))

def bridge_ico_sigma_invol (i : IcosaIndex) : Id IcosaIndex (bridge_ico_sigma (bridge_ico_sigma i)) i
  ≔ refl ((k b c ↦ (k, (b, c))) : Fin 3 → Bool → Bool → IcosaIndex)
      (bridge_ico_cyc_invol (i .fst)) (bool_not_involutive (i .snd .fst)) (bool_not_involutive (i .snd .snd))

def bridge_sign (K : BlindEuclideanField) (s : Bool) (x : K .field .fst .carrier)
  : Id (K .field .fst .carrier) (blind_sign K s x) (icosa_sign (K .field .fst .carrier) (K .field .fst .neg) (bool_not s) x)
  ≔ match s [ false. ↦ refl x | true. ↦ refl (K .field .fst .neg x) ]

def bridge_vertex_case (K : BlindEuclideanField) (x : K .field .fst .carrier) (k : Fin 3) (s1 s2 : Bool)
  : Id (Fin 3 → K .field .fst .carrier)
      (blind_cyclic K k (K .field .fst .zero) (blind_sign K s1 (K .field .fst .one)) (blind_sign K s2 x))
      (icosa_vertex (K .field .fst .carrier) (K .field .fst .zero) (K .field .fst .one) (K .field .fst .neg) x
        (bridge_ico_cyc k, (bool_not s1, bool_not s2)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    let z ≔ R .zero in
    let b ≔ blind_sign K s1 (R .one) in let c ≔ blind_sign K s2 x in
    let b' ≔ icosa_sign S (R .neg) (bool_not s1) (R .one) in let c' ≔ icosa_sign S (R .neg) (bool_not s2) x in
    let pb ≔ bridge_sign K s1 (R .one) in let pc ≔ bridge_sign K s2 x in
    match k [
    | inl. u ↦ match u [
      | inl. w ↦ fin_three_funext S (blind_vec3 K z b c) (triple_vector S z b' c') (refl z) pb pc
      | inr. _ ↦ fin_three_funext S (blind_vec3 K b c z) (triple_vector S b' c' z) pb pc (refl z) ]
    | inr. _ ↦ fin_three_funext S (blind_vec3 K c z b) (triple_vector S c' z b') pc (refl z) pb ]

def bridge_vertex (K : BlindEuclideanField) (v : BlindIcoIndex)
  : Id (Fin 3 → K .field .fst .carrier) (blind_ico_vertex K v) (icosahedron_vertex (bridge_ef14 K) (bridge_ico_sigma v))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 3 → S in
    concat F (blind_ico_vertex K v) (icosa_vertex S (R .zero) (R .one) (R .neg) (blind_phi K) (bridge_ico_sigma v))
      (icosahedron_vertex (bridge_ef14 K) (bridge_ico_sigma v))
      (bridge_vertex_case K (blind_phi K) (v .fst) (v .snd .fst) (v .snd .snd))
      (refl ((x ↦ icosa_vertex S (R .zero) (R .one) (R .neg) x (bridge_ico_sigma v)) : S → F) (bridge_phi K))

def bridge_vertex_back (K : BlindEuclideanField) (i : IcosaIndex)
  : Id (Fin 3 → K .field .fst .carrier) (blind_ico_vertex K (bridge_ico_sigma i)) (icosahedron_vertex (bridge_ef14 K) i)
  ≔ let F ≔ Fin 3 → K .field .fst .carrier in
    concat F (blind_ico_vertex K (bridge_ico_sigma i)) (icosahedron_vertex (bridge_ef14 K) (bridge_ico_sigma (bridge_ico_sigma i)))
      (icosahedron_vertex (bridge_ef14 K) i)
      (bridge_vertex K (bridge_ico_sigma i)) (refl (icosahedron_vertex (bridge_ef14 K)) (bridge_ico_sigma_invol i))

{` The two 12-term sums agree after reindexing. `}
def bridge_sum3 (R : AbstractRing) (W : RingModule R) (a b c : W .carrier)
  : Id (W .carrier) (W .add (W .add (W .add (W .zero) a) b) c) (W .add (W .add a c) b)
  ≔ let T ≔ W .carrier in
    calc
      W .add (W .add (W .add (W .zero) a) b) c = W .add (W .add a b) c
        by refl ((y ↦ W .add (W .add y b) c) : T → T) (W .add_laws .unit_left a)
      = W .add a (W .add b c) by inverse T (W .add a (W .add b c)) (W .add (W .add a b) c) (W .add_laws .assoc a b c)
      = W .add a (W .add c b) by refl (W .add a) (W .add_comm b c)
      = W .add (W .add a c) b by W .add_laws .assoc a c b ∎

def bridge_ico_sum (K : BlindEuclideanField) (W : RingModule (K .field .fst)) (f : BlindIcoIndex → W .carrier)
  : Id (W .carrier) (blind_ico_sum K W f) (icosa_index_sum (K .field .fst) W (i ↦ f (bridge_ico_sigma i)))
  ≔ let G ≔ (k : Fin 3) ↦ W .add (W .add (f (k, (false., false.))) (f (k, (false., true.))))
                                  (W .add (f (k, (true., false.))) (f (k, (true., true.)))) in
    bridge_sum3 (K .field .fst) W (G (inl. (inl. (inr. star.)))) (G (inl. (inr. star.))) (G (inr. star.))

{` Definition at 294: the vertex set. `}
def bridge_vertex_pred (K : BlindEuclideanField)
  : Id ((Fin 3 → K .field .fst .carrier) → PropTypes) (blind_icosahedron_vertices K .snd)
      (icosahedron_vertex_set (bridge_ef14 K) .snd)
  ≔ let L ≔ bridge_ef14 K in let S ≔ K .field .fst .carrier in let F ≔ Fin 3 → S in
    let bv ≔ blind_ico_vertex K in let ov ≔ icosahedron_vertex L in
    funext F (_ ↦ PropTypes) (blind_icosahedron_vertices K .snd) (icosahedron_vertex_set L .snd)
      (P ↦
        let A ≔ Σ BlindIcoIndex (v ↦ Id F P (bv v)) in
        let B ≔ Σ IcosaIndex (i ↦ Id F (ov i) P) in
        proposition_extensionality (blind_icosahedron_vertices K .snd P) (icosahedron_vertex_set L .snd P)
          (mere_rec A (Mere B) (mere_isprop B)
            (u ↦ mere B (bridge_ico_sigma (u .fst),
              inverse F P (ov (bridge_ico_sigma (u .fst)))
                (concat F P (bv (u .fst)) (ov (bridge_ico_sigma (u .fst))) (u .snd) (bridge_vertex K (u .fst))))))
          (mere_rec B (Mere A) (mere_isprop A)
            (u ↦ mere A (bridge_ico_sigma (u .fst),
              concat F P (ov (u .fst)) (bv (bridge_ico_sigma (u .fst)))
                (inverse F (ov (u .fst)) P (u .snd))
                (inverse F (bv (bridge_ico_sigma (u .fst))) (ov (u .fst)) (bridge_vertex_back K (u .fst)))))))

def bridge_icosahedron_vertices (K : BlindEuclideanField)
  : Id (EuclideanObject (bridge_ef14 K) propositions_settype)
      (bridge_obj K blind_prop_set (blind_icosahedron_vertices K)) (icosahedron_vertex_set (bridge_ef14 K))
  ≔ (bridge_std_es K 3, bridge_vertex_pred K)

{` Definition at 294: the convex hull. `}
def bridge_hull_forward (K : BlindEuclideanField) (P : Fin 3 → K .field .fst .carrier) (u : BlindIcoHullWitness K P)
  : IcosahedronConvexCombination (bridge_ef14 K) P
  ≔ let L ≔ bridge_ef14 K in let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 3 → S in
    let W ≔ standard_module R 3 in let I ≔ ring_self_module R in
    let l ≔ u .fst in let λ ≔ (i : IcosaIndex) ↦ l (bridge_ico_sigma i) in
    let f ≔ (v : BlindIcoIndex) ↦ W .smul (l v) (blind_ico_vertex K v) in
    (λ,
     (i ↦ u .snd .fst (bridge_ico_sigma i),
      (concat S (icosa_index_sum R I λ) (blind_ico_sum K I l) (R .one)
         (inverse S (blind_ico_sum K I l) (icosa_index_sum R I λ) (bridge_ico_sum K I l)) (u .snd .snd .fst),
       calc
         icosa_index_sum R W (i ↦ W .smul (λ i) (icosahedron_vertex L i))
         = icosa_index_sum R W (i ↦ f (bridge_ico_sigma i))
           by refl (icosa_index_sum R W)
             (funext IcosaIndex (_ ↦ F) (i ↦ W .smul (λ i) (icosahedron_vertex L i)) (i ↦ f (bridge_ico_sigma i))
               (i ↦ refl (W .smul (λ i))
                 (inverse F (blind_ico_vertex K (bridge_ico_sigma i)) (icosahedron_vertex L i) (bridge_vertex_back K i))))
         = blind_ico_sum K W f by inverse F (blind_ico_sum K W f) (icosa_index_sum R W (i ↦ f (bridge_ico_sigma i))) (bridge_ico_sum K W f)
         = P by inverse F P (blind_ico_sum K W f) (u .snd .snd .snd) ∎)))

def bridge_hull_backward (K : BlindEuclideanField) (P : Fin 3 → K .field .fst .carrier)
  (u : IcosahedronConvexCombination (bridge_ef14 K) P) : BlindIcoHullWitness K P
  ≔ let L ≔ bridge_ef14 K in let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 3 → S in
    let W ≔ standard_module R 3 in let I ≔ ring_self_module R in
    let λ ≔ u .fst in let l ≔ (v : BlindIcoIndex) ↦ λ (bridge_ico_sigma v) in
    let f ≔ (v : BlindIcoIndex) ↦ W .smul (l v) (blind_ico_vertex K v) in
    let lσ : Id (IcosaIndex → S) (i ↦ l (bridge_ico_sigma i)) λ
      ≔ funext IcosaIndex (_ ↦ S) (i ↦ l (bridge_ico_sigma i)) λ (i ↦ refl λ (bridge_ico_sigma_invol i)) in
    (l,
     (v ↦ u .snd .fst (bridge_ico_sigma v),
      (calc
         blind_ico_sum K I l = icosa_index_sum R I (i ↦ l (bridge_ico_sigma i)) by bridge_ico_sum K I l
         = icosa_index_sum R I λ by refl (icosa_index_sum R I) lσ
         = R .one by u .snd .snd .fst ∎,
       calc
         P = icosa_index_sum R W (i ↦ W .smul (λ i) (icosahedron_vertex L i))
           by inverse F (icosa_index_sum R W (i ↦ W .smul (λ i) (icosahedron_vertex L i))) P (u .snd .snd .snd)
         = icosa_index_sum R W (i ↦ f (bridge_ico_sigma i))
           by refl (icosa_index_sum R W)
             (funext IcosaIndex (_ ↦ F) (i ↦ W .smul (λ i) (icosahedron_vertex L i)) (i ↦ f (bridge_ico_sigma i))
               (i ↦ refl (W .smul) (inverse S (l (bridge_ico_sigma i)) (λ i) (refl λ (bridge_ico_sigma_invol i)))
                 (inverse F (blind_ico_vertex K (bridge_ico_sigma i)) (icosahedron_vertex L i) (bridge_vertex_back K i))))
         = blind_ico_sum K W f by inverse F (blind_ico_sum K W f) (icosa_index_sum R W (i ↦ f (bridge_ico_sigma i))) (bridge_ico_sum K W f) ∎)))

def bridge_hull_pred (K : BlindEuclideanField)
  : Id ((Fin 3 → K .field .fst .carrier) → PropTypes) (blind_icosahedron K .snd) (icosahedron (bridge_ef14 K) .snd)
  ≔ let L ≔ bridge_ef14 K in let F ≔ Fin 3 → K .field .fst .carrier in
    funext F (_ ↦ PropTypes) (blind_icosahedron K .snd) (icosahedron L .snd)
      (P ↦
        let A ≔ BlindIcoHullWitness K P in let B ≔ IcosahedronConvexCombination L P in
        proposition_extensionality (blind_icosahedron K .snd P) (icosahedron L .snd P)
          (mere_rec A (Mere B) (mere_isprop B) (u ↦ mere B (bridge_hull_forward K P u)))
          (mere_rec B (Mere A) (mere_isprop A) (u ↦ mere A (bridge_hull_backward K P u))))

def bridge_icosahedron (K : BlindEuclideanField)
  : Id (EuclideanObject (bridge_ef14 K) propositions_settype)
      (bridge_obj K blind_prop_set (blind_icosahedron K)) (icosahedron (bridge_ef14 K))
  ≔ (bridge_std_es K 3, bridge_hull_pred K)

{` Remark at 300. Generic computations in the third coordinate x (then
   x := φ). `}
def bridge_rect_sides (K : BlindEuclideanField) (x : K .field .fst .carrier)
  : Id (Fin 3 → K .field .fst .carrier)
      (blind_sub3 K (blind_vec3 K (K .field .fst .zero) (K .field .fst .one) x)
                    (blind_vec3 K (K .field .fst .zero) (K .field .fst .neg (K .field .fst .one)) x))
      (blind_sub3 K (blind_vec3 K (K .field .fst .zero) (K .field .fst .one) (K .field .fst .neg x))
                    (blind_vec3 K (K .field .fst .zero) (K .field .fst .neg (K .field .fst .one)) (K .field .fst .neg x)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let o ≔ R .one in let ng ≔ R .neg in
    fin_three_funext S
      (blind_sub3 K (blind_vec3 K z o x) (blind_vec3 K z (ng o) x))
      (blind_sub3 K (blind_vec3 K z o (ng x)) (blind_vec3 K z (ng o) (ng x)))
      (refl (R .add z (ng z))) (refl (R .add o (ng (ng o))))
      (concat S (R .add x (ng x)) z (R .add (ng x) (ng (ng x))) (R .add_laws .inv_right x)
        (inverse S (R .add (ng x) (ng (ng x))) z (R .add_laws .inv_right (ng x))))

def bridge_rect_orthogonal (K : BlindEuclideanField) (x : K .field .fst .carrier)
  : Id (K .field .fst .carrier)
      (blind_dot K 3 (blind_sub3 K (blind_vec3 K (K .field .fst .zero) (K .field .fst .one) x)
                                   (blind_vec3 K (K .field .fst .zero) (K .field .fst .neg (K .field .fst .one)) x))
                     (blind_sub3 K (blind_vec3 K (K .field .fst .zero) (K .field .fst .one) x)
                                   (blind_vec3 K (K .field .fst .zero) (K .field .fst .one) (K .field .fst .neg x))))
      (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let o ≔ R .one in let ng ≔ R .neg in
    let a ≔ R .add in let m ≔ R .mul in
    calc
      a (a (a z (m (a z (ng z)) (a z (ng z)))) (m (a o (ng (ng o))) (a o (ng o)))) (m (a x (ng x)) (a x (ng (ng x))))
      = a (a (a z (m z (a z (ng z)))) (m (a o (ng (ng o))) z)) (m z (a x (ng (ng x))))
        by refl ((p q r ↦ a (a (a z (m p (a z (ng z)))) (m (a o (ng (ng o))) q)) (m r (a x (ng (ng x))))) : S → S → S → S)
             (R .add_laws .inv_right z) (R .add_laws .inv_right o) (R .add_laws .inv_right x)
      = a (a (a z z) z) z
        by refl ((p q r ↦ a (a (a z p) q) r) : S → S → S → S)
             (ring_mul_zero_left R (a z (ng z))) (ring_mul_zero_right R (a o (ng (ng o)))) (ring_mul_zero_left R (a x (ng (ng x))))
      = a (a z z) z by refl ((y ↦ a (a y z) z) : S → S) (R .add_laws .unit_left z)
      = a z z by refl ((y ↦ a y z) : S → S) (R .add_laws .unit_left z)
      = z by R .add_laws .unit_left z ∎

def bridge_norm_ours (K : BlindEuclideanField) (v : Fin 3 → K .field .fst .carrier)
  : Id (K .field .fst .carrier) (blind_norm3 K v) (ip_norm (bridge_ef14 K) (standard_inner_product_space (bridge_ef14 K) 3) v)
  ≔ let X ≔ blind_dot K 3 v v in
    refl ((h : K .nonneg X) ↦ K .sqrt X h .fst)
      (K .nonneg_prop X (blind_dot_laws K 3 .pos v) (dot_product_inner (bridge_ef14 K) 3 .nonneg v))

def bridge_golden_rectangle (K : BlindEuclideanField) : blind_golden_rectangle K
  ≔ let L ≔ bridge_ef14 K in let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 3 → S in
    let z ≔ R .zero in let o ≔ R .one in let ng ≔ R .neg in
    let φb ≔ blind_phi K in let φ ≔ golden_ratio L in let pφ ≔ bridge_phi K in
    let ab ≔ (x : S) ↦ blind_sub3 K (blind_vec3 K z o x) (blind_vec3 K z (ng o) x) in
    let ac ≔ (x : S) ↦ blind_sub3 K (blind_vec3 K z o x) (blind_vec3 K z o (ng x)) in
    (bridge_rect_sides K φb,
     (bridge_rect_orthogonal K φb,
      (calc
         blind_norm3 K (ab φb) = blind_norm3 K (ab φ) by refl ((x ↦ blind_norm3 K (ab x)) : S → S) pφ
         = standard_three_distance L (golden_rectangle_a L) (golden_rectangle_b L) by bridge_norm_ours K (ab φ)
         = blind_two K by golden_rectangle_short_length L ∎,
       calc
         blind_norm3 K (ac φb) = blind_norm3 K (ac φ) by refl ((x ↦ blind_norm3 K (ac x)) : S → S) pφ
         = standard_three_distance L (golden_rectangle_a L) (golden_rectangle_d L) by bridge_norm_ours K (ac φ)
         = R .add φ φ by golden_rectangle_long_length L
         = R .mul (blind_two K) φ by inverse S (R .mul (blind_two K) φ) (R .add φ φ) (ring_two_mul R φ)
         = R .mul (blind_two K) φb by refl (R .mul (blind_two K)) (inverse S φb φ pφ) ∎)))

{` (0,1,x) - (1,x,0) has squared norm 1 + (x-1)² + x², for any x. `}
def bridge_adjacent_square (K : BlindEuclideanField) (x : K .field .fst .carrier)
  : Id (K .field .fst .carrier)
      (blind_dot K 3 (blind_sub3 K (blind_vec3 K (K .field .fst .zero) (K .field .fst .one) x) (blind_vec3 K (K .field .fst .one) x (K .field .fst .zero)))
                     (blind_sub3 K (blind_vec3 K (K .field .fst .zero) (K .field .fst .one) x) (blind_vec3 K (K .field .fst .one) x (K .field .fst .zero))))
      (K .field .fst .add (K .field .fst .add (K .field .fst .one)
          (K .field .fst .mul (K .field .fst .add x (K .field .fst .neg (K .field .fst .one))) (K .field .fst .add x (K .field .fst .neg (K .field .fst .one)))))
        (K .field .fst .mul x x))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let o ≔ R .one in let ng ≔ R .neg in
    let a ≔ R .add in let m ≔ R .mul in let G ≔ ring_additive_group R in
    let X ≔ a o (ng x) in let Y ≔ a x (ng o) in
    let c0 : Id S (m (a z (ng o)) (a z (ng o))) o
      ≔ calc
          m (a z (ng o)) (a z (ng o)) = m (ng o) (ng o) by refl (m) (R .add_laws .unit_left (ng o)) (R .add_laws .unit_left (ng o))
          = m o o by inverse S (m o o) (m (ng o) (ng o)) (ring_neg_neg_mul R o o)
          = o by ring_mul_one_left R o ∎ in
    let yx : Id S (a Y X) z
      ≔ calc
          a Y X = a x (a (ng o) X) by inverse S (a x (a (ng o) X)) (a Y X) (ring_add_assoc R x (ng o) X)
          = a x (a (a (ng o) o) (ng x)) by refl (a x) (ring_add_assoc R (ng o) o (ng x))
          = a x (a z (ng x)) by refl ((y ↦ a x (a y (ng x))) : S → S) (ag_inv_left G o)
          = a x (ng x) by refl (a x) (R .add_laws .unit_left (ng x))
          = z by R .add_laws .inv_right x ∎ in
    let xn : Id S X (ng Y) ≔ ag_inv_unique_right G Y X yx in
    let c1 : Id S (m X X) (m Y Y)
      ≔ concat S (m X X) (m (ng Y) (ng Y)) (m Y Y) (refl m xn xn) (inverse S (m Y Y) (m (ng Y) (ng Y)) (ring_neg_neg_mul R Y Y)) in
    let e : Id S (a x (ng z)) x
      ≔ concat S (a x (ng z)) (a x z) x (refl (a x) (ag_inv_unit G)) (R .add_laws .unit_right x) in
    calc
      a (a (a z (m (a z (ng o)) (a z (ng o)))) (m X X)) (m (a x (ng z)) (a x (ng z)))
      = a (a (a z o) (m Y Y)) (m x x) by refl (a) (refl (a) (refl (a z) c0) c1) (refl m e e)
      = a (a o (m Y Y)) (m x x) by refl ((y ↦ a (a y (m Y Y)) (m x x)) : S → S) (R .add_laws .unit_left o) ∎

def bridge_icosahedron_adjacent_distance (K : BlindEuclideanField) : blind_icosahedron_adjacent_distance K
  ≔ let L ≔ bridge_ef14 K in let R ≔ K .field .fst in let S ≔ R .carrier in
    let z ≔ R .zero in let o ≔ R .one in let ng ≔ R .neg in let a ≔ R .add in let m ≔ R .mul in
    let φb ≔ blind_phi K in let φ ≔ golden_ratio L in let pφ ≔ bridge_phi K in
    let d ≔ (x : S) ↦ blind_sub3 K (blind_vec3 K z o x) (blind_vec3 K o x z) in
    let total ≔ (x : S) ↦ a (a o (m (a x (ng o)) (a x (ng o)))) (m x x) in
    (bridge_adjacent_square K φb,
     (calc
        total φb = total φ by refl total pφ
        = blind_dot K 3 (d φ) (d φ) by inverse S (blind_dot K 3 (d φ) (d φ)) (total φ) (bridge_adjacent_square K φ)
        = ring_of_nat R 4 by icosahedron_edge_square L
        = blind_four K by inverse S (blind_four K) (ring_of_nat R 4) (bridge_four K) ∎,
      calc
        blind_norm3 K (d φb) = blind_norm3 K (d φ) by refl ((x ↦ blind_norm3 K (d x)) : S → S) pφ
        = standard_three_distance L (icosahedron_vertex L (inl. (inl. (inr. star.)), (true., true.)))
            (icosahedron_vertex L (inr. star., (true., true.))) by bridge_norm_ours K (d φ)
        = blind_two K by icosahedron_edge_length L ∎))
