export "815-dihedral-classifying-paths"

{` con:bidirectional-bicycle (congp.tex:109): φ induces a bijection on
   symmetries, hence (BD_n and the component being connected) φ is an
   equivalence (cor:fib-vs-path, connected_map_equiv_from_loops).

   At the base point x₀ = (Fin 2, X₀, f) the symmetries of BD_n are the pairs
   (σ, g) with σ : Fin 2 ≃ Fin 2, g : X₀ ≃ X₀, g ∘ f_s = f_{σ s} ∘ g
   (module 815), and Ωφ sends (σ, g) to the bicycle automorphism σ × g of
   φ(x₀) = (Fin 2 × X₀, a, b) (judgmentally on underlying maps). Every
   automorphism k of φ(x₀) is of this form: commuting with a, the first
   coordinate of k(s, -) is invariant under f_s, hence constant (every element
   of X₀ is f_s^z of [(s, 0)] = x*); commuting with b, the second coordinate
   does not depend on s. So k = σ × g with σ s = (k(s, x*)).1 and
   g x = (k(yes, x)).2, and the same for k⁻¹ gives the inverses. `}

def dbl_two : Type ≔ two_set_carrier dihedral_two_shape

def dbl_point (H : Subtypes Int) (h : IntegerSubgroupLaws H) : DihedralBaseSet H h
  ≔ dihedral_class dihedral_two_shape H h s2c3_fin2_yes int_zero

def dbl_frame (H : Subtypes Int) (h : IntegerSubgroupLaws H) : DFrame
  ≔ dbc_frame H h (dihedral_classifying_base H h)

def dbl_bicycle (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Bicycles
  ≔ dihedral_bicycle H h (dihedral_classifying_base H h)

{` An equivalence of a 2-element set commutes with swap. `}
def dbc_equiv_swap (S : TwoElementSets) (σ : Equiv (two_set_carrier S) (two_set_carrier S)) (s : two_set_carrier S)
  : Id (two_set_carrier S) (σ .map (two_set_swap S s)) (two_set_swap S (σ .map s))
  ≔ let g ≔ equiv_inverse_map (two_set_carrier S) (two_set_carrier S) σ in
    two_set_other_is_swap S (σ .map s) (σ .map (two_set_swap S s))
      (q ↦ two_set_swap_ne S s (calc
        two_set_swap S s = g (σ .map (two_set_swap S s))
          by equiv_unit (two_set_carrier S) (two_set_carrier S) σ (two_set_swap S s)
        = g (σ .map s) by refl g q
        = s by equiv_retraction (two_set_carrier S) (two_set_carrier S) σ s ∎))

{` Bicycle isomorphisms are determined by their underlying maps. `}
def dbc_iso_ext (B B' : Bicycles) (e d : BicycleIsomorphisms B B')
  (p : (x : bicycle_carrier B) → Id (bicycle_carrier B') (e .fst .map x) (d .fst .map x))
  : Id (BicycleIsomorphisms B B') e d
  ≔ subtype_equal (Equiv (bicycle_carrier B) (bicycle_carrier B'))
      (f ↦ Product
        (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (f .map))
        (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (f .map)))
      (f ↦ product_prop
        (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (f .map))
        (Commutes (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (f .map))
        (commutes_prop (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier_set B') (bicycle_a B) (bicycle_a B') (f .map))
        (commutes_prop (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier_set B') (bicycle_b B) (bicycle_b B') (f .map)))
      e d (equiv_homotopy (bicycle_carrier B) (bicycle_carrier B') (e .fst) (d .fst) p)

{` (σ, g) ↦ σ × g. `}
def dihedral_frame_product (H : Subtypes Int) (h : IntegerSubgroupLaws H) (e : DFrameIsos (dbl_frame H h) (dbl_frame H h))
  : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)
  ≔ (product_equiv dbl_two (DihedralBaseSet H h) dbl_two (DihedralBaseSet H h) (e .fst .fst) (e .fst .snd),
     (u ↦ refl (dbc_pair_at dbl_two (DihedralBaseSet H h) (e .fst .fst .map (u .fst))) (e .snd (u .fst) (u .snd)),
      u ↦ refl (dbc_pair_with dbl_two (DihedralBaseSet H h) (e .fst .snd .map (u .snd)))
            (dbc_equiv_swap dihedral_two_shape (e .fst .fst) (u .fst))))

{` A map Int → B invariant under succ is constant. `}
def dbl_int_const_pos (B : Type) (c : Int → B) (step : (w : Int) → Id B (c (int_succ w)) (c w)) (n : Nat)
  : Id B (c (pos. n)) (c int_zero)
  ≔ match n [
  | zero. ↦ refl (c int_zero)
  | suc. m ↦ concat B (c (pos. (suc. m))) (c (pos. m)) (c int_zero) (step (pos. m)) (dbl_int_const_pos B c step m) ]

def dbl_int_const_neg (B : Type) (c : Int → B) (step : (w : Int) → Id B (c (int_succ w)) (c w)) (n : Nat)
  : Id B (c (neg. n)) (c int_zero)
  ≔ match n [
  | zero. ↦ inverse B (c int_zero) (c (neg. zero.)) (step (neg. zero.))
  | suc. m ↦ concat B (c (neg. (suc. m))) (c (neg. m)) (c int_zero)
      (inverse B (c (neg. m)) (c (neg. (suc. m))) (step (neg. (suc. m)))) (dbl_int_const_neg B c step m) ]

def dbl_int_const (B : Type) (c : Int → B) (step : (w : Int) → Id B (c (int_succ w)) (c w)) (w : Int)
  : Id B (c w) (c int_zero)
  ≔ match w [ pos. n ↦ dbl_int_const_pos B c step n | neg. n ↦ dbl_int_const_neg B c step n ]

{` A map out of X₀ into a set, invariant under f_s, is constant. `}
def dbl_const_on_cycle (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : dbl_two) (B : Type) (hB : isSet B)
  (c : DihedralBaseSet H h → B)
  (inv : (u : DihedralBaseSet H h) → Id B (c (dihedral_move dihedral_two_shape H h s u)) (c u))
  (u : DihedralBaseSet H h) : Id B (c u) (c (dbl_point H h))
  ≔ let S ≔ dihedral_two_shape in
    quotient_prop_induction (DihedralPair S) (dihedral_relation S H h)
      (u ↦ Id B (c u) (c (dbl_point H h))) (u ↦ hB (c u) (c (dbl_point H h)))
      (v ↦ calc
        c (dihedral_class S H h (v .fst) (v .snd))
          = c (dihedral_class S H h s (dihedral_sign dbl_two s (v .fst) (two_set_decidable S (v .fst) s) (v .snd)))
          by refl c (inverse (DihedralBaseSet H h)
               (dihedral_class S H h s (dihedral_sign dbl_two s (v .fst) (two_set_decidable S (v .fst) s) (v .snd)))
               (dihedral_class S H h (v .fst) (v .snd))
               (dihedral_insert_eval_at S H h s (v .fst) (v .snd) (two_set_decidable S (v .fst) s)))
        = c (dihedral_class S H h s int_zero)
          by dbl_int_const B (w ↦ c (dihedral_class S H h s w))
               (w ↦ concat B (c (dihedral_class S H h s (int_succ w))) (c (dihedral_move S H h s (dihedral_class S H h s w)))
                  (c (dihedral_class S H h s w))
                  (refl c (inverse (DihedralBaseSet H h) (dihedral_move S H h s (dihedral_class S H h s w))
                    (dihedral_class S H h s (int_succ w)) (dihedral_move_self S H h s w)))
                  (inv (dihedral_class S H h s w)))
               (dihedral_sign dbl_two s (v .fst) (two_set_decidable S (v .fst) s) (v .snd))
        = c (dbl_point H h) by refl c (dihedral_zero_unambiguous S H h s s2c3_fin2_yes) ∎)
      u

{` The two coordinates of a bicycle automorphism k of φ(x₀). `}
def dbl_first (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
  (s : dbl_two) (u : DihedralBaseSet H h) : dbl_two
  ≔ k .fst .map (s, u) .fst

def dbl_second (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
  (s : dbl_two) (u : DihedralBaseSet H h) : DihedralBaseSet H h
  ≔ k .fst .map (s, u) .snd

def dbl_first_const (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (s : dbl_two) (u : DihedralBaseSet H h)
  : Id dbl_two (dbl_first H h k s u) (dbl_first H h k s (dbl_point H h))
  ≔ dbl_const_on_cycle H h s dbl_two (dihedral_two_shape .fst .snd) (dbl_first H h k s)
      (v ↦ refl ((w ↦ w .fst) : DihedralBaseProduct H h → dbl_two) (k .snd .fst (s, v))) u

def dbl_second_swap (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (s : dbl_two) (u : DihedralBaseSet H h)
  : Id (DihedralBaseSet H h) (dbl_second H h k (two_set_swap dihedral_two_shape s) u) (dbl_second H h k s u)
  ≔ refl ((w ↦ w .snd) : DihedralBaseProduct H h → DihedralBaseSet H h) (k .snd .snd (s, u))

def dbl_second_const (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (s : Fin two) (u : DihedralBaseSet H h)
  : Id (DihedralBaseSet H h) (dbl_second H h k s u) (dbl_second H h k s2c3_fin2_yes u)
  ≔ match s [
  | inr. star. ↦ refl (dbl_second H h k s2c3_fin2_yes u)
  | inl. (inr. star.) ↦ concat (DihedralBaseSet H h) (dbl_second H h k s2c3_fin2_no u)
      (dbl_second H h k (two_set_swap dihedral_two_shape s2c3_fin2_yes) u) (dbl_second H h k s2c3_fin2_yes u)
      (refl ((t ↦ dbl_second H h k t u) : dbl_two → DihedralBaseSet H h)
        (two_set_other_is_swap dihedral_two_shape s2c3_fin2_yes s2c3_fin2_no s2c3_fin2_no_not_yes))
      (dbl_second_swap H h k s2c3_fin2_yes u)
  | inl. (inl. e) ↦ match e [] ]

def dbl_sigma (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
  (s : dbl_two) : dbl_two
  ≔ dbl_first H h k s (dbl_point H h)

def dbl_g (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
  (u : DihedralBaseSet H h) : DihedralBaseSet H h
  ≔ dbl_second H h k s2c3_fin2_yes u

{` k(s, u) = (σ s, g u). `}
def dbl_decompose (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (s : dbl_two) (u : DihedralBaseSet H h)
  : Id (DihedralBaseProduct H h) (k .fst .map (s, u)) (dbl_sigma H h k s, dbl_g H h k u)
  ≔ (dbl_first_const H h k s u, dbl_second_const H h k s u)

def dbl_inverse (H : Subtypes Int) (h : IntegerSubgroupLaws H) (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
  : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)
  ≔ bicycle_iso_inverse (dbl_bicycle H h) (dbl_bicycle H h) k

def dbl_sigma_retraction (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (s : dbl_two)
  : Id dbl_two (dbl_sigma H h (dbl_inverse H h k) (dbl_sigma H h k s)) s
  ≔ let k' ≔ dbl_inverse H h k in
    let x ≔ dbl_point H h in
    calc
      dbl_first H h k' (dbl_sigma H h k s) x = dbl_first H h k' (dbl_sigma H h k s) (dbl_g H h k x)
        by inverse dbl_two (dbl_first H h k' (dbl_sigma H h k s) (dbl_g H h k x)) (dbl_first H h k' (dbl_sigma H h k s) x)
             (dbl_first_const H h k' (dbl_sigma H h k s) (dbl_g H h k x))
      = k' .fst .map (k .fst .map (s, x)) .fst
        by refl ((w ↦ k' .fst .map w .fst) : DihedralBaseProduct H h → dbl_two)
             (inverse (DihedralBaseProduct H h) (k .fst .map (s, x)) (dbl_sigma H h k s, dbl_g H h k x) (dbl_decompose H h k s x))
      = s by refl ((w ↦ w .fst) : DihedralBaseProduct H h → dbl_two)
             (equiv_retraction (DihedralBaseProduct H h) (DihedralBaseProduct H h) (k .fst) (s, x)) ∎

def dbl_sigma_section (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (s : dbl_two)
  : Id dbl_two (dbl_sigma H h k (dbl_sigma H h (dbl_inverse H h k) s)) s
  ≔ let k' ≔ dbl_inverse H h k in
    let x ≔ dbl_point H h in
    calc
      dbl_first H h k (dbl_sigma H h k' s) x = dbl_first H h k (dbl_sigma H h k' s) (dbl_g H h k' x)
        by inverse dbl_two (dbl_first H h k (dbl_sigma H h k' s) (dbl_g H h k' x)) (dbl_first H h k (dbl_sigma H h k' s) x)
             (dbl_first_const H h k (dbl_sigma H h k' s) (dbl_g H h k' x))
      = k .fst .map (k' .fst .map (s, x)) .fst
        by refl ((w ↦ k .fst .map w .fst) : DihedralBaseProduct H h → dbl_two)
             (inverse (DihedralBaseProduct H h) (k' .fst .map (s, x)) (dbl_sigma H h k' s, dbl_g H h k' x) (dbl_decompose H h k' s x))
      = s by refl ((w ↦ w .fst) : DihedralBaseProduct H h → dbl_two)
             (equiv_counit (DihedralBaseProduct H h) (DihedralBaseProduct H h) (k .fst) (s, x)) ∎

def dbl_g_retraction (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (u : DihedralBaseSet H h)
  : Id (DihedralBaseSet H h) (dbl_g H h (dbl_inverse H h k) (dbl_g H h k u)) u
  ≔ let k' ≔ dbl_inverse H h k in
    let y ≔ s2c3_fin2_yes in
    calc
      dbl_second H h k' y (dbl_g H h k u) = dbl_second H h k' (dbl_sigma H h k y) (dbl_g H h k u)
        by inverse (DihedralBaseSet H h) (dbl_second H h k' (dbl_sigma H h k y) (dbl_g H h k u)) (dbl_second H h k' y (dbl_g H h k u))
             (dbl_second_const H h k' (dbl_sigma H h k y) (dbl_g H h k u))
      = k' .fst .map (k .fst .map (y, u)) .snd
        by refl ((w ↦ k' .fst .map w .snd) : DihedralBaseProduct H h → DihedralBaseSet H h)
             (inverse (DihedralBaseProduct H h) (k .fst .map (y, u)) (dbl_sigma H h k y, dbl_g H h k u) (dbl_decompose H h k y u))
      = u by refl ((w ↦ w .snd) : DihedralBaseProduct H h → DihedralBaseSet H h)
             (equiv_retraction (DihedralBaseProduct H h) (DihedralBaseProduct H h) (k .fst) (y, u)) ∎

def dbl_g_section (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (u : DihedralBaseSet H h)
  : Id (DihedralBaseSet H h) (dbl_g H h k (dbl_g H h (dbl_inverse H h k) u)) u
  ≔ let k' ≔ dbl_inverse H h k in
    let y ≔ s2c3_fin2_yes in
    calc
      dbl_second H h k y (dbl_g H h k' u) = dbl_second H h k (dbl_sigma H h k' y) (dbl_g H h k' u)
        by inverse (DihedralBaseSet H h) (dbl_second H h k (dbl_sigma H h k' y) (dbl_g H h k' u)) (dbl_second H h k y (dbl_g H h k' u))
             (dbl_second_const H h k (dbl_sigma H h k' y) (dbl_g H h k' u))
      = k .fst .map (k' .fst .map (y, u)) .snd
        by refl ((w ↦ k .fst .map w .snd) : DihedralBaseProduct H h → DihedralBaseSet H h)
             (inverse (DihedralBaseProduct H h) (k' .fst .map (y, u)) (dbl_sigma H h k' y, dbl_g H h k' u) (dbl_decompose H h k' y u))
      = u by refl ((w ↦ w .snd) : DihedralBaseProduct H h → DihedralBaseSet H h)
             (equiv_counit (DihedralBaseProduct H h) (DihedralBaseProduct H h) (k .fst) (y, u)) ∎

{` g ∘ f_s = f_{σ s} ∘ g. `}
def dbl_commutes (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (s : dbl_two) (u : DihedralBaseSet H h)
  : Id (DihedralBaseSet H h) (dbl_g H h k (dihedral_move dihedral_two_shape H h s u))
      (dihedral_move dihedral_two_shape H h (dbl_sigma H h k s) (dbl_g H h k u))
  ≔ let f ≔ dihedral_move dihedral_two_shape H h in
    calc
      dbl_g H h k (f s u) = dbl_second H h k s (f s u)
        by inverse (DihedralBaseSet H h) (dbl_second H h k s (f s u)) (dbl_g H h k (f s u)) (dbl_second_const H h k s (f s u))
      = f (dbl_first H h k s u) (dbl_second H h k s u)
        by refl ((w ↦ w .snd) : DihedralBaseProduct H h → DihedralBaseSet H h) (k .snd .fst (s, u))
      = f (dbl_sigma H h k s) (dbl_g H h k u)
        by refl ((w ↦ f (w .fst) (w .snd)) : DihedralBaseProduct H h → DihedralBaseSet H h) (dbl_decompose H h k s u) ∎

def dihedral_frame_decompose (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) : DFrameIsos (dbl_frame H h) (dbl_frame H h)
  ≔ ((quasi_inverse_equiv dbl_two dbl_two (dbl_sigma H h k) (dbl_sigma H h (dbl_inverse H h k))
        (dbl_sigma_retraction H h k) (dbl_sigma_section H h k),
      quasi_inverse_equiv (DihedralBaseSet H h) (DihedralBaseSet H h) (dbl_g H h k) (dbl_g H h (dbl_inverse H h k))
        (dbl_g_retraction H h k) (dbl_g_section H h k)),
     s u ↦ dbl_commutes H h k s u)

def dbl_frame_commutes_prop (H : Subtypes Int) (h : IntegerSubgroupLaws H) (e : DFrameEquivs (dbl_frame H h .fst) (dbl_frame H h .fst))
  : isProp (dframe_commutes_family (dbl_frame H h) (dbl_frame H h) e)
  ≔ pi_prop dbl_two (s ↦ (x : DihedralBaseSet H h) → Id (DihedralBaseSet H h) (e .snd .map (dihedral_move dihedral_two_shape H h s x))
        (dihedral_move dihedral_two_shape H h (e .fst .map s) (e .snd .map x)))
      (s ↦ pi_prop (DihedralBaseSet H h) (x ↦ Id (DihedralBaseSet H h) (e .snd .map (dihedral_move dihedral_two_shape H h s x))
          (dihedral_move dihedral_two_shape H h (e .fst .map s) (e .snd .map x)))
        (x ↦ dihedral_cycle_set_set dihedral_two_shape H h (e .snd .map (dihedral_move dihedral_two_shape H h s x))
          (dihedral_move dihedral_two_shape H h (e .fst .map s) (e .snd .map x))))

def dbl_decompose_product (H : Subtypes Int) (h : IntegerSubgroupLaws H) (e : DFrameIsos (dbl_frame H h) (dbl_frame H h))
  : Id (DFrameIsos (dbl_frame H h) (dbl_frame H h)) (dihedral_frame_decompose H h (dihedral_frame_product H h e)) e
  ≔ subtype_equal (DFrameEquivs (dbl_frame H h .fst) (dbl_frame H h .fst))
      (dframe_commutes_family (dbl_frame H h) (dbl_frame H h)) (dbl_frame_commutes_prop H h)
      (dihedral_frame_decompose H h (dihedral_frame_product H h e)) e
      (equiv_homotopy dbl_two dbl_two (dihedral_frame_decompose H h (dihedral_frame_product H h e) .fst .fst) (e .fst .fst)
         (s ↦ refl (e .fst .fst .map s)),
       equiv_homotopy (DihedralBaseSet H h) (DihedralBaseSet H h)
         (dihedral_frame_decompose H h (dihedral_frame_product H h e) .fst .snd) (e .fst .snd)
         (u ↦ refl (e .fst .snd .map u)))

def dbl_product_decompose (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (k : BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
  : Id (BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h)) (dihedral_frame_product H h (dihedral_frame_decompose H h k)) k
  ≔ dbc_iso_ext (dbl_bicycle H h) (dbl_bicycle H h) (dihedral_frame_product H h (dihedral_frame_decompose H h k)) k
      (u ↦ inverse (DihedralBaseProduct H h) (k .fst .map (u .fst, u .snd)) (dbl_sigma H h k (u .fst), dbl_g H h k (u .snd))
        (dbl_decompose H h k (u .fst) (u .snd)))

{` Symmetries (σ, g) of x₀ in BD_n correspond to automorphisms of φ(x₀). `}
def dihedral_frame_product_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (DFrameIsos (dbl_frame H h) (dbl_frame H h)) (BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
  ≔ quasi_inverse_equiv (DFrameIsos (dbl_frame H h) (dbl_frame H h)) (BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
      (dihedral_frame_product H h) (dihedral_frame_decompose H h) (dbl_decompose_product H h) (dbl_product_decompose H h)

def dihedral_loops_bicycle_isos_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
      (BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
  ≔ compose_equiv (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
      (DFrameIsos (dbl_frame H h) (dbl_frame H h)) (BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
      (dihedral_classifying_paths_equiv H h (dihedral_classifying_base H h) (dihedral_classifying_base H h))
      (dihedral_frame_product_equiv H h)

{` Ωφ (followed by bicycle_paths_equiv) is this equivalence: on underlying
   maps both send ℓ to (s, u) ↦ (ℓ_S .trr s, ℓ_X .trr u). `}
def dihedral_loops_bicycle_isos_agree (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (l : Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
  : Id (BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h))
      (bicycle_paths_equiv (dbl_bicycle H h) (dbl_bicycle H h) .map (refl (dihedral_bicycle H h) l))
      (dihedral_loops_bicycle_isos_equiv H h .map l)
  ≔ dbc_iso_ext (dbl_bicycle H h) (dbl_bicycle H h)
      (bicycle_paths_equiv (dbl_bicycle H h) (dbl_bicycle H h) .map (refl (dihedral_bicycle H h) l))
      (dihedral_loops_bicycle_isos_equiv H h .map l)
      (u ↦ refl (l .fst .fst .fst .trr (u .fst), l .snd .fst .fst .fst .trr (u .snd)))

def dbl_component_paths_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
             (dihedral_bicycle_map H h (dihedral_classifying_base H h)))
      (Id Bicycles (dbl_bicycle H h) (dbl_bicycle H h))
  ≔ subtype_path_equiv Bicycles (B ↦ Mere (Id Bicycles (dihedral_standard_bicycle H h) B))
      (B ↦ mere_isprop (Id Bicycles (dihedral_standard_bicycle H h) B))
      (dihedral_bicycle_map H h (dihedral_classifying_base H h)) (dihedral_bicycle_map H h (dihedral_classifying_base H h))

def dbl_loops_target_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
      (Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
        (dihedral_bicycle_map H h (dihedral_classifying_base H h)))
  ≔ let P ≔ Id Bicycles (dbl_bicycle H h) (dbl_bicycle H h) in
    let I ≔ BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h) in
    let C ≔ Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
              (dihedral_bicycle_map H h (dihedral_classifying_base H h)) in
    compose_equiv (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h)) I C
      (dihedral_loops_bicycle_isos_equiv H h)
      (compose_equiv I P C (canonical_inverse_equiv P I (bicycle_paths_equiv (dbl_bicycle H h) (dbl_bicycle H h)))
        (canonical_inverse_equiv C P (dbl_component_paths_equiv H h)))

def dbl_loops_target_agree (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (l : Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
  : Id (Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
          (dihedral_bicycle_map H h (dihedral_classifying_base H h)))
      (dbl_loops_target_equiv H h .map l) (refl (dihedral_bicycle_map H h) l)
  ≔ let P ≔ Id Bicycles (dbl_bicycle H h) (dbl_bicycle H h) in
    let I ≔ BicycleIsomorphisms (dbl_bicycle H h) (dbl_bicycle H h) in
    let C ≔ Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
              (dihedral_bicycle_map H h (dihedral_classifying_base H h)) in
    let bp ≔ bicycle_paths_equiv (dbl_bicycle H h) (dbl_bicycle H h) in
    let sub ≔ dbl_component_paths_equiv H h in
    let p2 : Id P (refl (dihedral_bicycle H h) l) (equiv_inverse_map P I bp (dihedral_loops_bicycle_isos_equiv H h .map l))
      ≔ concat P (refl (dihedral_bicycle H h) l) (equiv_inverse_map P I bp (bp .map (refl (dihedral_bicycle H h) l)))
          (equiv_inverse_map P I bp (dihedral_loops_bicycle_isos_equiv H h .map l))
          (equiv_unit P I bp (refl (dihedral_bicycle H h) l))
          (refl (equiv_inverse_map P I bp) (dihedral_loops_bicycle_isos_agree H h l)) in
    let p3 : Id C (refl (dihedral_bicycle_map H h) l)
               (equiv_inverse_map C P sub (equiv_inverse_map P I bp (dihedral_loops_bicycle_isos_equiv H h .map l)))
      ≔ concat C (refl (dihedral_bicycle_map H h) l) (equiv_inverse_map C P sub (sub .map (refl (dihedral_bicycle_map H h) l)))
          (equiv_inverse_map C P sub (equiv_inverse_map P I bp (dihedral_loops_bicycle_isos_equiv H h .map l)))
          (equiv_unit C P sub (refl (dihedral_bicycle_map H h) l))
          (refl (equiv_inverse_map C P sub) p2) in
    inverse C (refl (dihedral_bicycle_map H h) l) (dbl_loops_target_equiv H h .map l) p3

{` Ωφ is a bijection. `}
def dihedral_bicycle_loops_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
      (Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
        (dihedral_bicycle_map H h (dihedral_classifying_base H h)))
  ≔ equiv_change_map (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
      (Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
        (dihedral_bicycle_map H h (dihedral_classifying_base H h)))
      (dbl_loops_target_equiv H h)
      (map_path (DihedralClassifyingType H h) (DihedralBicycleComponent H h) (dihedral_bicycle_map H h)
        (dihedral_classifying_base H h) (dihedral_classifying_base H h))
      (dbl_loops_target_agree H h)

{` φ : BD_n → Bicyc_(standard) is an equivalence. `}
def dihedral_bicycle_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : BookEquiv (DihedralClassifyingType H h) (DihedralBicycleComponent H h)
  ≔ connected_map_equiv_from_loops native_truncation (DihedralClassifyingType H h) (DihedralBicycleComponent H h)
      (dihedral_bicycle_map H h) (dihedral_classifying_connected H h)
      (native_component_connected Bicycles (dihedral_standard_bicycle H h)) (dihedral_classifying_base H h)
      (book_equivalence
        (Id (DihedralClassifyingType H h) (dihedral_classifying_base H h) (dihedral_classifying_base H h))
        (Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_classifying_base H h))
          (dihedral_bicycle_map H h (dihedral_classifying_base H h)))
        (dihedral_bicycle_loops_equiv H h) .equiv)

def dihedral_bicycle_pointed_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : BookPointedEquiv (DihedralClassifyingType H h, dihedral_classifying_base H h)
      (DihedralBicycleComponent H h, component_point Bicycles (dihedral_standard_bicycle H h))
  ≔ (dihedral_bicycle_pointed_map H h, dihedral_bicycle_equiv H h .equiv)

{` con:bidirectional-bicycle: for each order n, a pointed equivalence
   φ : BD_n ≃* Bicyc_(Z/~n ⊔ Z/~n, a, b). `}
def bidirectional_bicycle_pointed_equiv (n : Order)
  : BookPointedEquiv (BG (generalized_dihedral_group n))
      (NativeComponent Bicycles (standard_dihedral_bicycle n), component_point Bicycles (standard_dihedral_bicycle n))
  ≔ dihedral_bicycle_pointed_equiv (order_periods n) (order_subgroup_laws n)

{` The underlying map is the book's φ(S, X, f) = (S × X, a, b). `}
def bidirectional_bicycle_map_value (n : Order) (x : BG (generalized_dihedral_group n) .carrier)
  : Id Bicycles (bidirectional_bicycle_pointed_equiv n .fst .fst x .fst) (dihedral_bicycle (order_periods n) (order_subgroup_laws n) x)
  ≔ refl (dihedral_bicycle (order_periods n) (order_subgroup_laws n) x)
