export "817-dihedral-bicycle-normal"

{` The exercise at congp.tex:189 (the two maps of the implementation of
   con:bidirectional-bicycle are inverse), first part: the orbit sets of
   φ(S, X, f) = (S × X, a, b).

   Y/a and Y/b are the orbit quotients OrbitQuotient Y a, OrbitQuotient Y b
   (module 58: y ~ y' iff ∃ z, y' = a^z y, the book's "y' = a^z(y) for some
   z : Z"). For Y = S × X:
   (S × X)/a ≃ S, [(s, x)] ↦ s (a preserves s, and f_s is transitive on X),
   (S × X)/b ≃ X, [(s, x)] ↦ x (b preserves x, and b(s, x) = (swap s, x)).
   Transitivity of f_s is a proposition about the point of BD_n; it is proved
   at the base point (where X = X_{Fin 2} ≅ Z/~n by module 806) and transported
   along the connectedness of BD_n. `}

{` A function invariant under e is invariant under all powers e^z. `}
def dps_iterate_invariant (A T : Type) (f : A → A) (k : A → T) (inv : (y : A) → Id T (k (f y)) (k y)) (n : Nat) (y : A)
  : Id T (k (iterate A f n y)) (k y)
  ≔ match n [
  | zero. ↦ refl (k y)
  | suc. m ↦ concat T (k (f (iterate A f m y))) (k (iterate A f m y)) (k y) (inv (iterate A f m y))
      (dps_iterate_invariant A T f k inv m y) ]

def dps_power_invariant (A T : Type) (e : Equiv A A) (k : A → T) (inv : (y : A) → Id T (k (e .map y)) (k y)) (z : Int) (y : A)
  : Id T (k (permutation_power A e z y)) (k y)
  ≔ let g ≔ equiv_inverse_map A A e in
    let inv' : (y : A) → Id T (k (g y)) (k y)
         ≔ y ↦ concat T (k (g y)) (k (e .map (g y))) (k y) (inverse T (k (e .map (g y))) (k (g y)) (inv (g y)))
                  (refl k (equiv_counit A A e y)) in
    match z [
    | pos. n ↦ dps_iterate_invariant A T (e .map) k inv n y
    | neg. n ↦ dps_iterate_invariant A T g k inv' (suc. n) y ]

{` The carrier S × X of φ(x) and its two orbit quotients. `}
def DpsProduct (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : Type
  ≔ Product (two_set_carrier (x .fst)) (x .snd .fst .fst .fst)

def DpsOrbitsA (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : Type
  ≔ OrbitQuotient (DpsProduct H h x) (dbc_a H h x)

def DpsOrbitsB (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : Type
  ≔ OrbitQuotient (DpsProduct H h x) (dbc_b H h x)

{` a-orbits preserve s, b-orbits preserve x. `}
def dps_first_respects (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Respects (DpsProduct H h x) (two_set_carrier (x .fst)) (orbit_relation (DpsProduct H h x) (dbc_a H h x)) (y ↦ y .fst)
  ≔ y y' r ↦ mere_rec (OrbitWitness (DpsProduct H h x) (dbc_a H h x) y y') (Id (two_set_carrier (x .fst)) (y .fst) (y' .fst))
      (x .fst .fst .snd (y .fst) (y' .fst))
      (w ↦ inverse (two_set_carrier (x .fst)) (y' .fst) (y .fst)
        (concat (two_set_carrier (x .fst)) (y' .fst) (permutation_power (DpsProduct H h x) (dbc_a H h x) (w .fst) y .fst) (y .fst)
          (refl ((v ↦ v .fst) : DpsProduct H h x → two_set_carrier (x .fst)) (w .snd))
          (dps_power_invariant (DpsProduct H h x) (two_set_carrier (x .fst)) (dbc_a H h x) (v ↦ v .fst)
            (v ↦ refl (v .fst)) (w .fst) y)))
      r

def dps_second_respects (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Respects (DpsProduct H h x) (x .snd .fst .fst .fst) (orbit_relation (DpsProduct H h x) (dbc_b H h x)) (y ↦ y .snd)
  ≔ y y' r ↦ mere_rec (OrbitWitness (DpsProduct H h x) (dbc_b H h x) y y') (Id (x .snd .fst .fst .fst) (y .snd) (y' .snd))
      (x .snd .fst .fst .snd (y .snd) (y' .snd))
      (w ↦ inverse (x .snd .fst .fst .fst) (y' .snd) (y .snd)
        (concat (x .snd .fst .fst .fst) (y' .snd) (permutation_power (DpsProduct H h x) (dbc_b H h x) (w .fst) y .snd) (y .snd)
          (refl ((v ↦ v .snd) : DpsProduct H h x → x .snd .fst .fst .fst) (w .snd))
          (dps_power_invariant (DpsProduct H h x) (x .snd .fst .fst .fst) (dbc_b H h x) (v ↦ v .snd)
            (v ↦ refl (v .snd)) (w .fst) y)))
      r

{` Same x: (s, x) and (s', x) are b-related (s' = s or s' = swap s). `}
def dps_second_reflects_at (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (y y' : DpsProduct H h x) (q : Id (x .snd .fst .fst .fst) (y .snd) (y' .snd))
  (d : Decidable (Id (two_set_carrier (x .fst)) (y' .fst) (y .fst)))
  : OrbitWitness (DpsProduct H h x) (dbc_b H h x) y y'
  ≔ match d [
  | inl. p ↦ (int_zero, (p, inverse (x .snd .fst .fst .fst) (y .snd) (y' .snd) q))
  | inr. n ↦ (pos. (suc. zero.), (two_set_other_is_swap (x .fst) (y .fst) (y' .fst) n,
      inverse (x .snd .fst .fst .fst) (y .snd) (y' .snd) q)) ]

def dps_second_reflects (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (y y' : DpsProduct H h x) (q : Id (x .snd .fst .fst .fst) (y .snd) (y' .snd))
  : Rel (DpsProduct H h x) (orbit_relation (DpsProduct H h x) (dbc_b H h x)) y y'
  ≔ mere (OrbitWitness (DpsProduct H h x) (dbc_b H h x) y y')
      (dps_second_reflects_at H h x y y' q (two_set_decidable (x .fst) (y' .fst) (y .fst)))

{` X is merely inhabited; S is merely inhabited. `}
def dps_set_mere (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Mere (x .snd .fst .fst .fst)
  ≔ mere_rec (Id (S2C3Type (x .fst)) (dihedral_point (x .fst) H h) (x .snd .fst)) (Mere (x .snd .fst .fst .fst))
      (mere_isprop (x .snd .fst .fst .fst))
      (p ↦ mere (x .snd .fst .fst .fst) (p .fst .fst .trr (dihedral_base_point (x .fst) H h)))
      (x .snd .snd)

def dps_first_surjective (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Surjective (DpsProduct H h x) (two_set_carrier (x .fst)) (y ↦ y .fst)
  ≔ s ↦ mere_rec (x .snd .fst .fst .fst)
      (Mere (BookFiber (DpsProduct H h x) (two_set_carrier (x .fst)) (y ↦ y .fst) s))
      (mere_isprop (BookFiber (DpsProduct H h x) (two_set_carrier (x .fst)) (y ↦ y .fst) s))
      (u ↦ mere (BookFiber (DpsProduct H h x) (two_set_carrier (x .fst)) (y ↦ y .fst) s) ((s, u), refl s))
      (dps_set_mere H h x)

def dps_second_surjective (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Surjective (DpsProduct H h x) (x .snd .fst .fst .fst) (y ↦ y .snd)
  ≔ u ↦ mere_rec (two_set_carrier (x .fst))
      (Mere (BookFiber (DpsProduct H h x) (x .snd .fst .fst .fst) (y ↦ y .snd) u))
      (mere_isprop (BookFiber (DpsProduct H h x) (x .snd .fst .fst .fst) (y ↦ y .snd) u))
      (s ↦ mere (BookFiber (DpsProduct H h x) (x .snd .fst .fst .fst) (y ↦ y .snd) u) ((s, u), refl u))
      (dihedral_two_set_mere (x .fst))

{` Transitivity of f_s on X: (s, u) and (s, u') are a-related. `}
def DpsTransitive (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : Type
  ≔ (s : two_set_carrier (x .fst)) (u u' : x .snd .fst .fst .fst) → SameOrbit (DpsProduct H h x) (dbc_a H h x) (s, u) (s, u')

def dps_transitive_prop (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : isProp (DpsTransitive H h x)
  ≔ pi_prop (two_set_carrier (x .fst))
      (s ↦ (u u' : x .snd .fst .fst .fst) → SameOrbit (DpsProduct H h x) (dbc_a H h x) (s, u) (s, u'))
      (s ↦ pi_prop (x .snd .fst .fst .fst) (u ↦ (u' : x .snd .fst .fst .fst) → SameOrbit (DpsProduct H h x) (dbc_a H h x) (s, u) (s, u'))
        (u ↦ pi_prop (x .snd .fst .fst .fst) (u' ↦ SameOrbit (DpsProduct H h x) (dbc_a H h x) (s, u) (s, u'))
          (u' ↦ same_orbit_prop (DpsProduct H h x) (dbc_a H h x) (s, u) (s, u'))))

{` At the base point: ι_s(q + 1) = f_s(ι_s q), so f_s^k(ι_s [w]) = ι_s [w + k]. `}
def dps_insert_succ (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : dbl_two) (q : SubgroupQuotient H h)
  : Id (DihedralBaseSet H h)
      (dihedral_insert dihedral_two_shape H h s (subgroup_translation H h (pos. (suc. zero.)) q))
      (dihedral_move dihedral_two_shape H h s (dihedral_insert dihedral_two_shape H h s q))
  ≔ quotient_prop_induction Int (subgroup_relation H h)
      (q ↦ Id (DihedralBaseSet H h)
        (dihedral_insert dihedral_two_shape H h s (subgroup_translation H h (pos. (suc. zero.)) q))
        (dihedral_move dihedral_two_shape H h s (dihedral_insert dihedral_two_shape H h s q)))
      (q ↦ dihedral_cycle_set_set dihedral_two_shape H h
        (dihedral_insert dihedral_two_shape H h s (subgroup_translation H h (pos. (suc. zero.)) q))
        (dihedral_move dihedral_two_shape H h s (dihedral_insert dihedral_two_shape H h s q)))
      (z ↦ inverse (DihedralBaseSet H h)
        (dihedral_move dihedral_two_shape H h s (dihedral_class dihedral_two_shape H h s z))
        (dihedral_class dihedral_two_shape H h s (int_succ z))
        (dihedral_move_self dihedral_two_shape H h s z))
      q

def dps_int_add_sub (w w' : Int) : Id Int (int_add w (int_sub w' w)) w'
  ≔ concat Int (int_add w (int_sub w' w)) (int_add (int_sub w' w) w) w' (int_add_comm w (int_sub w' w)) (int_sub_add w' w)

def dps_base_orbit (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : dbl_two) (u u' : DihedralBaseSet H h) (w w' : Int)
  (pw : Id (SubgroupQuotient H h) (dihedral_eval dihedral_two_shape H h s u) (subgroup_class H h w))
  (pw' : Id (SubgroupQuotient H h) (dihedral_eval dihedral_two_shape H h s u') (subgroup_class H h w'))
  : OrbitWitness (DihedralBaseProduct H h) (dbc_a H h (dihedral_classifying_base H h)) (s, u) (s, u')
  ≔ let S ≔ dihedral_two_shape in
    let X ≔ DihedralBaseSet H h in
    let P ≔ DihedralBaseProduct H h in
    let a ≔ dbc_a H h (dihedral_classifying_base H h) in
    let e ≔ dihedral_move_equiv S H h s in
    let ι ≔ dihedral_insert S H h s in
    let k ≔ int_sub w' w in
    let at : X → P ≔ dbc_pair_at dbl_two X s in
    (k, calc
      at u' = at (ι (dihedral_eval S H h s u'))
        by refl at (inverse X (ι (dihedral_eval S H h s u')) u' (dihedral_insert_eval S H h s u'))
      = at (ι (subgroup_class H h w')) by refl ((v ↦ at (ι v)) : SubgroupQuotient H h → P) pw'
      = at (ι (subgroup_class H h (int_add w k)))
        by refl ((z ↦ at (ι (subgroup_class H h z))) : Int → P) (inverse Int (int_add w k) w' (dps_int_add_sub w w'))
      = at (ι (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) k (subgroup_class H h w)))
        by refl ((v ↦ at (ι v)) : SubgroupQuotient H h → P) (subgroup_power_class H h k w)
      = at (permutation_power X e k (ι (subgroup_class H h w)))
        by refl at (permutation_power_intertwine (SubgroupQuotient H h) X (subgroup_successor H h) e ι
             (q ↦ dps_insert_succ H h s q) k (subgroup_class H h w))
      = at (permutation_power X e k (ι (dihedral_eval S H h s u)))
        by refl ((v ↦ at (permutation_power X e k (ι v))) : SubgroupQuotient H h → P)
             (inverse (SubgroupQuotient H h) (dihedral_eval S H h s u) (subgroup_class H h w) pw)
      = at (permutation_power X e k u)
        by refl ((v ↦ at (permutation_power X e k v)) : X → P) (dihedral_insert_eval S H h s u)
      = permutation_power P a k (at u)
        by permutation_power_intertwine X P e a at (v ↦ refl (at (dihedral_move S H h s v))) k u ∎)

def dps_transitive_base (H : Subtypes Int) (h : IntegerSubgroupLaws H) : DpsTransitive H h (dihedral_classifying_base H h)
  ≔ s u u' ↦
    let S ≔ dihedral_two_shape in
    let P ≔ DihedralBaseProduct H h in
    let a ≔ dbc_a H h (dihedral_classifying_base H h) in
    let Fb : SubgroupQuotient H h → Type ≔ q ↦ BookFiber Int (SubgroupQuotient H h) (subgroup_class H h) q in
    mere_rec (Fb (dihedral_eval S H h s u)) (SameOrbit P a (s, u) (s, u')) (same_orbit_prop P a (s, u) (s, u'))
      (v ↦ mere_rec (Fb (dihedral_eval S H h s u')) (SameOrbit P a (s, u) (s, u')) (same_orbit_prop P a (s, u) (s, u'))
        (v' ↦ mere (OrbitWitness P a (s, u) (s, u')) (dps_base_orbit H h s u u' (v .fst) (v' .fst) (v .snd) (v' .snd)))
        (quotient_surjective Int (subgroup_relation H h) (dihedral_eval S H h s u')))
      (quotient_surjective Int (subgroup_relation H h) (dihedral_eval S H h s u))

def dps_transitive (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : DpsTransitive H h x
  ≔ mere_transport native_truncation (DihedralClassifyingType H h) (DpsTransitive H h) (dps_transitive_prop H h)
      (dihedral_classifying_base H h) x
      (dihedral_classifying_connected H h .snd (dihedral_classifying_base H h) x)
      (dps_transitive_base H h)

def dps_first_reflects (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (y y' : DpsProduct H h x) (q : Id (two_set_carrier (x .fst)) (y .fst) (y' .fst))
  : Rel (DpsProduct H h x) (orbit_relation (DpsProduct H h x) (dbc_a H h x)) y y'
  ≔ transport (two_set_carrier (x .fst)) (t ↦ SameOrbit (DpsProduct H h x) (dbc_a H h x) y (t, y' .snd))
      (y .fst) (y' .fst) q (dps_transitive H h x (y .fst) (y .snd) (y' .snd))

{` (S × X)/a ≃ S and (S × X)/b ≃ X. `}
def dihedral_orbits_a_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Equiv (DpsOrbitsA H h x) (two_set_carrier (x .fst))
  ≔ quotient_presentation_equiv (DpsProduct H h x) (two_set_carrier (x .fst))
      (orbit_relation (DpsProduct H h x) (dbc_a H h x)) (x .fst .fst .snd) (y ↦ y .fst)
      (dps_first_respects H h x) (dps_first_reflects H h x) (dps_first_surjective H h x)

def dihedral_orbits_b_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Equiv (DpsOrbitsB H h x) (x .snd .fst .fst .fst)
  ≔ quotient_presentation_equiv (DpsProduct H h x) (x .snd .fst .fst .fst)
      (orbit_relation (DpsProduct H h x) (dbc_b H h x)) (x .snd .fst .fst .snd) (y ↦ y .snd)
      (dps_second_respects H h x) (dps_second_reflects H h x) (dps_second_surjective H h x)

{` Litmus: the maps compute on classes. `}
def dihedral_orbits_a_class (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (y : DpsProduct H h x)
  : Id (two_set_carrier (x .fst))
      (dihedral_orbits_a_equiv H h x .map (quotient_class (DpsProduct H h x) (orbit_relation (DpsProduct H h x) (dbc_a H h x)) y))
      (y .fst)
  ≔ refl (y .fst)

def dihedral_orbits_b_class (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (y : DpsProduct H h x)
  : Id (x .snd .fst .fst .fst)
      (dihedral_orbits_b_equiv H h x .map (quotient_class (DpsProduct H h x) (orbit_relation (DpsProduct H h x) (dbc_b H h x)) y))
      (y .snd)
  ≔ refl (y .snd)
