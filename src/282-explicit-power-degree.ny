export "172-power-bundle-degree"
export "153-heavy-transport"
export "223-constructed-circle"

{` circle.tex con:psi-alpha-m (circle.tex:1959-2045), cor:dgm-conncov and the
   sentence after it (circle.tex:2068-2069): the book's explicit clock
   construction of psi_m : Tot(R_m) ≃ S¹ and alpha_m : dg_m ∘ psi_m = p_m, the
   inverse of psi_m, and the explicit equivalence Fin m ≃ dg_m⁻¹(base),
   k ↦ (base, loop⁻ᵏ).  (Module 172 obtains psi_m, alpha_m only by transport
   along a path from the classification of connected coverings.)

   Encoding.  Everything is for an arbitrary C : CircleSignature and m = suc n.
   * The book has dg_m(base) ≡ base.  circle_degree_map is circle_rec, so here
     only beta := circle_degree_boundary C m .fst : dg_m(base) = base.  The
     book's fiber element (base, loop⁻ᵏ) therefore becomes
       (base, loop⁻ᵏ · beta⁻¹) : BookFiber S¹ S¹ dg_m base = Σ z, base = dg_m z,
     with loop⁻ᵏ = loop_power loop (int_neg (pos. k)), the book's integer power.
   * k : Fin m (the literal Sum-encoding) is read as the number
     fin_book_value k < m through fin_book_below_equiv, the enumeration that
     also defines the successor on Fin m (module 130).  R_m(base) is Fin m only
     through the computation rule of circle_rec (power_base_trivialization);
     its points are numbered by power_base_enumeration.
   * psi_m(base,x) ≡ base and the loop values of psi_m, alpha_m hold in the book
     by the computation rules of circle induction; here these are explicit
     identifications (power_psi_base, power_psi_loop, power_alpha_base).

   Contents.
   A. power_degree_explicit_fiber_equiv: the equivalence of circle.tex:2068,
      whose underlying map is literally k ↦ (base, loop⁻ᵏ · beta⁻¹).  Proof:
      module 83's degree_base_fiber_enumeration is this map
      (degree_base_fiber_enumeration_explicit).
   B. The clock (con:psi-alpha-m): power_psi with psi_m(base) = const base and
      psi_m(loop) sending the arc leaving the mark k to refl for k < m-1 and
      to loop for k = m-1; power_alpha with alpha_m(base,k) = loopᵏ in the
      orientation dg_m psi_m = p_m of the statement, i.e. the book's
      alpha_m(base,k) = loop⁻ᵏ in the orientation p_m = dg_m psi_m of the
      implementation (power_alpha_book_base), and with the book's squares
      alpha_m(loop,k) (power_alpha_square); psi_m is an equivalence
      (power_psi_is_equiv); all packaged as power_degree_explicit_comparison.
   C. power_explicit_comparison_fiber_map: xca:preim-eq applied to this
      (psi_m, alpha_m) (module 172's power_comparison_base_fiber_equiv) sends
      k to (base, loop⁻ᵏ · beta⁻¹), as the book says.
   D. The inverse of psi_m as in the book, base ↦ (base,0) and
      loop ↦ a_{m-1}⋯a_0 (closed up by x_m = x_0): power_psi_inverse_map, with
      psi_m ∘ inverse = id (power_psi_section) and hence equal to the inverse of
      the equivalence psi_m (power_psi_inverse_agrees, power_psi_inverse_equiv).
   Two cheap instantiations at constructed_circle close the module. `}

{` ===== A. The explicit equivalence Fin m ≃ dg_m⁻¹(base) ===== `}

{` Transport in the family of book fibers b ↦ f⁻¹(b) = Σ a, b = f a along
   p : b0 = b1 keeps the point and prepends p⁻¹. `}
def book_fiber_transport_formula (A B : Type) (f : A → B) (b0 b1 : B) (p : Id B b0 b1)
  (t : BookFiber A B f b0)
  : Id (BookFiber A B f b1) (transport B (BookFiber A B f) b0 b1 p t)
      (t .fst, concat B b1 b0 (f (t .fst)) (inverse B b0 b1 p) (t .snd))
  ≔ J B b0
      (b1 p ↦ Id (BookFiber A B f b1) (transport B (BookFiber A B f) b0 b1 p t)
        (t .fst, concat B b1 b0 (f (t .fst)) (inverse B b0 b1 p) (t .snd)))
      (concat (BookFiber A B f b0) (transport B (BookFiber A B f) b0 b0 (refl b0) t) t
        (t .fst, concat B b0 b0 (f (t .fst)) (inverse B b0 b0 (refl b0)) (t .snd))
        (transport_refl B (BookFiber A B f) b0 t)
        (refl (t .fst), inverse (Id B b0 (f (t .fst)))
          (concat B b0 b0 (f (t .fst)) (inverse B b0 b0 (refl b0)) (t .snd)) (t .snd)
          (concat (Id B b0 (f (t .fst)))
            (concat B b0 b0 (f (t .fst)) (inverse B b0 b0 (refl b0)) (t .snd))
            (concat B b0 b0 (f (t .fst)) (refl b0) (t .snd)) (t .snd)
            (refl ((r ↦ concat B b0 b0 (f (t .fst)) r (t .snd)) : Id B b0 b0 → Id B b0 (f (t .fst)))
              (inverse_refl B b0))
            (concat_1p B b0 (f (t .fst)) (t .snd)))))
      b1 p

{` A loop commutes with its own powers: l · lᵏ = lᵏ⁺¹ (= lᵏ · l). `}
def loop_power_nat_succ_left (A : Type) (a : A) (l : Id A a a) (j : Nat)
  : Id (Id A a a) (concat A a a a l (loop_power_nat A a l j)) (loop_power_nat A a l (suc. j))
  ≔ match j [
  | zero. ↦ concat (Id A a a) (concat A a a a l (refl a)) l (concat A a a a (refl a) l)
      (concat_p1 A a a l) (inverse (Id A a a) (concat A a a a (refl a) l) l (concat_1p A a a l))
  | suc. j ↦ concat (Id A a a)
      (concat A a a a l (concat A a a a (loop_power_nat A a l j) l))
      (concat A a a a (concat A a a a l (loop_power_nat A a l j)) l)
      (concat A a a a (loop_power_nat A a l (suc. j)) l)
      (inverse (Id A a a) (concat A a a a (concat A a a a l (loop_power_nat A a l j)) l)
        (concat A a a a l (concat A a a a (loop_power_nat A a l j) l))
        (concat_assoc A a a a a l (loop_power_nat A a l j) l))
      (refl ((r ↦ concat A a a a r l) : Id A a a → Id A a a) (loop_power_nat_succ_left A a l j)) ]

{` The book's loop⁻ᵏ, an integer power, is the k-th power of loop⁻¹. `}
def loop_negative_power_nat (A : Type) (a : A) (l : Id A a a) (k : Nat)
  : Id (Id A a a) (loop_power A a l (int_neg (pos. k))) (loop_power_nat A a (inverse A a a l) k)
  ≔ match k [
  | zero. ↦ refl (refl a)
  | suc. k ↦ refl (loop_power_nat A a (inverse A a a l) (suc. k)) ]

{` The number < n denoted by k : Fin n (standard enumeration). `}
def fin_book_value (n : Nat) (k : Fin n) : Nat ≔ fin_book_below_equiv n .map k .fst

{` Iterating the monodromy of the degree covering (transport along loop
   in b ↦ dg_m⁻¹(b)) j times prepends (loop⁻¹)ʲ. `}
def degree_fiber_monodromy_power (C : CircleSignature) (m : Nat) (j : Nat) (a : C .carrier)
  (u : Id (C .carrier) (C .base) (circle_degree_map C m a))
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C m) (C .base))
      (iterate (BookFiber (C .carrier) (C .carrier) (circle_degree_map C m) (C .base))
        (transport (C .carrier) (BookFiber (C .carrier) (C .carrier) (circle_degree_map C m)) (C .base) (C .base) (C .loop))
        j (a, u))
      (a, concat (C .carrier) (C .base) (C .base) (circle_degree_map C m a)
        (loop_power_nat (C .carrier) (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop)) j) u)
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let f ≔ circle_degree_map C m in
    let D ≔ BookFiber S S f b in
    let L ≔ inverse S b b (C .loop) in
    let sigma ≔ transport S (BookFiber S S f) b b (C .loop) in
    match j [
    | zero. ↦ (refl a, inverse (Id S b (f a)) (concat S b b (f a) (refl b) u) u (concat_1p S b (f a) u))
    | suc. j ↦ concat D (sigma (iterate D sigma j (a, u)))
        (sigma (a, concat S b b (f a) (loop_power_nat S b L j) u))
        (a, concat S b b (f a) (loop_power_nat S b L (suc. j)) u)
        (refl sigma (degree_fiber_monodromy_power C m j a u))
        (concat D (sigma (a, concat S b b (f a) (loop_power_nat S b L j) u))
          (a, concat S b b (f a) L (concat S b b (f a) (loop_power_nat S b L j) u))
          (a, concat S b b (f a) (loop_power_nat S b L (suc. j)) u)
          (book_fiber_transport_formula S S f b b (C .loop) (a, concat S b b (f a) (loop_power_nat S b L j) u))
          (refl a, concat (Id S b (f a))
            (concat S b b (f a) L (concat S b b (f a) (loop_power_nat S b L j) u))
            (concat S b b (f a) (concat S b b b L (loop_power_nat S b L j)) u)
            (concat S b b (f a) (loop_power_nat S b L (suc. j)) u)
            (inverse (Id S b (f a)) (concat S b b (f a) (concat S b b b L (loop_power_nat S b L j)) u)
              (concat S b b (f a) L (concat S b b (f a) (loop_power_nat S b L j) u))
              (concat_assoc S b b b (f a) L (loop_power_nat S b L j) u))
            (refl ((r ↦ concat S b b (f a) r u) : Id S b b → Id S b (f a))
              (loop_power_nat_succ_left S b L j)))) ]

{` A map commuting with two permutations commutes with their iterates. `}
def commuting_map_iterate (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : A → B)
  (hc : Commutes A B e f h) (j : Nat) (x : A)
  : Id B (h (iterate A (e .map) j x)) (iterate B (f .map) j (h x))
  ≔ match j [
  | zero. ↦ refl (h x)
  | suc. j ↦ concat B (h (e .map (iterate A (e .map) j x))) (f .map (h (iterate A (e .map) j x)))
      (f .map (iterate B (f .map) j (h x)))
      (hc (iterate A (e .map) j x)) (refl (f .map) (commuting_map_iterate A B e f h hc j x)) ]

{` The enumeration of module 83 sends the remainder 0 to the base point
   (base, beta⁻¹): this is how its cycle path was chosen. `}
def degree_enumeration_base_point (C : CircleSignature) (n : Nat)
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (cycle_paths_equiv (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
        .map (degree_cover_standard_cycle C n) .fst .map (remainder_at n zero. star.))
      (degree_cover_base_point C (suc. n) (lt_to_book zero. (suc. n) star.))
  ≔ let pos ≔ lt_to_book zero. (suc. n) star. in
    let c ≔ finite_standard_cycle n in
    let d ≔ degree_cover_cycle C (suc. n) pos in
    let H ≔ concat (Subtypes Int) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n))
        (CyclePeriods (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.)))
        (finite_standard_periods n)
        (inverse (Subtypes Int) (CyclePeriods (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.)))
          (Multiples (suc. n)) (degree_cover_periods C (suc. n) (lt_to_book zero. (suc. n) star.))) in
    inverse (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (degree_cover_base_point C (suc. n) pos)
      (cycle_path_evaluate c d (degree_cover_standard_cycle C n) (remainder_at n zero. star.))
      (cycle_evaluation_from_periods c d H (remainder_at n zero. star.) .equiv
        (degree_cover_base_point C (suc. n) pos) .center .snd)

{` The enumeration of module 83 at a remainder r is (base, (loop⁻¹)^r · beta⁻¹):
   it commutes with the successor and the monodromy, and the monodromy
   prepends loop⁻¹. `}
def degree_enumeration_value (C : CircleSignature) (n : Nat) (r : Remainder (suc. n))
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (cycle_paths_equiv (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
        .map (degree_cover_standard_cycle C n) .fst .map r)
      (C .base, concat (C .carrier) (C .base) (C .base) (circle_degree_map C (suc. n) (C .base))
        (loop_power_nat (C .carrier) (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop)) (r .fst))
        (inverse (C .carrier) (circle_degree_map C (suc. n) (C .base)) (C .base) (circle_degree_boundary C (suc. n) .fst)))
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let f ≔ circle_degree_map C (suc. n) in
    let D ≔ BookFiber S S f b in
    let pos ≔ lt_to_book zero. (suc. n) star. in
    let c ≔ finite_standard_cycle n in
    let d ≔ degree_cover_cycle C (suc. n) pos in
    let iso ≔ cycle_paths_equiv c d .map (degree_cover_standard_cycle C n) in
    let x0 ≔ remainder_at n zero. star. in
    let h ≔ lt_from_book (r .fst) (suc. n) (r .snd) in
    let sigma ≔ transport S (BookFiber S S f) b b (C .loop) in
    calc
      iso .fst .map r
      = iso .fst .map (remainder_at n (r .fst) h)
        by refl (iso .fst .map) (remainder_equal (suc. n) r (remainder_at n (r .fst) h) (refl (r .fst)))
      = iso .fst .map (iterate (Remainder (suc. n)) (modular_successor n) (r .fst) x0)
        by refl (iso .fst .map) (inverse (Remainder (suc. n))
          (iterate (Remainder (suc. n)) (modular_successor n) (r .fst) x0) (remainder_at n (r .fst) h)
          (modular_successor_iterate n (r .fst) h))
      = iterate D sigma (r .fst) (iso .fst .map x0)
        by commuting_map_iterate (Remainder (suc. n)) D (modular_successor_equiv n) (d .fst .snd)
          (iso .fst .map) (iso .snd) (r .fst) x0
      = iterate D sigma (r .fst) (degree_cover_base_point C (suc. n) pos)
        by refl (iterate D sigma (r .fst)) (degree_enumeration_base_point C n)
      = (b, concat S b b (f b) (loop_power_nat S b (inverse S b b (C .loop)) (r .fst))
          (inverse S (f b) b (circle_degree_boundary C (suc. n) .fst)))
        by degree_fiber_monodromy_power C (suc. n) (r .fst) b (inverse S (f b) b (circle_degree_boundary C (suc. n) .fst)) ∎

{` The book's formula on remainders r < m: r ↦ (base, loop⁻ʳ · beta⁻¹). `}
def power_degree_explicit_remainder_map (C : CircleSignature) (n : Nat) (r : Remainder (suc. n))
  : BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base)
  ≔ (C .base, concat (C .carrier) (C .base) (C .base) (circle_degree_map C (suc. n) (C .base))
      (loop_power (C .carrier) (C .base) (C .loop) (int_neg (pos. (r .fst))))
      (inverse (C .carrier) (circle_degree_map C (suc. n) (C .base)) (C .base) (circle_degree_boundary C (suc. n) .fst)))

def degree_enumeration_explicit (C : CircleSignature) (n : Nat) (r : Remainder (suc. n))
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (cycle_paths_equiv (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
        .map (degree_cover_standard_cycle C n) .fst .map r)
      (power_degree_explicit_remainder_map C n r)
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let f ≔ circle_degree_map C (suc. n) in
    let bi ≔ inverse S (f b) b (circle_degree_boundary C (suc. n) .fst) in
    concat (BookFiber S S f b)
      (cycle_paths_equiv (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
        .map (degree_cover_standard_cycle C n) .fst .map r)
      (b, concat S b b (f b) (loop_power_nat S b (inverse S b b (C .loop)) (r .fst)) bi)
      (power_degree_explicit_remainder_map C n r)
      (degree_enumeration_value C n r)
      (refl b, refl ((q ↦ concat S b b (f b) q bi) : Id S b b → Id S b (f b))
        (inverse (Id S b b) (loop_power S b (C .loop) (int_neg (pos. (r .fst))))
          (loop_power_nat S b (inverse S b b (C .loop)) (r .fst))
          (loop_negative_power_nat S b (C .loop) (r .fst))))

{` Remainders below m ≃ dg_m⁻¹(base), with the book's map on the nose. `}
def power_degree_explicit_remainder_equiv (C : CircleSignature) (n : Nat)
  : Equiv (Remainder (suc. n)) (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
  ≔ equiv_change_map (Remainder (suc. n)) (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (cycle_paths_equiv (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
        .map (degree_cover_standard_cycle C n) .fst)
      (power_degree_explicit_remainder_map C n) (degree_enumeration_explicit C n)

{` The explicit map of circle.tex:2068 on the literal Fin m:
   k ↦ (base, loop⁻ᵏ · beta⁻¹), k read as the number fin_book_value k < m. `}
def power_degree_explicit_fiber_map (C : CircleSignature) (n : Nat) (k : Fin (suc. n))
  : BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base)
  ≔ (C .base, concat (C .carrier) (C .base) (C .base) (circle_degree_map C (suc. n) (C .base))
      (loop_power (C .carrier) (C .base) (C .loop) (int_neg (pos. (fin_book_value (suc. n) k))))
      (inverse (C .carrier) (circle_degree_map C (suc. n) (C .base)) (C .base) (circle_degree_boundary C (suc. n) .fst)))

{` The explicit equivalence Fin m ≃ dg_m⁻¹(base) after cor:dgm-conncov. `}
def power_degree_explicit_fiber_equiv (C : CircleSignature) (n : Nat)
  : Equiv (Fin (suc. n)) (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
  ≔ equiv_change_map (Fin (suc. n)) (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (compose_equiv (Fin (suc. n)) (Remainder (suc. n))
        (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
        (fin_book_below_equiv (suc. n)) (power_degree_explicit_remainder_equiv C n))
      (power_degree_explicit_fiber_map C n)
      (k ↦ refl (power_degree_explicit_fiber_map C n k))

{` Its underlying map is literally the displayed formula. `}
def power_degree_explicit_fiber_equiv_map (C : CircleSignature) (n : Nat) (k : Fin (suc. n))
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (power_degree_explicit_fiber_equiv C n .map k)
      (C .base, concat (C .carrier) (C .base) (C .base) (circle_degree_map C (suc. n) (C .base))
        (loop_power (C .carrier) (C .base) (C .loop) (int_neg (pos. (fin_book_value (suc. n) k))))
        (inverse (C .carrier) (circle_degree_map C (suc. n) (C .base)) (C .base) (circle_degree_boundary C (suc. n) .fst)))
  ≔ refl (power_degree_explicit_fiber_map C n k)

{` The enumeration degree_base_fiber_enumeration of module 83 (obtained
   from the classification of cycles) is this explicit map. `}
def degree_base_fiber_enumeration_explicit (C : CircleSignature) (n : Nat) (k : Fin (suc. n))
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (degree_base_fiber_enumeration C n .map k) (power_degree_explicit_fiber_map C n k)
  ≔ degree_enumeration_explicit C n (fin_book_below_equiv (suc. n) .map k)

{` ===== B. con:psi-alpha-m: the clock construction of psi_m and alpha_m ===== `}

{` The fiber R_m(z) of the power bundle (def:RmtoS1, module 171). `}
def power_fiber (C : CircleSignature) (n : Nat) (z : C .carrier) : Type ≔ power_circle_family C n z .fst

{` R_m(base) is Fin m only up to the computation rule of circle_rec;
   its points are numbered by trivializing and then reading Fin m as
   remainders below m. `}
def power_base_enumeration (C : CircleSignature) (n : Nat)
  : Equiv (power_fiber C n (C .base)) (Remainder (suc. n))
  ≔ compose_equiv (power_fiber C n (C .base)) (Fin (suc. n)) (Remainder (suc. n))
      (power_base_trivialization C n) (fin_book_below_equiv (suc. n))

def power_base_value (C : CircleSignature) (n : Nat) (x : power_fiber C n (C .base)) : Nat
  ≔ power_base_enumeration C n .map x .fst

{` A path of free loops of sets intertwines the two transports. `}
def set_freeloop_path_transport (u v : FreeLoop SetTypes) (w : Id (FreeLoop SetTypes) u v) (y : u .fst .fst)
  : Id (v .fst .fst) (w .fst .fst .trr (u .snd .fst .trr y)) (v .snd .fst .trr (w .fst .fst .trr y))
  ≔ J (FreeLoop SetTypes) u
      (v w ↦ (y : u .fst .fst)
        → Id (v .fst .fst) (w .fst .fst .trr (u .snd .fst .trr y)) (v .snd .fst .trr (w .fst .fst .trr y)))
      (y ↦ calc
        transport Type (X ↦ X) (u .fst .fst) (u .fst .fst) (refl (u .fst .fst)) (u .snd .fst .trr y)
        = u .snd .fst .trr y by transport_refl Type (X ↦ X) (u .fst .fst) (u .snd .fst .trr y)
        = u .snd .fst .trr (transport Type (X ↦ X) (u .fst .fst) (u .fst .fst) (refl (u .fst .fst)) y)
          by refl (u .snd .fst .trr) (transport_refl Type (X ↦ X) (u .fst .fst) y) ∎)
      v w y

{` Transport in R_m along loop is the successor k ↦ k+1 mod m. `}
def power_monodromy_trivialization (C : CircleSignature) (n : Nat) (y : power_fiber C n (C .base))
  : Id (Fin (suc. n))
      (power_base_trivialization C n .map (transport (C .carrier) (power_fiber C n) (C .base) (C .base) (C .loop) y))
      (finite_fin_successor n .map (power_base_trivialization C n .map y))
  ≔ set_freeloop_path_transport (circle_eval C SetTypes (power_circle_family C n))
      (power_fiber_set n, power_fiber_rotation n) (power_circle_family_beta C n) y

def power_enumeration_monodromy (C : CircleSignature) (n : Nat) (y : power_fiber C n (C .base))
  : Id (Remainder (suc. n))
      (power_base_enumeration C n .map (transport (C .carrier) (power_fiber C n) (C .base) (C .base) (C .loop) y))
      (modular_successor n (power_base_enumeration C n .map y))
  ≔ let fb ≔ fin_book_below_equiv (suc. n) in
    let t ≔ power_base_trivialization C n in
    calc
      fb .map (t .map (transport (C .carrier) (power_fiber C n) (C .base) (C .base) (C .loop) y))
      = fb .map (finite_fin_successor n .map (t .map y))
        by refl (fb .map) (power_monodromy_trivialization C n y)
      = modular_successor n (fb .map (t .map y))
        by equiv_counit (Fin (suc. n)) (Remainder (suc. n)) fb (modular_successor n (fb .map (t .map y))) ∎

{` The clock: the arc leaving the mark k goes to refl for k < m-1 and
   to loop for k = m-1 (red labels of fig:m-power-clock). `}
def power_clock_split (C : CircleSignature) (n k : Nat) (s : Sum (Lt k n) (Id Nat k n))
  : Id (C .carrier) (C .base) (C .base)
  ≔ match s [ inl. _ ↦ refl (C .base) | inr. _ ↦ C .loop ]

def power_clock (C : CircleSignature) (n : Nat) (x : power_fiber C n (C .base))
  : Id (C .carrier) (C .base) (C .base)
  ≔ power_clock_split C n (power_base_value C n x)
      (le_split (power_base_value C n x) n
        (lt_from_book (power_base_value C n x) (suc. n) (power_base_enumeration C n .map x .snd)))

{` psi_m as an element of Π(z:S¹) (R_m(z) → S¹), by circle induction:
   psi_m(base) = const base, and psi_m(loop) sends a dependent path
   x2 : x0 =_{loop} x1 of R_m to the clock value of its source x0. `}
def power_psi_family (C : CircleSignature) (n : Nat) : C .carrier → Type
  ≔ z ↦ (power_fiber C n z → C .carrier)

def power_psi_datum (C : CircleSignature) (n : Nat)
  : CircleBoundary (C .carrier) (C .base) (C .loop) (power_psi_family C n)
  ≔ ((_ ↦ C .base), x ⤇ power_clock C n x.0)

def power_psi_curried (C : CircleSignature) (n : Nat) : (z : C .carrier) → power_psi_family C n z
  ≔ C .induction (power_psi_family C n) (power_psi_datum C n) .fst

{` con:psi-alpha-m: psi_m : Tot(R_m) → S¹. `}
def power_psi (C : CircleSignature) (n : Nat) (t : PowerBundleTotal C n) : C .carrier
  ≔ power_psi_curried C n (t .fst) (t .snd)

{` psi_m(base,x) = base: the base part of the computation rule. `}
def power_psi_base (C : CircleSignature) (n : Nat) (x : power_fiber C n (C .base))
  : Id (C .carrier) (power_psi C n (C .base, x)) (C .base)
  ≔ C .induction (power_psi_family C n) (power_psi_datum C n) .snd .fst (refl x)

{` Reading off the loop part of a boundary identification of maps
   R_m(z) → Y: the value on an arc is conjugated by the base paths. `}
def power_psi_boundary_loop (C : CircleSignature) (n : Nat)
  (u v : power_fiber C n (C .base) → C .carrier) (pq : Id (power_fiber C n (C .base) → C .carrier) u v)
  (r : Id (power_psi_family C n) (C .loop) u u) (s : Id (power_psi_family C n) (C .loop) v v)
  (w : Id ((g ↦ Id (power_psi_family C n) (C .loop) g g) : (power_fiber C n (C .base) → C .carrier) → Type) pq r s)
  (x0 x1 : power_fiber C n (C .base)) (x2 : Id (power_fiber C n) (C .loop) x0 x1)
  : Id (Id (C .carrier) (v x0) (v x1)) (s x2)
      (concat (C .carrier) (v x0) (u x0) (v x1) (inverse (C .carrier) (u x0) (v x0) (pq (refl x0)))
        (concat (C .carrier) (u x0) (u x1) (v x1) (r x2) (pq (refl x1))))
  ≔ J (power_fiber C n (C .base) → C .carrier) u
      (v pq ↦ (s : Id (power_psi_family C n) (C .loop) v v)
        → Id ((g ↦ Id (power_psi_family C n) (C .loop) g g) : (power_fiber C n (C .base) → C .carrier) → Type) pq r s
        → Id (Id (C .carrier) (v x0) (v x1)) (s x2)
            (concat (C .carrier) (v x0) (u x0) (v x1) (inverse (C .carrier) (u x0) (v x0) (pq (refl x0)))
              (concat (C .carrier) (u x0) (u x1) (v x1) (r x2) (pq (refl x1)))))
      (s w ↦ calc
        s x2
        = r x2
          by refl ((z ↦ z x2) : Id (power_psi_family C n) (C .loop) u u → Id (C .carrier) (u x0) (u x1)) w
        = concat (C .carrier) (u x0) (u x1) (u x1) (r x2) (refl (u x1))
          by concat_p1 (C .carrier) (u x0) (u x1) (r x2)
        = concat (C .carrier) (u x0) (u x0) (u x1) (refl (u x0))
            (concat (C .carrier) (u x0) (u x1) (u x1) (r x2) (refl (u x1)))
          by concat_1p (C .carrier) (u x0) (u x1) (concat (C .carrier) (u x0) (u x1) (u x1) (r x2) (refl (u x1)))
        = concat (C .carrier) (u x0) (u x0) (u x1) (inverse (C .carrier) (u x0) (u x0) (refl (u x0)))
            (concat (C .carrier) (u x0) (u x1) (u x1) (r x2) (refl (u x1)))
          by refl ((q ↦ concat (C .carrier) (u x0) (u x0) (u x1) q
                (concat (C .carrier) (u x0) (u x1) (u x1) (r x2) (refl (u x1))))
              : Id (C .carrier) (u x0) (u x0) → Id (C .carrier) (u x0) (u x1))
            (inverse_refl (C .carrier) (u x0)) ∎)
      v pq s w

{` psi_m on an arc (loop, x2) : (base,x0) = (base,x1) of Tot(R_m) is the
   clock value of x0, up to the base paths psi_m(base,xi) = base. `}
def power_psi_loop (C : CircleSignature) (n : Nat) (x0 x1 : power_fiber C n (C .base))
  (x2 : Id (power_fiber C n) (C .loop) x0 x1)
  : Id (Id (C .carrier) (C .base) (C .base)) (power_clock C n x0)
      (concat (C .carrier) (C .base) (power_psi C n (C .base, x0)) (C .base)
        (inverse (C .carrier) (power_psi C n (C .base, x0)) (C .base) (power_psi_base C n x0))
        (concat (C .carrier) (power_psi C n (C .base, x0)) (power_psi C n (C .base, x1)) (C .base)
          (refl (power_psi C n)
            ((C .loop, x2) : Id (PowerBundleTotal C n) (C .base, x0) (C .base, x1)))
          (power_psi_base C n x1)))
  ≔ let ind ≔ C .induction (power_psi_family C n) (power_psi_datum C n) in
    power_psi_boundary_loop C n (ind .fst (C .base)) (_ ↦ C .base) (ind .snd .fst)
      (refl (ind .fst) (C .loop)) (power_psi_datum C n .snd) (ind .snd .snd) x0 x1 x2

{` p · (p⁻¹ · q) = q. `}
def concat_right_inverse_cancel (A : Type) (x y z : A) (p : Id A x y) (q : Id A x z)
  : Id (Id A x z) (concat A x y z p (concat A y x z (inverse A x y p) q)) q
  ≔ calc
      concat A x y z p (concat A y x z (inverse A x y p) q)
      = concat A x x z (concat A x y x p (inverse A x y p)) q by concat_assoc A x y x z p (inverse A x y p) q
      = concat A x x z (refl x) q
        by refl ((r ↦ concat A x x z r q) : Id A x x → Id A x z) (concat_inverse_right A x y p)
      = q by concat_1p A x z q ∎

{` The squares alpha_m(loop,k) of fig:psi-alpha-m-help, with the base
   paths removed: with a_k := dg_m(clock_k)⁻¹, the composite
   a_k · (beta · loopᵏ⁰) · loop equals beta · loopᵏ¹, where k1 = k0+1 mod m. `}
def PowerClockKey (C : CircleSignature) (n : Nat) (c : Id (C .carrier) (C .base) (C .base)) (k0 k1 : Nat) : Type
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let f ≔ circle_degree_map C (suc. n) in
    let bt ≔ circle_degree_boundary C (suc. n) .fst in
    Id (Id S (f b) b)
      (concat S (f b) (f b) b (inverse S (f b) (f b) (refl f c))
        (concat S (f b) b b (concat S (f b) b b bt (loop_power_nat S b (C .loop) k0)) (C .loop)))
      (concat S (f b) b b bt (loop_power_nat S b (C .loop) k1))

{` k < m-1: the "trivial proof" refl·loop⁻ᵏ = loop⁻⁽ᵏ⁺¹⁾·loop, reoriented. `}
def power_clock_key_small (C : CircleSignature) (n k0 : Nat) : PowerClockKey C n (refl (C .base)) k0 (suc. k0)
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let f ≔ circle_degree_map C (suc. n) in
    let bt ≔ circle_degree_boundary C (suc. n) .fst in
    let X ≔ concat S (f b) b b (concat S (f b) b b bt (loop_power_nat S b (C .loop) k0)) (C .loop) in
    calc
      concat S (f b) (f b) b (inverse S (f b) (f b) (refl (f b))) X
      = concat S (f b) (f b) b (refl (f b)) X
        by refl ((q ↦ concat S (f b) (f b) b q X) : Id S (f b) (f b) → Id S (f b) b) (inverse_refl S (f b))
      = X by concat_1p S (f b) b X
      = concat S (f b) b b bt (concat S b b b (loop_power_nat S b (C .loop) k0) (C .loop))
        by concat_assoc S (f b) b b b bt (loop_power_nat S b (C .loop) k0) (C .loop) ∎

{` k = m-1: the proof that loop^m · loop⁻⁽ᵐ⁻¹⁾ = loop⁻⁰ · loop, reoriented;
   it uses dg_m(loop) = loop^m (circle_degree_action_is_power). `}
def power_clock_key_last (C : CircleSignature) (n : Nat) : PowerClockKey C n (C .loop) n zero.
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let l ≔ C .loop in
    let f ≔ circle_degree_map C (suc. n) in
    let bt ≔ circle_degree_boundary C (suc. n) .fst in
    let al ≔ refl f l in
    let ln ≔ loop_power_nat S b l n in
    let conj : Id (Id S b b) (concat S b (f b) b (inverse S (f b) b bt) (concat S (f b) (f b) b al bt))
        (concat S b b b ln l)
      ≔ calc
          concat S b (f b) b (inverse S (f b) b bt) (concat S (f b) (f b) b al bt)
          = transport S (x ↦ Id S x x) (f b) b bt al by transport_conjugation S (f b) b bt al
          = loop_power_nat S b l (suc. n) by circle_degree_action_is_power C (suc. n) l ∎ in
    calc
      concat S (f b) (f b) b (inverse S (f b) (f b) al) (concat S (f b) b b (concat S (f b) b b bt ln) l)
      = concat S (f b) (f b) b (inverse S (f b) (f b) al) (concat S (f b) b b bt (concat S b b b ln l))
        by refl (concat S (f b) (f b) b (inverse S (f b) (f b) al)) (concat_assoc S (f b) b b b bt ln l)
      = concat S (f b) (f b) b (inverse S (f b) (f b) al)
          (concat S (f b) b b bt (concat S b (f b) b (inverse S (f b) b bt) (concat S (f b) (f b) b al bt)))
        by refl ((q ↦ concat S (f b) (f b) b (inverse S (f b) (f b) al) (concat S (f b) b b bt q))
            : Id S b b → Id S (f b) b) conj
      = concat S (f b) (f b) b (inverse S (f b) (f b) al) (concat S (f b) (f b) b al bt)
        by refl (concat S (f b) (f b) b (inverse S (f b) (f b) al))
          (concat_right_inverse_cancel S (f b) b b bt (concat S (f b) (f b) b al bt))
      = bt by concat_left_inverse S (f b) (f b) b al bt
      = concat S (f b) b b bt (refl b) by concat_p1 S (f b) b bt ∎

def power_clock_key (C : CircleSignature) (n k0 : Nat) (h0 : Le k0 n) (s : Sum (Lt k0 n) (Id Nat k0 n))
  (k1 : Nat) (hk1 : Id Nat k1 (modular_successor n (remainder_at n k0 h0) .fst))
  : PowerClockKey C n (power_clock_split C n k0 s) k0 k1
  ≔ match s [
  | inl. small ↦ transport Nat (k ↦ PowerClockKey C n (refl (C .base)) k0 k) (suc. k0) k1
      (inverse Nat k1 (suc. k0)
        (concat Nat k1 (modular_successor n (remainder_at n k0 h0) .fst) (suc. k0) hk1
          (modular_successor_small n k0 small h0 .fst)))
      (power_clock_key_small C n k0)
  | inr. last ↦ transport Nat (k ↦ PowerClockKey C n (C .loop) k k1) n k0 (inverse Nat k0 n last)
      (transport Nat (k ↦ PowerClockKey C n (C .loop) n k) zero. k1
        (inverse Nat k1 zero.
          (concat Nat k1 (modular_successor n (remainder_at n k0 h0) .fst) zero. hk1
            (concat Nat (modular_successor n (remainder_at n k0 h0) .fst)
              (modular_successor n (remainder_at n n (le_refl n)) .fst) zero.
              (refl ((r ↦ modular_successor n r .fst) : Remainder (suc. n) → Nat)
                (remainder_equal (suc. n) (remainder_at n k0 h0) (remainder_at n n (le_refl n)) last))
              (modular_successor_last n .fst))))
        (power_clock_key_last C n)) ]

{` The successor relation along an arc of R_m.  (Stated with explicit
   concatenations: letting calc guess orientations here is very slow.) `}
def power_value_successor (C : CircleSignature) (n : Nat) (x0 x1 : power_fiber C n (C .base))
  (x2 : Id (power_fiber C n) (C .loop) x0 x1)
  : Id Nat (power_base_value C n x1)
      (modular_successor n (remainder_at n (power_base_value C n x0)
        (lt_from_book (power_base_value C n x0) (suc. n) (power_base_enumeration C n .map x0 .snd))) .fst)
  ≔ let tx0 ≔ transport (C .carrier) (power_fiber C n) (C .base) (C .base) (C .loop) x0 in
    let r0 ≔ remainder_at n (power_base_value C n x0)
        (lt_from_book (power_base_value C n x0) (suc. n) (power_base_enumeration C n .map x0 .snd)) in
    concat Nat (power_base_value C n x1) (power_base_value C n tx0) (modular_successor n r0 .fst)
      (inverse Nat (power_base_value C n tx0) (power_base_value C n x1)
        (refl ((y ↦ power_base_value C n y) : power_fiber C n (C .base) → Nat)
          (pathover_transport_equiv (C .carrier) (power_fiber C n) (C .base) (C .base) (C .loop) x0 x1 .map x2)))
      (concat Nat (power_base_value C n tx0) (modular_successor n (power_base_enumeration C n .map x0) .fst)
        (modular_successor n r0 .fst)
        (power_enumeration_monodromy C n x0 .fst)
        (refl ((r ↦ modular_successor n r .fst) : Remainder (suc. n) → Nat)
          (remainder_equal (suc. n) (power_base_enumeration C n .map x0) r0 (refl (power_base_value C n x0)))))

{` Removing the base paths from a square: the case of reflexive ones. `}
def power_square_reduction_refl (Y : Type) (g : Y → Y) (b : Y) (bt : Id Y (g b) b) (l : Id Y b b)
  (k0 k1 : Nat) (c : Id Y b b)
  (key : Id (Id Y (g b) b)
    (concat Y (g b) (g b) b (inverse Y (g b) (g b) (refl g c))
      (concat Y (g b) b b (concat Y (g b) b b bt (loop_power_nat Y b l k0)) l))
    (concat Y (g b) b b bt (loop_power_nat Y b l k1)))
  (psi : Id Y b b)
  (hc : Id (Id Y b b) c (concat Y b b b (inverse Y b b (refl b)) (concat Y b b b psi (refl b))))
  : Id (Id Y (g b) b)
      (concat Y (g b) (g b) b (inverse Y (g b) (g b) (refl g psi))
        (concat Y (g b) b b (concat Y (g b) (g b) b (refl (g b)) (concat Y (g b) b b bt (loop_power_nat Y b l k0))) l))
      (concat Y (g b) (g b) b (refl (g b)) (concat Y (g b) b b bt (loop_power_nat Y b l k1)))
  ≔ let X0 ≔ concat Y (g b) b b bt (loop_power_nat Y b l k0) in
    let X1 ≔ concat Y (g b) b b bt (loop_power_nat Y b l k1) in
    let pc : Id (Id Y b b) psi c
      ≔ calc
          psi
          = concat Y b b b psi (refl b) by concat_p1 Y b b psi
          = concat Y b b b (refl b) (concat Y b b b psi (refl b)) by concat_1p Y b b (concat Y b b b psi (refl b))
          = concat Y b b b (inverse Y b b (refl b)) (concat Y b b b psi (refl b))
            by refl ((q ↦ concat Y b b b q (concat Y b b b psi (refl b))) : Id Y b b → Id Y b b) (inverse_refl Y b)
          = c by hc ∎ in
    calc
      concat Y (g b) (g b) b (inverse Y (g b) (g b) (refl g psi))
        (concat Y (g b) b b (concat Y (g b) (g b) b (refl (g b)) X0) l)
      = concat Y (g b) (g b) b (inverse Y (g b) (g b) (refl g psi)) (concat Y (g b) b b X0 l)
        by refl ((q ↦ concat Y (g b) (g b) b (inverse Y (g b) (g b) (refl g psi)) (concat Y (g b) b b q l))
            : Id Y (g b) b → Id Y (g b) b) (concat_1p Y (g b) b X0)
      = concat Y (g b) (g b) b (inverse Y (g b) (g b) (refl g c)) (concat Y (g b) b b X0 l)
        by refl ((q ↦ concat Y (g b) (g b) b (inverse Y (g b) (g b) (refl g q)) (concat Y (g b) b b X0 l))
            : Id Y b b → Id Y (g b) b) pc
      = X1 by key
      = concat Y (g b) (g b) b (refl (g b)) X1 by concat_1p Y (g b) b X1 ∎

{` Removing the base paths e0, e1 from a square, by path induction. `}
def power_square_reduction (Y : Type) (g : Y → Y) (b : Y) (bt : Id Y (g b) b) (l : Id Y b b)
  (k0 k1 : Nat) (c : Id Y b b)
  (key : Id (Id Y (g b) b)
    (concat Y (g b) (g b) b (inverse Y (g b) (g b) (refl g c))
      (concat Y (g b) b b (concat Y (g b) b b bt (loop_power_nat Y b l k0)) l))
    (concat Y (g b) b b bt (loop_power_nat Y b l k1)))
  (P0 : Y) (e0 : Id Y P0 b) (P1 : Y) (e1 : Id Y P1 b) (psi : Id Y P0 P1)
  (hc : Id (Id Y b b) c (concat Y b P0 b (inverse Y P0 b e0) (concat Y P0 P1 b psi e1)))
  : Id (Id Y (g P1) b)
      (concat Y (g P1) (g P0) b (inverse Y (g P0) (g P1) (refl g psi))
        (concat Y (g P0) b b (concat Y (g P0) (g b) b (refl g e0) (concat Y (g b) b b bt (loop_power_nat Y b l k0))) l))
      (concat Y (g P1) (g b) b (refl g e1) (concat Y (g b) b b bt (loop_power_nat Y b l k1)))
  ≔ path_to_induction Y b
      (P0 e0 ↦ (psi : Id Y P0 P1)
        → Id (Id Y b b) c (concat Y b P0 b (inverse Y P0 b e0) (concat Y P0 P1 b psi e1))
        → Id (Id Y (g P1) b)
            (concat Y (g P1) (g P0) b (inverse Y (g P0) (g P1) (refl g psi))
              (concat Y (g P0) b b (concat Y (g P0) (g b) b (refl g e0) (concat Y (g b) b b bt (loop_power_nat Y b l k0))) l))
            (concat Y (g P1) (g b) b (refl g e1) (concat Y (g b) b b bt (loop_power_nat Y b l k1))))
      (path_to_induction Y b
        (P1 e1 ↦ (psi : Id Y b P1)
          → Id (Id Y b b) c (concat Y b b b (inverse Y b b (refl b)) (concat Y b P1 b psi e1))
          → Id (Id Y (g P1) b)
              (concat Y (g P1) (g b) b (inverse Y (g b) (g P1) (refl g psi))
                (concat Y (g b) b b (concat Y (g b) (g b) b (refl g (refl b)) (concat Y (g b) b b bt (loop_power_nat Y b l k0))) l))
              (concat Y (g P1) (g b) b (refl g e1) (concat Y (g b) b b bt (loop_power_nat Y b l k1))))
        (psi hc ↦ power_square_reduction_refl Y g b bt l k0 k1 c key psi hc)
        P1 e1)
      P0 e0 psi hc

{` alpha_m at a mark (base,x), in the orientation dg_m psi_m = p_m of the
   statement: dg_m(psi_m(base,x)) = dg_m(base) = base = base, the last step
   being loopᵏ for the mark k of x.  The book's alpha_m(base,k) = loop⁻ᵏ is
   the inverse (power_alpha_book_base below). `}
def power_alpha_base_value (C : CircleSignature) (n : Nat) (x : power_fiber C n (C .base))
  : Id (C .carrier) (circle_degree_map C (suc. n) (power_psi C n (C .base, x))) (C .base)
  ≔ concat (C .carrier) (circle_degree_map C (suc. n) (power_psi C n (C .base, x)))
      (circle_degree_map C (suc. n) (C .base)) (C .base)
      (refl (circle_degree_map C (suc. n)) (power_psi_base C n x))
      (concat (C .carrier) (circle_degree_map C (suc. n) (C .base)) (C .base) (C .base)
        (circle_degree_boundary C (suc. n) .fst)
        (loop_power_nat (C .carrier) (C .base) (C .loop) (power_base_value C n x)))

{` The squares alpha_m(loop,k): along every arc (loop, x2) of Tot(R_m). `}
def power_alpha_square (C : CircleSignature) (n : Nat) (x0 x1 : power_fiber C n (C .base))
  (x2 : Id (power_fiber C n) (C .loop) x0 x1)
  : Id ((t ↦ Id (C .carrier) (circle_degree_map C (suc. n) (power_psi C n t)) (t .fst)) : PowerBundleTotal C n → Type)
      ((C .loop, x2) : Id (PowerBundleTotal C n) (C .base, x0) (C .base, x1))
      (power_alpha_base_value C n x0) (power_alpha_base_value C n x1)
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let f ≔ circle_degree_map C (suc. n) in
    let T ≔ PowerBundleTotal C n in
    let gam : Id T (b, x0) (b, x1) ≔ (C .loop, x2) in
    let k0 ≔ power_base_value C n x0 in
    let h0 ≔ lt_from_book k0 (suc. n) (power_base_enumeration C n .map x0 .snd) in
    pathover_of_eq T (t ↦ Id S (f (power_psi C n t)) (t .fst)) (b, x0) (b, x1) gam
      (power_alpha_base_value C n x0) (power_alpha_base_value C n x1)
      (concat (Id S (f (power_psi C n (b, x1))) b)
        (transport T (t ↦ Id S (f (power_psi C n t)) (t .fst)) (b, x0) (b, x1) gam (power_alpha_base_value C n x0))
        (concat S (f (power_psi C n (b, x1))) (f (power_psi C n (b, x0))) b
          (inverse S (f (power_psi C n (b, x0))) (f (power_psi C n (b, x1))) (refl f (refl (power_psi C n) gam)))
          (concat S (f (power_psi C n (b, x0))) b b (power_alpha_base_value C n x0) (C .loop)))
        (power_alpha_base_value C n x1)
        (transport_path_family T S (t ↦ f (power_psi C n t)) (t ↦ t .fst) (b, x0) (b, x1) gam
          (power_alpha_base_value C n x0))
        (power_square_reduction S f b (circle_degree_boundary C (suc. n) .fst) (C .loop)
          k0 (power_base_value C n x1) (power_clock C n x0)
          (power_clock_key C n k0 h0 (le_split k0 n h0) (power_base_value C n x1) (power_value_successor C n x0 x1 x2))
          (power_psi C n (b, x0)) (power_psi_base C n x0) (power_psi C n (b, x1)) (power_psi_base C n x1)
          (refl (power_psi C n) gam) (power_psi_loop C n x0 x1 x2)))

def power_alpha_family (C : CircleSignature) (n : Nat) : C .carrier → Type
  ≔ z ↦ (x : power_fiber C n z) → Id (C .carrier) (circle_degree_map C (suc. n) (power_psi_curried C n z x)) z

def power_alpha_datum (C : CircleSignature) (n : Nat)
  : CircleBoundary (C .carrier) (C .base) (C .loop) (power_alpha_family C n)
  ≔ (power_alpha_base_value C n, x ⤇ power_alpha_square C n x.0 x.1 x.2)

def power_alpha_curried (C : CircleSignature) (n : Nat) : (z : C .carrier) → power_alpha_family C n z
  ≔ C .induction (power_alpha_family C n) (power_alpha_datum C n) .fst

def power_alpha_homotopy (C : CircleSignature) (n : Nat) (t : PowerBundleTotal C n)
  : Id (C .carrier) (circle_degree_map C (suc. n) (power_psi C n t)) (t .fst)
  ≔ power_alpha_curried C n (t .fst) (t .snd)

def power_alpha_base (C : CircleSignature) (n : Nat) (x : power_fiber C n (C .base))
  : Id (Id (C .carrier) (circle_degree_map C (suc. n) (power_psi C n (C .base, x))) (C .base))
      (power_alpha_homotopy C n (C .base, x)) (power_alpha_base_value C n x)
  ≔ C .induction (power_alpha_family C n) (power_alpha_datum C n) .snd .fst (refl x)

{` con:psi-alpha-m: alpha_m : dg_m ∘ psi_m = p_m. `}
def power_alpha (C : CircleSignature) (n : Nat)
  : Id (PowerBundleTotal C n → C .carrier)
      (compose (PowerBundleTotal C n) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (power_psi C n))
      (t ↦ t .fst)
  ≔ funext (PowerBundleTotal C n) (_ ↦ C .carrier)
      (compose (PowerBundleTotal C n) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (power_psi C n))
      (t ↦ t .fst) (power_alpha_homotopy C n)

{` (lᵏ)⁻¹ = (l⁻¹)ᵏ. `}
def loop_power_nat_inverse (A : Type) (a : A) (l : Id A a a) (k : Nat)
  : Id (Id A a a) (inverse A a a (loop_power_nat A a l k)) (loop_power_nat A a (inverse A a a l) k)
  ≔ match k [
  | zero. ↦ inverse_refl A a
  | suc. k ↦ concat (Id A a a) (inverse A a a (concat A a a a (loop_power_nat A a l k) l))
      (concat A a a a (inverse A a a l) (inverse A a a (loop_power_nat A a l k)))
      (loop_power_nat A a (inverse A a a l) (suc. k))
      (inverse_concat A a a a (loop_power_nat A a l k) l)
      (concat (Id A a a) (concat A a a a (inverse A a a l) (inverse A a a (loop_power_nat A a l k)))
        (concat A a a a (inverse A a a l) (loop_power_nat A a (inverse A a a l) k))
        (loop_power_nat A a (inverse A a a l) (suc. k))
        (refl (concat A a a a (inverse A a a l)) (loop_power_nat_inverse A a l k))
        (loop_power_nat_succ_left A a (inverse A a a l) k)) ]

{` con:psi-alpha-m, "alpha_m(base,k) := loop⁻ᵏ" in the book's orientation
   p_m(base,k) = dg_m(psi_m(base,k)).  The book has psi_m(base,k) ≡ base and
   dg_m(base) ≡ base; here these are the computation rules
   power_psi_base and beta, which appear as the two trailing factors. `}
def power_alpha_book_base (C : CircleSignature) (n : Nat) (x : power_fiber C n (C .base))
  : Id (Id (C .carrier) (C .base) (circle_degree_map C (suc. n) (power_psi C n (C .base, x))))
      (inverse (C .carrier) (circle_degree_map C (suc. n) (power_psi C n (C .base, x))) (C .base)
        (power_alpha_homotopy C n (C .base, x)))
      (concat (C .carrier) (C .base) (C .base) (circle_degree_map C (suc. n) (power_psi C n (C .base, x)))
        (loop_power (C .carrier) (C .base) (C .loop) (int_neg (pos. (power_base_value C n x))))
        (concat (C .carrier) (C .base) (circle_degree_map C (suc. n) (C .base))
          (circle_degree_map C (suc. n) (power_psi C n (C .base, x)))
          (inverse (C .carrier) (circle_degree_map C (suc. n) (C .base)) (C .base) (circle_degree_boundary C (suc. n) .fst))
          (inverse (C .carrier) (circle_degree_map C (suc. n) (power_psi C n (C .base, x)))
            (circle_degree_map C (suc. n) (C .base))
            (refl (circle_degree_map C (suc. n)) (power_psi_base C n x)))))
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let l ≔ C .loop in
    let f ≔ circle_degree_map C (suc. n) in
    let bt ≔ circle_degree_boundary C (suc. n) .fst in
    let k ≔ power_base_value C n x in
    let P ≔ power_psi C n (b, x) in
    let E ≔ refl f (power_psi_base C n x) in
    let lk ≔ loop_power_nat S b l k in
    calc
      inverse S (f P) b (power_alpha_homotopy C n (b, x))
      = inverse S (f P) b (concat S (f P) (f b) b E (concat S (f b) b b bt lk))
        by refl (inverse S (f P) b) (power_alpha_base C n x)
      = concat S b (f b) (f P) (inverse S (f b) b (concat S (f b) b b bt lk)) (inverse S (f P) (f b) E)
        by inverse_concat S (f P) (f b) b E (concat S (f b) b b bt lk)
      = concat S b (f b) (f P) (concat S b b (f b) (inverse S b b lk) (inverse S (f b) b bt)) (inverse S (f P) (f b) E)
        by refl ((q ↦ concat S b (f b) (f P) q (inverse S (f P) (f b) E)) : Id S b (f b) → Id S b (f P))
          (inverse_concat S (f b) b b bt lk)
      = concat S b b (f P) (inverse S b b lk) (concat S b (f b) (f P) (inverse S (f b) b bt) (inverse S (f P) (f b) E))
        by concat_assoc S b b (f b) (f P) (inverse S b b lk) (inverse S (f b) b bt) (inverse S (f P) (f b) E)
      = concat S b b (f P) (loop_power_nat S b (inverse S b b l) k)
          (concat S b (f b) (f P) (inverse S (f b) b bt) (inverse S (f P) (f b) E))
        by refl ((q ↦ concat S b b (f P) q (concat S b (f b) (f P) (inverse S (f b) b bt) (inverse S (f P) (f b) E)))
            : Id S b b → Id S b (f P)) (loop_power_nat_inverse S b l k)
      = concat S b b (f P) (loop_power S b l (int_neg (pos. k)))
          (concat S b (f b) (f P) (inverse S (f b) b bt) (inverse S (f P) (f b) E))
        by refl ((q ↦ concat S b b (f P) q (concat S b (f b) (f P) (inverse S (f b) b bt) (inverse S (f P) (f b) E)))
            : Id S b b → Id S b (f P))
          (inverse (Id S b b) (loop_power S b l (int_neg (pos. k))) (loop_power_nat S b (inverse S b b l) k)
            (loop_negative_power_nat S b l k)) ∎

{` The map of fibers over z induced by psi_m and alpha_m (xca:preim-eq
   without assuming psi_m is an equivalence):
   (t, u : z = p_m t) ↦ (psi_m t, u · alpha_m(t)⁻¹). `}
def power_psi_fiber_map (C : CircleSignature) (n : Nat) (z : C .carrier)
  (w : BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z)
  : BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) z
  ≔ (power_psi C n (w .fst),
      concat (C .carrier) z (w .fst .fst) (circle_degree_map C (suc. n) (power_psi C n (w .fst))) (w .snd)
        (inverse (C .carrier) (circle_degree_map C (suc. n) (power_psi C n (w .fst))) (w .fst .fst)
          (power_alpha_homotopy C n (w .fst))))

{` On the mark x over base it gives the book's (base, loop⁻ᵏ) (· beta⁻¹). `}
def power_psi_fiber_map_base (C : CircleSignature) (n : Nat) (x : power_fiber C n (C .base))
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (power_psi_fiber_map C n (C .base) ((C .base, x), refl (C .base)))
      (C .base, concat (C .carrier) (C .base) (C .base) (circle_degree_map C (suc. n) (C .base))
        (loop_power (C .carrier) (C .base) (C .loop) (int_neg (pos. (power_base_value C n x))))
        (inverse (C .carrier) (circle_degree_map C (suc. n) (C .base)) (C .base) (circle_degree_boundary C (suc. n) .fst)))
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let f ≔ circle_degree_map C (suc. n) in
    let e ≔ power_psi_base C n x in
    let P ≔ power_psi C n (b, x) in
    let E ≔ refl f e in
    let L ≔ loop_power S b (C .loop) (int_neg (pos. (power_base_value C n x))) in
    let ib ≔ inverse S (f b) b (circle_degree_boundary C (suc. n) .fst) in
    let a ≔ inverse S (f P) b (power_alpha_homotopy C n (b, x)) in
    (e, pathover_of_eq S (y ↦ Id S b (f y)) P b e (concat S b b (f P) (refl b) a) (concat S b b (f b) L ib)
      (calc
        concat S b (f P) (f b) (concat S b b (f P) (refl b) a) E
        = concat S b (f P) (f b) a E
          by refl ((q ↦ concat S b (f P) (f b) q E) : Id S b (f P) → Id S b (f b)) (concat_1p S b (f P) a)
        = concat S b (f P) (f b) (concat S b b (f P) L (concat S b (f b) (f P) ib (inverse S (f P) (f b) E))) E
          by refl ((q ↦ concat S b (f P) (f b) q E) : Id S b (f P) → Id S b (f b)) (power_alpha_book_base C n x)
        = concat S b b (f b) L (concat S b (f P) (f b) (concat S b (f b) (f P) ib (inverse S (f P) (f b) E)) E)
          by concat_assoc S b b (f P) (f b) L (concat S b (f b) (f P) ib (inverse S (f P) (f b) E)) E
        = concat S b b (f b) L (concat S b (f b) (f b) ib (concat S (f b) (f P) (f b) (inverse S (f P) (f b) E) E))
          by refl (concat S b b (f b) L) (concat_assoc S b (f b) (f P) (f b) ib (inverse S (f P) (f b) E) E)
        = concat S b b (f b) L (concat S b (f b) (f b) ib (refl (f b)))
          by refl ((q ↦ concat S b b (f b) L (concat S b (f b) (f b) ib q)) : Id S (f b) (f b) → Id S b (f b))
            (concat_inverse_left S (f P) (f b) E)
        = concat S b b (f b) L ib
          by refl (concat S b b (f b) L) (concat_p1 S b (f b) ib) ∎))

{` The same at the mark k : Fin m (through the trivialization). `}
def power_psi_fiber_map_explicit (C : CircleSignature) (n : Nat) (k : Fin (suc. n))
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (power_psi_fiber_map C n (C .base)
        ((C .base, equiv_inverse_map (power_fiber C n (C .base)) (Fin (suc. n)) (power_base_trivialization C n) k),
          refl (C .base)))
      (power_degree_explicit_fiber_map C n k)
  ≔ let x ≔ equiv_inverse_map (power_fiber C n (C .base)) (Fin (suc. n)) (power_base_trivialization C n) k in
    let ib ≔ inverse (C .carrier) (circle_degree_map C (suc. n) (C .base)) (C .base) (circle_degree_boundary C (suc. n) .fst) in
    concat (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (power_psi_fiber_map C n (C .base) ((C .base, x), refl (C .base)))
      (C .base, concat (C .carrier) (C .base) (C .base) (circle_degree_map C (suc. n) (C .base))
        (loop_power (C .carrier) (C .base) (C .loop) (int_neg (pos. (power_base_value C n x)))) ib)
      (power_degree_explicit_fiber_map C n k)
      (power_psi_fiber_map_base C n x)
      (refl (C .base), refl ((j ↦ concat (C .carrier) (C .base) (C .base) (circle_degree_map C (suc. n) (C .base))
            (loop_power (C .carrier) (C .base) (C .loop) (int_neg (pos. j))) ib)
          : Nat → Id (C .carrier) (C .base) (circle_degree_map C (suc. n) (C .base)))
        (refl ((j ↦ fin_book_value (suc. n) j) : Fin (suc. n) → Nat)
          (equiv_counit (power_fiber C n (C .base)) (Fin (suc. n)) (power_base_trivialization C n) k)))

{` The fiber map over base is an equivalence, by 2-out-of-3 with the
   explicit equivalence Fin m ≃ dg_m⁻¹(base) constructed above. `}
def power_psi_base_fiber_is_equiv (C : CircleSignature) (n : Nat)
  : isEquiv (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) (C .base))
      (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (power_psi_fiber_map C n (C .base))
  ≔ let R0 ≔ power_fiber C n (C .base) in
    let D ≔ BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base) in
    let FT ≔ BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) (C .base) in
    let J ≔ compose_equiv (Fin (suc. n)) R0 FT
        (canonical_inverse_equiv R0 (Fin (suc. n)) (power_base_trivialization C n))
        (native_equivalence R0 FT
          (book_projection_inclusion_equiv (C .carrier) (z ↦ power_circle_family C n z .fst) (C .base))) in
    two_out_of_three_right (Fin (suc. n)) FT D (J .map) (power_degree_explicit_fiber_map C n)
      (power_psi_fiber_map C n (C .base))
      (funext (Fin (suc. n)) (_ ↦ D) (compose (Fin (suc. n)) FT D (power_psi_fiber_map C n (C .base)) (J .map))
        (power_degree_explicit_fiber_map C n) (power_psi_fiber_map_explicit C n))
      (J .equiv) (power_degree_explicit_fiber_equiv C n .equiv)

{` Every fiber map is an equivalence: S¹ is connected. `}
def power_psi_fiber_is_equiv (C : CircleSignature) (n : Nat) (z : C .carrier)
  : isEquiv (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z)
      (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) z)
      (power_psi_fiber_map C n z)
  ≔ connected_based_elim native_truncation (C .carrier) (native_circle_connected C) (C .base)
      (z ↦ isEquiv (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z)
        (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) z)
        (power_psi_fiber_map C n z))
      (z ↦ isequiv_isprop (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z)
        (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) z)
        (power_psi_fiber_map C n z))
      (power_psi_base_fiber_is_equiv C n) z

{` con:psi-alpha-m: psi_m is an equivalence.  (The book leaves this as an
   exercise via the inverse; here: psi_m is the total map of the fiberwise
   equivalences, up to lem:sum-of-fibers on both sides.) `}
def power_psi_is_equiv (C : CircleSignature) (n : Nat) : isEquiv (PowerBundleTotal C n) (C .carrier) (power_psi C n)
  ≔ let T ≔ PowerBundleTotal C n in
    let S ≔ C .carrier in
    let f ≔ circle_degree_map C (suc. n) in
    let FT : S → Type ≔ z ↦ BookFiber T S (t ↦ t .fst) z in
    let FD : S → Type ≔ z ↦ BookFiber S S f z in
    let E1 ≔ sum_of_fibers_equiv T S (t ↦ t .fst) in
    let G ≔ compose_equiv (Σ S FT) (Σ S FD) S
        (family_equiv S FT FD (z ↦ (power_psi_fiber_map C n z, power_psi_fiber_is_equiv C n z)))
        (sum_of_fibers_equiv S S f) in
    two_out_of_three_right (Σ S FT) T S (E1 .map) (G .map) (power_psi C n)
      (refl (G .map)) (E1 .equiv) (G .equiv)

{` con:psi-alpha-m, with the book's clock psi_m and alpha_m(base,k) = loop⁻ᵏ. `}
def power_degree_explicit_comparison (C : CircleSignature) (n : Nat) : PowerDegreeComparison C n
  ≔ (book_equivalence (PowerBundleTotal C n) (C .carrier) (power_psi C n, power_psi_is_equiv C n),
      power_alpha C n)

{` ===== C. The explicit formula via xca:preim-eq ===== `}

{` The sentence after cor:dgm-conncov: the equivalence Fin m ≃ dg_m⁻¹(base)
   obtained from psi_m and alpha_m by xca:preim-eq (module 172's
   power_comparison_base_fiber_equiv, applied to the clock construction)
   sends k to (base, loop⁻ᵏ) (· beta⁻¹). `}
def power_explicit_comparison_fiber_map (C : CircleSignature) (n : Nat) (k : Fin (suc. n))
  : Id (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (power_comparison_base_fiber_equiv C n (power_degree_explicit_comparison C n) .map k)
      (power_degree_explicit_fiber_map C n k)
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let f ≔ circle_degree_map C (suc. n) in
    let T ≔ PowerBundleTotal C n in
    let x ≔ equiv_inverse_map (power_fiber C n b) (Fin (suc. n)) (power_base_trivialization C n) k in
    let P ≔ power_psi C n (b, x) in
    concat (BookFiber S S f b)
      (P, concat S b b (f P) (refl b)
        (inverse S (f P) b
          (happly T (_ ↦ S) (compose T S S f (power_psi C n)) (t ↦ t .fst) (power_alpha C n) (b, x))))
      (power_psi_fiber_map C n b ((b, x), refl b))
      (power_degree_explicit_fiber_map C n k)
      (refl P, refl ((q ↦ concat S b b (f P) (refl b) (inverse S (f P) b q)) : Id S (f P) b → Id S b (f P))
        (inverse (Id S (f P) b) (power_alpha_homotopy C n (b, x))
          (happly T (_ ↦ S) (compose T S S f (power_psi C n)) (t ↦ t .fst) (power_alpha C n) (b, x))
          (funext_beta T (_ ↦ S) (compose T S S f (power_psi C n)) (t ↦ t .fst) (power_alpha_homotopy C n) (b, x))))
      (power_psi_fiber_map_explicit C n k)

{` ===== D. The inverse of psi_m: base ↦ (base,0), loop ↦ a_{m-1}⋯a_0 ===== `}

{` The marks x_k = s^k(0) of R_m(base), s = transport along loop. `}
def power_mark (C : CircleSignature) (n k : Nat) : power_fiber C n (C .base)
  ≔ iterate (power_fiber C n (C .base))
      (transport (C .carrier) (power_fiber C n) (C .base) (C .base) (C .loop)) k (power_bundle_zero C n)

def power_mark_enumeration (C : CircleSignature) (n k : Nat)
  : Id (Remainder (suc. n)) (power_base_enumeration C n .map (power_mark C n k))
      (iterate (Remainder (suc. n)) (modular_successor n) k (remainder_at n zero. star.))
  ≔ match k [
  | zero. ↦ concat (Remainder (suc. n)) (power_base_enumeration C n .map (power_bundle_zero C n))
      (fin_book_below_equiv (suc. n) .map (inr. star.)) (remainder_at n zero. star.)
      (refl (fin_book_below_equiv (suc. n) .map)
        (equiv_counit (power_fiber C n (C .base)) (Fin (suc. n)) (power_base_trivialization C n) (inr. star.)))
      (remainder_equal (suc. n) (fin_book_below_equiv (suc. n) .map (inr. star.)) (remainder_at n zero. star.)
        (refl zero.))
  | suc. k ↦ concat (Remainder (suc. n))
      (power_base_enumeration C n .map
        (transport (C .carrier) (power_fiber C n) (C .base) (C .base) (C .loop) (power_mark C n k)))
      (modular_successor n (power_base_enumeration C n .map (power_mark C n k)))
      (modular_successor n (iterate (Remainder (suc. n)) (modular_successor n) k (remainder_at n zero. star.)))
      (power_enumeration_monodromy C n (power_mark C n k))
      (refl (modular_successor n) (power_mark_enumeration C n k)) ]

def power_mark_remainder (C : CircleSignature) (n k : Nat) (h : Le k n)
  : Id (Remainder (suc. n)) (power_base_enumeration C n .map (power_mark C n k)) (remainder_at n k h)
  ≔ concat (Remainder (suc. n)) (power_base_enumeration C n .map (power_mark C n k))
      (iterate (Remainder (suc. n)) (modular_successor n) k (remainder_at n zero. star.)) (remainder_at n k h)
      (power_mark_enumeration C n k) (modular_successor_iterate n k h)

{` Going once around the clock returns to the mark 0: x_m = x_0. `}
def power_mark_closing (C : CircleSignature) (n : Nat)
  : Id (power_fiber C n (C .base)) (power_mark C n (suc. n)) (power_mark C n zero.)
  ≔ let nu ≔ power_base_enumeration C n .map in
    equivalence_injective (power_fiber C n (C .base)) (Remainder (suc. n)) (power_base_enumeration C n)
      (power_mark C n (suc. n)) (power_mark C n zero.)
      (concat (Remainder (suc. n)) (nu (power_mark C n (suc. n))) (remainder_at n zero. star.) (nu (power_mark C n zero.))
        (concat (Remainder (suc. n)) (nu (power_mark C n (suc. n)))
          (modular_successor n (remainder_at n n (le_refl n))) (remainder_at n zero. star.)
          (concat (Remainder (suc. n)) (nu (power_mark C n (suc. n)))
            (modular_successor n (nu (power_mark C n n))) (modular_successor n (remainder_at n n (le_refl n)))
            (power_enumeration_monodromy C n (power_mark C n n))
            (refl (modular_successor n) (power_mark_remainder C n n (le_refl n))))
          (modular_successor_last n))
        (inverse (Remainder (suc. n)) (nu (power_mark C n zero.)) (remainder_at n zero. star.)
          (power_mark_enumeration C n zero.)))

{` The arc a_k = (loop, refl) : (base,k) = (base,k+1) of Tot(R_m). `}
def power_arc (C : CircleSignature) (n k : Nat)
  : Id (PowerBundleTotal C n) (C .base, power_mark C n k) (C .base, power_mark C n (suc. k))
  ≔ (C .loop, refl (power_fiber C n) (C .loop) .liftr (power_mark C n k))

{` a_{k-1}⋯a_0 : (base,0) = (base,k). `}
def power_arcs (C : CircleSignature) (n k : Nat)
  : Id (PowerBundleTotal C n) (C .base, power_mark C n zero.) (C .base, power_mark C n k)
  ≔ match k [
  | zero. ↦ refl ((C .base, power_mark C n zero.) : PowerBundleTotal C n)
  | suc. k ↦ concat (PowerBundleTotal C n) (C .base, power_mark C n zero.) (C .base, power_mark C n k)
      (C .base, power_mark C n (suc. k)) (power_arcs C n k) (power_arc C n k) ]

{` The product of all arcs around the clock, a_{m-1}⋯a_0, closed up by
   x_m = x_0 (judgmental in the book, where s(m-1) = 0). `}
def power_arc_loop (C : CircleSignature) (n : Nat)
  : Id (PowerBundleTotal C n) (C .base, power_mark C n zero.) (C .base, power_mark C n zero.)
  ≔ concat (PowerBundleTotal C n) (C .base, power_mark C n zero.) (C .base, power_mark C n (suc. n))
      (C .base, power_mark C n zero.) (power_arcs C n (suc. n))
      ((refl (C .base), power_mark_closing C n)
        : Id (PowerBundleTotal C n) (C .base, power_mark C n (suc. n)) (C .base, power_mark C n zero.))

{` con:psi-alpha-m, "the inverse of psi_m maps base to (base,0) and loop
   to a_{m-1}⋯a_0". `}
def power_psi_inverse_map (C : CircleSignature) (n : Nat) : C .carrier → PowerBundleTotal C n
  ≔ circle_rec C (PowerBundleTotal C n) ((C .base, power_mark C n zero.), power_arc_loop C n)

def power_psi_inverse_base (C : CircleSignature) (n : Nat)
  : Id (PowerBundleTotal C n) (power_psi_inverse_map C n (C .base)) (C .base, power_mark C n zero.)
  ≔ circle_rec_beta C (PowerBundleTotal C n) ((C .base, power_mark C n zero.), power_arc_loop C n) .fst

{` clock(x_0) ⋯ clock(x_{k-1}). `}
def power_clock_product (C : CircleSignature) (n k : Nat) : Id (C .carrier) (C .base) (C .base)
  ≔ match k [
  | zero. ↦ refl (C .base)
  | suc. k ↦ concat (C .carrier) (C .base) (C .base) (C .base) (power_clock_product C n k)
      (power_clock C n (power_mark C n k)) ]

{` psi_m(a_{k-1}⋯a_0) is the product of the clock values (telescoping). `}
def power_psi_arcs (C : CircleSignature) (n k : Nat)
  : Id (Id (C .carrier) (C .base) (C .base))
      (concat (C .carrier) (C .base) (power_psi C n (C .base, power_mark C n zero.)) (C .base)
        (inverse (C .carrier) (power_psi C n (C .base, power_mark C n zero.)) (C .base)
          (power_psi_base C n (power_mark C n zero.)))
        (concat (C .carrier) (power_psi C n (C .base, power_mark C n zero.)) (power_psi C n (C .base, power_mark C n k))
          (C .base) (refl (power_psi C n) (power_arcs C n k)) (power_psi_base C n (power_mark C n k))))
      (power_clock_product C n k)
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let T ≔ PowerBundleTotal C n in
    let ps ≔ power_psi C n in
    let P0 ≔ ps (b, power_mark C n zero.) in
    let e0 ≔ power_psi_base C n (power_mark C n zero.) in
    match k [
    | zero. ↦ concat (Id S b b)
        (concat S b P0 b (inverse S P0 b e0) (concat S P0 P0 b (refl P0) e0))
        (concat S b P0 b (inverse S P0 b e0) e0) (refl b)
        (refl (concat S b P0 b (inverse S P0 b e0)) (concat_1p S P0 b e0))
        (concat_inverse_left S P0 b e0)
    | suc. k ↦
      let Pk ≔ ps (b, power_mark C n k) in
      let Pk1 ≔ ps (b, power_mark C n (suc. k)) in
      let ek ≔ power_psi_base C n (power_mark C n k) in
      let ek1 ≔ power_psi_base C n (power_mark C n (suc. k)) in
      let Ak ≔ refl ps (power_arcs C n k) in
      let ak ≔ refl ps (power_arc C n k) in
      let ck ≔ power_clock C n (power_mark C n k) in
      calc
        concat S b P0 b (inverse S P0 b e0)
          (concat S P0 Pk1 b (refl ps (concat T (b, power_mark C n zero.) (b, power_mark C n k) (b, power_mark C n (suc. k))
            (power_arcs C n k) (power_arc C n k))) ek1)
        = concat S b P0 b (inverse S P0 b e0) (concat S P0 Pk1 b (concat S P0 Pk Pk1 Ak ak) ek1)
          by refl ((q ↦ concat S b P0 b (inverse S P0 b e0) (concat S P0 Pk1 b q ek1)) : Id S P0 Pk1 → Id S b b)
            (map_path_concat T S ps (b, power_mark C n zero.) (b, power_mark C n k) (b, power_mark C n (suc. k))
              (power_arcs C n k) (power_arc C n k))
        = concat S b P0 b (inverse S P0 b e0) (concat S P0 Pk b Ak (concat S Pk Pk1 b ak ek1))
          by refl (concat S b P0 b (inverse S P0 b e0)) (concat_assoc S P0 Pk Pk1 b Ak ak ek1)
        = concat S b P0 b (inverse S P0 b e0)
            (concat S P0 Pk b Ak (concat S Pk b b ek (concat S b Pk b (inverse S Pk b ek) (concat S Pk Pk1 b ak ek1))))
          by refl ((q ↦ concat S b P0 b (inverse S P0 b e0) (concat S P0 Pk b Ak q)) : Id S Pk b → Id S b b)
            (inverse (Id S Pk b)
              (concat S Pk b b ek (concat S b Pk b (inverse S Pk b ek) (concat S Pk Pk1 b ak ek1)))
              (concat S Pk Pk1 b ak ek1)
              (concat_right_inverse_cancel S Pk b b ek (concat S Pk Pk1 b ak ek1)))
        = concat S b P0 b (inverse S P0 b e0) (concat S P0 Pk b Ak (concat S Pk b b ek ck))
          by refl ((q ↦ concat S b P0 b (inverse S P0 b e0) (concat S P0 Pk b Ak (concat S Pk b b ek q)))
              : Id S b b → Id S b b)
            (inverse (Id S b b) ck (concat S b Pk b (inverse S Pk b ek) (concat S Pk Pk1 b ak ek1))
              (power_psi_loop C n (power_mark C n k) (power_mark C n (suc. k))
                (refl (power_fiber C n) (C .loop) .liftr (power_mark C n k))))
        = concat S b P0 b (inverse S P0 b e0) (concat S P0 b b (concat S P0 Pk b Ak ek) ck)
          by refl (concat S b P0 b (inverse S P0 b e0))
            (inverse (Id S P0 b) (concat S P0 b b (concat S P0 Pk b Ak ek) ck) (concat S P0 Pk b Ak (concat S Pk b b ek ck))
              (concat_assoc S P0 Pk b b Ak ek ck))
        = concat S b b b (concat S b P0 b (inverse S P0 b e0) (concat S P0 Pk b Ak ek)) ck
          by inverse (Id S b b) (concat S b b b (concat S b P0 b (inverse S P0 b e0) (concat S P0 Pk b Ak ek)) ck)
            (concat S b P0 b (inverse S P0 b e0) (concat S P0 b b (concat S P0 Pk b Ak ek) ck))
            (concat_assoc S b P0 b b (inverse S P0 b e0) (concat S P0 Pk b Ak ek) ck)
        = concat S b b b (power_clock_product C n k) ck
          by refl ((q ↦ concat S b b b q ck) : Id S b b → Id S b b) (power_psi_arcs C n k) ∎ ]

{` The base path of psi_m is natural in the fiber direction. `}
def power_psi_base_natural (C : CircleSignature) (n : Nat) (x y : power_fiber C n (C .base))
  (c : Id (power_fiber C n (C .base)) x y)
  : Id (Id (C .carrier) (power_psi C n (C .base, x)) (C .base))
      (concat (C .carrier) (power_psi C n (C .base, x)) (power_psi C n (C .base, y)) (C .base)
        (refl (power_psi C n) ((refl (C .base), c) : Id (PowerBundleTotal C n) (C .base, x) (C .base, y)))
        (power_psi_base C n y))
      (power_psi_base C n x)
  ≔ J (power_fiber C n (C .base)) x
      (y c ↦ Id (Id (C .carrier) (power_psi C n (C .base, x)) (C .base))
        (concat (C .carrier) (power_psi C n (C .base, x)) (power_psi C n (C .base, y)) (C .base)
          (refl (power_psi C n) ((refl (C .base), c) : Id (PowerBundleTotal C n) (C .base, x) (C .base, y)))
          (power_psi_base C n y))
        (power_psi_base C n x))
      (concat_1p (C .carrier) (power_psi C n (C .base, x)) (C .base) (power_psi_base C n x)) y c

def power_clock_split_small (C : CircleSignature) (n v : Nat) (s : Sum (Lt v n) (Id Nat v n)) (h : Lt v n)
  : Id (Id (C .carrier) (C .base) (C .base)) (power_clock_split C n v s) (refl (C .base))
  ≔ match s [ inl. _ ↦ refl (refl (C .base)) | inr. p ↦ match lt_not_equal v n h p [] ]

def power_clock_split_last (C : CircleSignature) (n v : Nat) (s : Sum (Lt v n) (Id Nat v n)) (p : Id Nat v n)
  : Id (Id (C .carrier) (C .base) (C .base)) (power_clock_split C n v s) (C .loop)
  ≔ match s [ inl. h ↦ match lt_not_equal v n h p [] | inr. _ ↦ refl (C .loop) ]

def power_mark_value (C : CircleSignature) (n k : Nat) (h : Le k n)
  : Id Nat (power_base_value C n (power_mark C n k)) k
  ≔ power_mark_remainder C n k h .fst

{` The clock is refl at the marks k < m-1 and loop at the mark m-1. `}
def power_clock_mark_small (C : CircleSignature) (n k : Nat) (h : Lt k n)
  : Id (Id (C .carrier) (C .base) (C .base)) (power_clock C n (power_mark C n k)) (refl (C .base))
  ≔ let v ≔ power_base_value C n (power_mark C n k) in
    power_clock_split_small C n v
      (le_split v n (lt_from_book v (suc. n) (power_base_enumeration C n .map (power_mark C n k) .snd)))
      (transport Nat (j ↦ Lt j n) k v (inverse Nat v k (power_mark_value C n k (lt_le k n h))) h)

def power_clock_mark_last (C : CircleSignature) (n : Nat)
  : Id (Id (C .carrier) (C .base) (C .base)) (power_clock C n (power_mark C n n)) (C .loop)
  ≔ let v ≔ power_base_value C n (power_mark C n n) in
    power_clock_split_last C n v
      (le_split v n (lt_from_book v (suc. n) (power_base_enumeration C n .map (power_mark C n n) .snd)))
      (power_mark_value C n n (le_refl n))

def power_clock_product_prefix (C : CircleSignature) (n k : Nat) (h : Le k n)
  : Id (Id (C .carrier) (C .base) (C .base)) (power_clock_product C n k) (refl (C .base))
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    match k [
    | zero. ↦ refl (refl b)
    | suc. k ↦ concat (Id S b b)
        (concat S b b b (power_clock_product C n k) (power_clock C n (power_mark C n k)))
        (concat S b b b (refl b) (power_clock C n (power_mark C n k))) (refl b)
        (refl ((q ↦ concat S b b b q (power_clock C n (power_mark C n k))) : Id S b b → Id S b b)
          (power_clock_product_prefix C n k (lt_le k n h)))
        (concat (Id S b b) (concat S b b b (refl b) (power_clock C n (power_mark C n k)))
          (concat S b b b (refl b) (refl b)) (refl b)
          (refl (concat S b b b (refl b)) (power_clock_mark_small C n k h))
          (concat_p1 S b b (refl b))) ]

{` psi_m sends the loop a_{m-1}⋯a_0 to loop (conjugated by the base path). `}
def power_psi_arc_loop (C : CircleSignature) (n : Nat)
  : Id (Id (C .carrier) (C .base) (C .base))
      (concat (C .carrier) (C .base) (power_psi C n (C .base, power_mark C n zero.)) (C .base)
        (inverse (C .carrier) (power_psi C n (C .base, power_mark C n zero.)) (C .base)
          (power_psi_base C n (power_mark C n zero.)))
        (concat (C .carrier) (power_psi C n (C .base, power_mark C n zero.))
          (power_psi C n (C .base, power_mark C n zero.)) (C .base)
          (refl (power_psi C n) (power_arc_loop C n)) (power_psi_base C n (power_mark C n zero.))))
      (C .loop)
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let T ≔ PowerBundleTotal C n in
    let ps ≔ power_psi C n in
    let x0 ≔ power_mark C n zero. in
    let xm ≔ power_mark C n (suc. n) in
    let P0 ≔ ps (b, x0) in
    let Pm ≔ ps (b, xm) in
    let e0 ≔ power_psi_base C n x0 in
    let em ≔ power_psi_base C n xm in
    let V : Id T (b, xm) (b, x0) ≔ (refl b, power_mark_closing C n) in
    let Am ≔ refl ps (power_arcs C n (suc. n)) in
    calc
      concat S b P0 b (inverse S P0 b e0) (concat S P0 P0 b (refl ps (power_arc_loop C n)) e0)
      = concat S b P0 b (inverse S P0 b e0) (concat S P0 P0 b (concat S P0 Pm P0 Am (refl ps V)) e0)
        by refl ((q ↦ concat S b P0 b (inverse S P0 b e0) (concat S P0 P0 b q e0)) : Id S P0 P0 → Id S b b)
          (map_path_concat T S ps (b, x0) (b, xm) (b, x0) (power_arcs C n (suc. n)) V)
      = concat S b P0 b (inverse S P0 b e0) (concat S P0 Pm b Am (concat S Pm P0 b (refl ps V) e0))
        by refl (concat S b P0 b (inverse S P0 b e0)) (concat_assoc S P0 Pm P0 b Am (refl ps V) e0)
      = concat S b P0 b (inverse S P0 b e0) (concat S P0 Pm b Am em)
        by refl ((q ↦ concat S b P0 b (inverse S P0 b e0) (concat S P0 Pm b Am q)) : Id S Pm b → Id S b b)
          (power_psi_base_natural C n xm x0 (power_mark_closing C n))
      = power_clock_product C n (suc. n) by power_psi_arcs C n (suc. n)
      = concat S b b b (refl b) (power_clock C n (power_mark C n n))
        by refl ((q ↦ concat S b b b q (power_clock C n (power_mark C n n))) : Id S b b → Id S b b)
          (power_clock_product_prefix C n n (le_refl n))
      = concat S b b b (refl b) (C .loop)
        by refl (concat S b b b (refl b)) (power_clock_mark_last C n)
      = C .loop by concat_1p S b b (C .loop) ∎

{` psi_m ∘ (its book inverse) agrees with the identity on the boundary data. `}
def power_psi_inverse_boundary (C : CircleSignature) (n : Nat)
  : Id (FreeLoop (C .carrier))
      (circle_eval C (C .carrier)
        (compose (C .carrier) (PowerBundleTotal C n) (C .carrier) (power_psi C n) (power_psi_inverse_map C n)))
      (circle_eval C (C .carrier) (identity (C .carrier)))
  ≔ let S ≔ C .carrier in
    let b ≔ C .base in
    let T ≔ PowerBundleTotal C n in
    let ps ≔ power_psi C n in
    let phi ≔ power_psi_inverse_map C n in
    let x0 ≔ power_mark C n zero. in
    let P0 ≔ ps (b, x0) in
    let e0 ≔ power_psi_base C n x0 in
    let lam ≔ power_arc_loop C n in
    concat (FreeLoop S) (ps (phi b), refl ps (refl phi (C .loop))) (P0, refl ps lam) (b, C .loop)
      (refl ((u ↦ (ps (u .fst), refl ps (u .snd))) : FreeLoop T → FreeLoop S)
        (circle_rec_beta C T ((b, x0), lam)))
      (e0, pathover_of_eq S (a ↦ Id S a a) P0 b e0 (refl ps lam) (C .loop)
        (concat (Id S b b) (transport S (a ↦ Id S a a) P0 b e0 (refl ps lam))
          (concat S b P0 b (inverse S P0 b e0) (concat S P0 P0 b (refl ps lam) e0)) (C .loop)
          (transport_conjugation S P0 b e0 (refl ps lam)) (power_psi_arc_loop C n)))

{` psi_m ∘ inverse = id ... `}
def power_psi_section (C : CircleSignature) (n : Nat)
  : Id (C .carrier → C .carrier)
      (compose (C .carrier) (PowerBundleTotal C n) (C .carrier) (power_psi C n) (power_psi_inverse_map C n))
      (identity (C .carrier))
  ≔ circle_maps_equal C (C .carrier)
      (compose (C .carrier) (PowerBundleTotal C n) (C .carrier) (power_psi C n) (power_psi_inverse_map C n))
      (identity (C .carrier)) (power_psi_inverse_boundary C n)

{` ... hence, psi_m being an equivalence, the book's map is its inverse. `}
def power_psi_inverse_agrees (C : CircleSignature) (n : Nat) (z : C .carrier)
  : Id (PowerBundleTotal C n) (power_psi_inverse_map C n z)
      (equiv_inverse_map (PowerBundleTotal C n) (C .carrier) (power_psi C n, power_psi_is_equiv C n) z)
  ≔ let T ≔ PowerBundleTotal C n in
    let S ≔ C .carrier in
    let pe : Equiv T S ≔ (power_psi C n, power_psi_is_equiv C n) in
    concat T (power_psi_inverse_map C n z)
      (equiv_inverse_map T S pe (power_psi C n (power_psi_inverse_map C n z))) (equiv_inverse_map T S pe z)
      (equiv_unit T S pe (power_psi_inverse_map C n z))
      (refl (equiv_inverse_map T S pe)
        (happly S (_ ↦ S) (compose S T S (power_psi C n) (power_psi_inverse_map C n)) (identity S)
          (power_psi_section C n) z))

{` ... and inverse ∘ psi_m = id. `}
def power_psi_inverse_retraction (C : CircleSignature) (n : Nat) (t : PowerBundleTotal C n)
  : Id (PowerBundleTotal C n) (power_psi_inverse_map C n (power_psi C n t)) t
  ≔ let T ≔ PowerBundleTotal C n in
    let S ≔ C .carrier in
    let pe : Equiv T S ≔ (power_psi C n, power_psi_is_equiv C n) in
    concat T (power_psi_inverse_map C n (power_psi C n t)) (equiv_inverse_map T S pe (power_psi C n t)) t
      (power_psi_inverse_agrees C n (power_psi C n t)) (equiv_retraction T S pe t)

{` The book's inverse, as an equivalence S¹ ≃ Tot(R_m) with that map. `}
def power_psi_inverse_equiv (C : CircleSignature) (n : Nat) : Equiv (C .carrier) (PowerBundleTotal C n)
  ≔ let T ≔ PowerBundleTotal C n in
    let S ≔ C .carrier in
    equiv_change_map S T (canonical_inverse_equiv T S (power_psi C n, power_psi_is_equiv C n))
      (power_psi_inverse_map C n)
      (z ↦ inverse T (power_psi_inverse_map C n z)
        (equiv_inverse_map T S (power_psi C n, power_psi_is_equiv C n) z) (power_psi_inverse_agrees C n z))

{` ===== Instantiations at the constructed circle (modules 220-223) ===== `}

def S1_power_degree_explicit_fiber_equiv (n : Nat)
  : Equiv (Fin (suc. n))
      (BookFiber (constructed_circle .carrier) (constructed_circle .carrier)
        (circle_degree_map constructed_circle (suc. n)) (constructed_circle .base))
  ≔ power_degree_explicit_fiber_equiv constructed_circle n

def S1_power_degree_explicit_comparison (n : Nat) : PowerDegreeComparison constructed_circle n
  ≔ power_degree_explicit_comparison constructed_circle n
