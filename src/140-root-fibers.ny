export "139-cycle-residues"

def int_mul_zero_left_pos (m : Nat) : Id Int (int_mul int_zero (pos. m)) int_zero
  ≔ match m [
  | zero. ↦ refl int_zero
  | suc. m ↦ concat Int (int_add int_zero (int_mul int_zero (pos. m))) (int_mul int_zero (pos. m)) int_zero
      (int_add_zero_left (int_mul int_zero (pos. m))) (int_mul_zero_left_pos m) ]

def int_add_interchange (a b c d : Int)
  : Id Int (int_add (int_add a b) (int_add c d)) (int_add (int_add a c) (int_add b d))
  ≔ calc
      int_add (int_add a b) (int_add c d) = int_add a (int_add b (int_add c d)) by int_add_assoc a b (int_add c d)
      = int_add a (int_add (int_add b c) d)
        by refl (int_add a) (inverse Int (int_add (int_add b c) d) (int_add b (int_add c d)) (int_add_assoc b c d))
      = int_add a (int_add (int_add c b) d) by refl ((v ↦ int_add a (int_add v d)) : Int → Int) (int_add_comm b c)
      = int_add a (int_add c (int_add b d)) by refl (int_add a) (int_add_assoc c b d)
      = int_add (int_add a c) (int_add b d)
        by inverse Int (int_add (int_add a c) (int_add b d)) (int_add a (int_add c (int_add b d)))
          (int_add_assoc a c (int_add b d)) ∎

def int_mul_add_left_pos (x y : Int) (m : Nat)
  : Id Int (int_mul (int_add x y) (pos. m)) (int_add (int_mul x (pos. m)) (int_mul y (pos. m)))
  ≔ match m [
  | zero. ↦ refl int_zero
  | suc. m ↦ calc
      int_add (int_add x y) (int_mul (int_add x y) (pos. m))
      = int_add (int_add x y) (int_add (int_mul x (pos. m)) (int_mul y (pos. m)))
        by refl (int_add (int_add x y)) (int_mul_add_left_pos x y m)
      = int_add (int_add x (int_mul x (pos. m))) (int_add y (int_mul y (pos. m)))
        by int_add_interchange x y (int_mul x (pos. m)) (int_mul y (pos. m)) ∎ ]

def int_mul_neg_left_pos (x : Int) (m : Nat)
  : Id Int (int_mul (int_neg x) (pos. m)) (int_neg (int_mul x (pos. m)))
  ≔ match m [
  | zero. ↦ refl int_zero
  | suc. m ↦ calc
      int_add (int_neg x) (int_mul (int_neg x) (pos. m)) = int_add (int_neg x) (int_neg (int_mul x (pos. m)))
        by refl (int_add (int_neg x)) (int_mul_neg_left_pos x m)
      = int_neg (int_add x (int_mul x (pos. m)))
        by inverse Int (int_neg (int_add x (int_mul x (pos. m)))) (int_add (int_neg x) (int_neg (int_mul x (pos. m))))
          (int_neg_additive x (int_mul x (pos. m))) ∎ ]

{` The condition P of thm:fiber-cdg: H_t ⊆ mZ, with m = suc n. `}
def RootFiberCondition (n : Nat) (c : Cycles) : Type ≔ Inclusion Int (CyclePeriods c) (Multiples (suc. n))
def root_fiber_condition_prop (n : Nat) (c : Cycles) : isProp (RootFiberCondition n c)
  ≔ inclusion_prop Int (CyclePeriods c) (Multiples (suc. n))

{` P is the divisibility of orders from def:Order. `}
def root_fiber_condition_divides (n : Nat) (c : Cycles)
  : Equiv (RootFiberCondition n c) (OrderDivides (principal_order (suc. n)) (cycle_order c))
  ≔ iff_equiv (RootFiberCondition n c) (OrderDivides (principal_order (suc. n)) (cycle_order c))
      (root_fiber_condition_prop n c) (order_divides_prop (principal_order (suc. n)) (cycle_order c))
      (h z p ↦ transport (Subtypes Int) (H ↦ H z .fst) (Multiples (suc. n)) (CyclePeriods (finite_standard_cycle n))
        (inverse (Subtypes Int) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n)) (finite_standard_periods n))
        (h z p))
      (h z p ↦ standard_period_multiple n z (h z p))

{` The subgroup {q | q·m ∈ H_t}; under P its m-multiples are exactly H_t. `}
def QuotientPeriods (n : Nat) (c : Cycles) : Subtypes Int ≔ q ↦ CyclePeriods c (int_mul q (pos. (suc. n)))

def quotient_periods_laws (n : Nat) (c : Cycles) : IntegerSubgroupLaws (QuotientPeriods n c)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let m : Int ≔ pos. (suc. n) in
    (zero_is_period c (int_mul int_zero m) (int_mul_zero_left_pos (suc. n)),
     ((q r hq hr ↦ transport Int (PowerPeriod X t) (int_add (int_mul q m) (int_mul r m)) (int_mul (int_add q r) m)
         (inverse Int (int_mul (int_add q r) m) (int_add (int_mul q m) (int_mul r m)) (int_mul_add_left_pos q r (suc. n)))
         (power_period_add X t (int_mul q m) (int_mul r m) hq hr)),
      (q hq ↦ transport Int (PowerPeriod X t) (int_neg (int_mul q m)) (int_mul (int_neg q) m)
         (inverse Int (int_mul (int_neg q) m) (int_neg (int_mul q m)) (int_mul_neg_left_pos q (suc. n)))
         (power_period_neg X t (int_mul q m) hq))))

def quotient_order (n : Nat) (c : Cycles) : Order
  ≔ subgroup_to_order (QuotientPeriods n c, quotient_periods_laws n c)

def quotient_order_periods (n : Nat) (c : Cycles)
  : Id (Subtypes Int) (order_periods (quotient_order n c)) (QuotientPeriods n c)
  ≔ subgroup_cycle_periods (QuotientPeriods n c) (quotient_periods_laws n c)

def quotient_periods_scaled (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  : Id (Subtypes Int) (CyclePeriods c) (ScaledSubtype (suc. n) (QuotientPeriods n c))
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let m : Int ≔ pos. (suc. n) in
    let S ≔ ScaledSubtype (suc. n) (QuotientPeriods n c) in
    inclusion_antisym Int (CyclePeriods c) S
      (z h ↦ mere_rec (MultipleWitness (suc. n) z) (S z .fst) (S z .snd)
        (w ↦ mere (ScaledWitness (suc. n) (QuotientPeriods n c) z)
          (w, transport Int (PowerPeriod X t) z (int_mul (w .fst) m) (w .snd) h))
        (pr z h))
      (z s ↦ mere_rec (ScaledWitness (suc. n) (QuotientPeriods n c) z) (CyclePeriods c z .fst) (CyclePeriods c z .snd)
        (v ↦ transport Int (PowerPeriod X t) (int_mul (v .fst .fst) m) z
          (inverse Int z (int_mul (v .fst .fst) m) (v .fst .snd)) (v .snd)) s)

{` The fiber of cdg_m at (X,t), with the book's orientation (X,t) = cdg_m(Y,u). `}
def RootFiber (n : Nat) (c : Cycles) : Type ≔ BookFiber Cycles Cycles (cycle_root n) c

{` The first coordinate fst(e(x)) of an identification e : (X,t) = cdg_m(Y,u),
   as a map of cycles into the standard m-cycle. `}
def root_path_residue (n : Nat) (c d : Cycles) (p : Id Cycles c (cycle_root n d)) : CycleResidues n c
  ≔ let Y ≔ d .fst .fst .fst in let F ≔ Product (Fin (suc. n)) Y in
    let i ≔ cycle_paths_equiv c (cycle_root n d) .map p in
    let first ≔ ((u ↦ fin_book_below_equiv (suc. n) .map (u .fst)) : F → Remainder (suc. n)) in
    ((x ↦ first (i .fst .map x)),
     x ↦ concat (Remainder (suc. n)) (first (i .fst .map (c .fst .snd .map x)))
       (first (root_finite n Y (d .fst .snd .map) (i .fst .map x)))
       (modular_successor n (first (i .fst .map x)))
       (refl first (i .snd x)) (root_finite_remainder_first n Y (d .fst .snd) (i .fst .map x)))

{` The proof of P from lem:m-root-id. `}
def root_path_condition (n : Nat) (c d : Cycles) (p : Id Cycles c (cycle_root n d)) : RootFiberCondition n c
  ≔ z h ↦ root_period_multiple n d z (transport Cycles (e ↦ CyclePeriods e z .fst) c (cycle_root n d) p h)

def root_path_quotient_equiv (n : Nat) (c d : Cycles) (p : Id Cycles c (cycle_root n d))
  : Equiv (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (Remainder (suc. n))
  ≔ residue_quotient_equiv n c (root_path_residue n c d p)

{` The class V_e: the unique class on which fst ∘ e vanishes. `}
def root_fiber_class (n : Nat) (c : Cycles) (w : RootFiber n c) : ModQuotient n (c .fst .fst .fst) (c .fst .snd)
  ≔ equiv_inverse_map (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (Remainder (suc. n))
      (root_path_quotient_equiv n c (w .fst) (w .snd)) (remainder_at n zero. star.)

{` The map g of thm:fiber-cdg. `}
def root_fiber_map (n : Nat) (c : Cycles) (w : RootFiber n c)
  : Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  ≔ (root_path_condition n c (w .fst) (w .snd), root_fiber_class n c w)

def equiv_inverse_characterization (A B : Type) (ha : isSet A) (hb : isSet B) (e : Equiv A B) (a : A) (b : B)
  : Equiv (Id A a (equiv_inverse_map A B e b)) (Id B (e .map a) b)
  ≔ iff_equiv (Id A a (equiv_inverse_map A B e b)) (Id B (e .map a) b) (ha a (equiv_inverse_map A B e b)) (hb (e .map a) b)
      (q ↦ concat B (e .map a) (e .map (equiv_inverse_map A B e b)) b (refl (e .map) q) (equiv_counit A B e b))
      (q ↦ inverse A (equiv_inverse_map A B e b) a (inverse_at_known_point A B e a b q))

{` As a subset of X, V_e = {x : X | fst(e(x)) = 0}. `}
def root_fiber_class_members (n : Nat) (c : Cycles) (w : RootFiber n c) (x : c .fst .fst .fst)
  : Equiv (root_fiber_class n c w .fst x .fst)
      (Id (Fin (suc. n)) (cycle_path_evaluate c (cycle_root n (w .fst)) (w .snd) x .fst) (inr. star.))
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let Q ≔ ModQuotient n X (c .fst .snd) in let E ≔ root_path_quotient_equiv n c (w .fst) (w .snd) in
    let V ≔ root_fiber_class n c w in
    let k ≔ cycle_path_evaluate c (cycle_root n (w .fst)) (w .snd) x .fst in
    let fbb ≔ fin_book_below_equiv (suc. n) in
    iff_equiv (V .fst x .fst) (Id (Fin (suc. n)) k (inr. star.)) (V .fst x .snd) (fin_set (suc. n) k (inr. star.))
      (h ↦ let cls ≔ equiv_inverse_map (Id Q V (quotient_class X R x)) (V .fst x .fst) (quotient_class_property X R V x) h in
        equivalence_injective (Fin (suc. n)) (Remainder (suc. n)) fbb k (inr. star.)
          (concat (Remainder (suc. n)) (fbb .map k) (remainder_at n zero. star.) (fbb .map (inr. star.))
            (equiv_inverse_characterization Q (Remainder (suc. n)) (quotient_set X R) (remainder_set (suc. n)) E
              (quotient_class X R x) (remainder_at n zero. star.) .map (inverse Q V (quotient_class X R x) cls))
            (remainder_equal (suc. n) (remainder_at n zero. star.) (fbb .map (inr. star.)) (refl zero.))))
      (h ↦ quotient_class_property X R V x .map (inverse Q (quotient_class X R x) V
        (equiv_inverse_map (Id Q (quotient_class X R x) V) (Id (Remainder (suc. n)) (E .map (quotient_class X R x)) (remainder_at n zero. star.))
          (equiv_inverse_characterization Q (Remainder (suc. n)) (quotient_set X R) (remainder_set (suc. n)) E
            (quotient_class X R x) (remainder_at n zero. star.))
          (concat (Remainder (suc. n)) (fbb .map k) (fbb .map (inr. star.)) (remainder_at n zero. star.)
            (refl (fbb .map) h) (remainder_equal (suc. n) (fbb .map (inr. star.)) (remainder_at n zero. star.) (refl zero.))))))

{` Fibers of g after choosing a representative x0 of the class. `}
def RootFiberAt (n : Nat) (c : Cycles) (x0 : c .fst .fst .fst) : Type
  ≔ Σ (RootFiber n c) (w ↦ Id (Remainder (suc. n)) (root_path_residue n c (w .fst) (w .snd) .fst x0) (remainder_at n zero. star.))

def root_fiber_map_fiber_equiv (n : Nat) (c : Cycles) (pr : RootFiberCondition n c)
  (x0 : c .fst .fst .fst) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  (s : Id (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) V
    (quotient_class (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd)) x0))
  : Equiv (BookFiber (RootFiber n c) (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)))
      (root_fiber_map n c) (pr, V)) (RootFiberAt n c x0)
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let Q ≔ ModQuotient n X (c .fst .snd) in let P ≔ RootFiberCondition n c in
    let PQ ≔ Product P Q in
    family_equiv (RootFiber n c) (w ↦ Id PQ (pr, V) (root_fiber_map n c w))
      (w ↦ Id (Remainder (suc. n)) (root_path_residue n c (w .fst) (w .snd) .fst x0) (remainder_at n zero. star.))
      (w ↦ let E ≔ root_path_quotient_equiv n c (w .fst) (w .snd) in
        let char ≔ equiv_inverse_characterization Q (Remainder (suc. n)) (quotient_set X R) (remainder_set (suc. n)) E
          (quotient_class X R x0) (remainder_at n zero. star.) in
        iff_equiv (Id PQ (pr, V) (root_fiber_map n c w))
          (Id (Remainder (suc. n)) (root_path_residue n c (w .fst) (w .snd) .fst x0) (remainder_at n zero. star.))
          (product_set P Q (prop_is_set P (root_fiber_condition_prop n c)) (quotient_set X R) (pr, V) (root_fiber_map n c w))
          (remainder_set (suc. n) (root_path_residue n c (w .fst) (w .snd) .fst x0) (remainder_at n zero. star.))
          (k ↦ char .map (concat Q (quotient_class X R x0) V (root_fiber_class n c w)
            (inverse Q V (quotient_class X R x0) s) (k .snd)))
          (z ↦ (root_fiber_condition_prop n c pr (root_path_condition n c (w .fst) (w .snd)),
            concat Q V (quotient_class X R x0) (root_fiber_class n c w) s
              (equiv_inverse_map (Id Q (quotient_class X R x0) (root_fiber_class n c w))
                (Id (Remainder (suc. n)) (E .map (quotient_class X R x0)) (remainder_at n zero. star.)) char z))))

{` Periods of a fiber element are the quotient subgroup. `}
def root_path_periods (n : Nat) (c d : Cycles) (p : Id Cycles c (cycle_root n d))
  : Id (Subtypes Int) (CyclePeriods d) (QuotientPeriods n c)
  ≔ let Y ≔ d .fst .fst .fst in let u ≔ d .fst .snd in let m : Int ≔ pos. (suc. n) in
    inclusion_antisym Int (CyclePeriods d) (QuotientPeriods n c)
      (q h ↦ transport Cycles (e ↦ CyclePeriods e (int_mul q m) .fst) (cycle_root n d) c
        (inverse Cycles c (cycle_root n d) p) (root_period_from_scaled n Y u q h))
      (q h ↦ root_period_quotient n Y u (int_mul q m)
        (transport Cycles (e ↦ CyclePeriods e (int_mul q m) .fst) c (cycle_root n d) p h)
        (q, refl (int_mul q m)))

def root_fiber_at_forget (n : Nat) (c : Cycles) (x0 : c .fst .fst .fst) (v : RootFiberAt n c x0)
  : PointedCyclesOfOrder (quotient_order n c)
  ≔ let d ≔ v .fst .fst in let p ≔ v .fst .snd in
    ((d, order_periods_injective (cycle_order d) (quotient_order n c)
        (concat (Subtypes Int) (CyclePeriods d) (QuotientPeriods n c) (order_periods (quotient_order n c))
          (root_path_periods n c d p)
          (inverse (Subtypes Int) (order_periods (quotient_order n c)) (QuotientPeriods n c) (quotient_order_periods n c)))),
     cycle_path_evaluate c (cycle_root n d) p x0 .snd)

def root_fiber_order_periods (n : Nat) (c : Cycles) (pr : RootFiberCondition n c) (u : CyclesOfOrder (quotient_order n c))
  : Id (Subtypes Int) (CyclePeriods c) (CyclePeriods (cycle_root n (u .fst)))
  ≔ let S ≔ ScaledSubtype (suc. n) in
    concat (Subtypes Int) (CyclePeriods c) (S (QuotientPeriods n c)) (CyclePeriods (cycle_root n (u .fst)))
      (quotient_periods_scaled n c pr)
      (inverse (Subtypes Int) (CyclePeriods (cycle_root n (u .fst))) (S (QuotientPeriods n c))
        (concat (Subtypes Int) (CyclePeriods (cycle_root n (u .fst))) (S (CyclePeriods (u .fst))) (S (QuotientPeriods n c))
          (root_cycle_periods n (u .fst))
          (refl S (concat (Subtypes Int) (CyclePeriods (u .fst)) (order_periods (quotient_order n c)) (QuotientPeriods n c)
            (refl order_periods (u .snd)) (quotient_order_periods n c)))))

def root_fiber_pointed_paths (n : Nat) (c : Cycles) (pr : RootFiberCondition n c) (x0 : c .fst .fst .fst)
  (u : CyclesOfOrder (quotient_order n c)) (y : u .fst .fst .fst .fst)
  : BookIsContr (PointedCyclePaths c (cycle_root n (u .fst)) x0 (inr. star., y))
  ≔ cycle_periods_imply_pointed c (cycle_root n (u .fst)) (root_fiber_order_periods n c pr u) x0 (inr. star., y)

def root_fiber_at_build (n : Nat) (c : Cycles) (pr : RootFiberCondition n c) (x0 : c .fst .fst .fst)
  (v : PointedCyclesOfOrder (quotient_order n c)) : RootFiberAt n c x0
  ≔ let pp ≔ root_fiber_pointed_paths n c pr x0 (v .fst) (v .snd) .center in
    let fbb ≔ fin_book_below_equiv (suc. n) in
    ((v .fst .fst, pp .fst),
     concat (Remainder (suc. n)) (fbb .map (cycle_path_evaluate c (cycle_root n (v .fst .fst)) (pp .fst) x0 .fst))
       (fbb .map (inr. star.)) (remainder_at n zero. star.)
       (refl ((t ↦ fbb .map (t .fst)) : Product (Fin (suc. n)) (v .fst .fst .fst .fst .fst) → Remainder (suc. n)) (pp .snd))
       (remainder_equal (suc. n) (fbb .map (inr. star.)) (remainder_at n zero. star.) (refl zero.)))

def root_fiber_at_contractible (n : Nat) (c : Cycles) (pr : RootFiberCondition n c) (x0 : c .fst .fst .fst)
  : isContr (RootFiberAt n c x0)
  ≔ let fbb ≔ fin_book_below_equiv (suc. n) in
    contractible_retract (PointedCyclesOfOrder (quotient_order n c)) (RootFiberAt n c x0)
      (native_contraction (PointedCyclesOfOrder (quotient_order n c)) (pointed_cycles_of_order_contractible (quotient_order n c)))
      (root_fiber_at_build n c pr x0) (root_fiber_at_forget n c x0)
      (v ↦ let d ≔ v .fst .fst in let p ≔ v .fst .snd in
        let F ≔ Product (Fin (suc. n)) (d .fst .fst .fst) in
        let ev ≔ cycle_path_evaluate c (cycle_root n d) p x0 in
        let first_zero ≔ equivalence_injective (Fin (suc. n)) (Remainder (suc. n)) fbb (ev .fst) (inr. star.)
          (concat (Remainder (suc. n)) (fbb .map (ev .fst)) (remainder_at n zero. star.) (fbb .map (inr. star.))
            (v .snd) (remainder_equal (suc. n) (remainder_at n zero. star.) (fbb .map (inr. star.)) (refl zero.))) in
        let u ≔ root_fiber_at_forget n c x0 v in
        let contr ≔ root_fiber_pointed_paths n c pr x0 (u .fst) (u .snd) in
        let K ≔ contr .contract (p, (first_zero, refl (ev .snd))) in
        let B ≔ ((w ↦ Id (Remainder (suc. n)) (root_path_residue n c (w .fst) (w .snd) .fst x0) (remainder_at n zero. star.))
          : RootFiber n c → Type) in
        let W ≔ root_fiber_at_build n c pr x0 u in
        ((refl d, K .fst),
         pathover_of_eq (RootFiber n c) B (W .fst) (d, p) (refl d, K .fst) (W .snd) (v .snd)
           (remainder_set (suc. n) (root_path_residue n c d p .fst x0) (remainder_at n zero. star.)
             (transport (RootFiber n c) B (W .fst) (d, p) (refl d, K .fst) (W .snd)) (v .snd))))

{` thm:fiber-cdg: the book's map g is an equivalence for any cycle (X,t). `}
def root_fiber_map_is_equiv (n : Nat) (c : Cycles)
  : BookIsEquiv (RootFiber n c) (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)))
      (root_fiber_map n c)
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let Q ≔ ModQuotient n X (c .fst .snd) in let PQ ≔ Product (RootFiberCondition n c) Q in
    b ↦ mere_rec (BookFiber X Q (quotient_class X R) (b .snd))
      (BookIsContr (BookFiber (RootFiber n c) PQ (root_fiber_map n c) b))
      (book_iscontr_isprop (BookFiber (RootFiber n c) PQ (root_fiber_map n c) b))
      (a ↦ book_contractibility_equiv (RootFiberAt n c (a .fst)) (BookFiber (RootFiber n c) PQ (root_fiber_map n c) b)
        (inverse_equiv (BookFiber (RootFiber n c) PQ (root_fiber_map n c) b) (RootFiberAt n c (a .fst))
          (root_fiber_map_fiber_equiv n c (b .fst) (a .fst) (b .snd) (a .snd)))
        .map (book_contraction (RootFiberAt n c (a .fst)) (root_fiber_at_contractible n c (b .fst) (a .fst))))
      (quotient_surjective X R (b .snd))

def root_fiber_equiv (n : Nat) (c : Cycles)
  : BookEquiv (RootFiber n c) (Product (RootFiberCondition n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)))
  ≔ (root_fiber_map n c, root_fiber_map_is_equiv n c)
