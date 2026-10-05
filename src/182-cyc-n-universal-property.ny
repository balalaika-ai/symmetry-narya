export "181-cyc-n-loop-cycles"

{` T(x) from the proof of prop:ump-cycn-into-groupoids: b : A with
   pi : (pt_n = x) → (a = b) such that pi(tau sigma_n) = pi(tau) s. `}
def CycLiftData (b : Nat) (A : Type) (a : A) (s : Id A a a) (x : CycleComponent (suc. b)) : Type
  ≔ Σ A (y ↦ PermutationMap (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) x) (Id A a y)
      (loop_concat_equiv (CycleComponent (suc. b)) (principal_component_point (suc. b)) x (cyc_generator b))
      (loop_concat_equiv A a y s))

def cyc_lift_pointed (b : Nat) (A : Type) (hA : isGroupoid A) (a : A) (s : Id A a a)
  (h : Id (Id A a a) (refl a) (loop_power_nat A a s (suc. b))) (y : A) (q : Id A a y)
  : PointedPermutationMaps (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (Id A a y)
      (loop_concat_equiv (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b))
        (cyc_generator b))
      (loop_concat_equiv A a y s) (refl (principal_component_point (suc. b))) q
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    pointed_cycle_map (Id C pt pt) (Id A a y) (cyc_loops_set b) (hA a y) (loop_concat_equiv C pt pt (cyc_generator b))
      (loop_concat_equiv A a y s) (cyc_loops_cyclic b) (cyc_loops_period_inclusion b A a y s (hA a y) h) (refl pt) q

{` T(pt_n) is a retract of the based path space at a, via evaluation at refl. `}
def cyc_lift_base_contractible (b : Nat) (A : Type) (hA : isGroupoid A) (a : A) (s : Id A a a)
  (h : Id (Id A a a) (refl a) (loop_power_nat A a s (suc. b)))
  : isContr (CycLiftData b A a s (principal_component_point (suc. b)))
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let L ≔ Id C pt pt in let e ≔ loop_concat_equiv C pt pt (cyc_generator b) in
    contractible_retract (Σ A (y ↦ Id A a y)) (CycLiftData b A a s pt) (based_paths_from_contractible A a)
      (u ↦ (u .fst, cyc_lift_pointed b A hA a s h (u .fst) (u .snd) .fst))
      (v ↦ (v .fst, v .snd .fst (refl pt)))
      (v ↦ (refl (v .fst),
        refl ((g ↦ g .fst) : PointedPermutationMaps L (Id A a (v .fst)) e (loop_concat_equiv A a (v .fst) s)
            (refl pt) (v .snd .fst (refl pt)) → PermutationMap L (Id A a (v .fst)) e (loop_concat_equiv A a (v .fst) s))
          (pointed_cycle_maps_prop L (Id A a (v .fst)) (hA a (v .fst)) e (loop_concat_equiv A a (v .fst) s)
            (cyc_loops_cyclic b) (refl pt) (v .snd .fst (refl pt))
            (cyc_lift_pointed b A hA a s h (v .fst) (v .snd .fst (refl pt)))
            (v .snd, refl (v .snd .fst (refl pt))))))

{` T(x) is contractible for every x in the connected type Cyc_n. `}
def cyc_lift_contractible (b : Nat) (A : Type) (hA : isGroupoid A) (a : A) (s : Id A a a)
  (h : Id (Id A a a) (refl a) (loop_power_nat A a s (suc. b))) (x : CycleComponent (suc. b))
  : BookIsContr (CycLiftData b A a s x)
  ≔ let pt ≔ principal_component_point (suc. b) in
    mere_rec (Id Cycles (finite_standard_cycle b) (x .fst)) (BookIsContr (CycLiftData b A a s x))
      (book_iscontr_isprop (CycLiftData b A a s x))
      (p ↦ transport (CycleComponent (suc. b)) (y ↦ BookIsContr (CycLiftData b A a s y)) pt x
        (subtype_equal Cycles (c ↦ Mere (Id Cycles (finite_standard_cycle b) c)) (cyc_component_prop b) pt x p)
        (book_contraction (CycLiftData b A a s pt) (cyc_lift_base_contractible b A hA a s h)))
      (x .snd)

{` The codomain of ev_{n,A}: a point, a symmetry s and refl a = s^n. `}
def CycSymmetryData (b : Nat) (A : Type) : Type
  ≔ Σ A (a ↦ Σ (Id A a a) (s ↦ Id (Id A a a) (refl a) (loop_power_nat A a s (suc. b))))

{` ev_{n,A}(f) = (f(pt_n), ap_f(sigma_n), !). `}
def cyc_evaluation (b : Nat) (A : Type) (f : CycleComponent (suc. b) → A) : CycSymmetryData b A
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    (f pt, (refl f (cyc_generator b),
      concat (Id A (f pt) (f pt)) (refl (f pt)) (refl f (loop_power_nat C pt (cyc_generator b) (suc. b)))
        (loop_power_nat A (f pt) (refl f (cyc_generator b)) (suc. b))
        (refl ((t ↦ refl f t) : Id C pt pt → Id A (f pt) (f pt)) (cyc_generator_order b))
        (map_path_loop_power_nat C A f pt (cyc_generator b) (suc. b))))

{` The inverse map: f(x) is the first component of the center of T(x). `}
def cyc_extension (b : Nat) (A : Type) (hA : isGroupoid A) (u : CycSymmetryData b A)
  (x : CycleComponent (suc. b)) : A
  ≔ cyc_lift_contractible b A hA (u .fst) (u .snd .fst) (u .snd .snd) x .center .fst

def cyc_extension_evaluation (b : Nat) (A : Type) (hA : isGroupoid A) (f : CycleComponent (suc. b) → A)
  : Id (CycleComponent (suc. b) → A) (cyc_extension b A hA (cyc_evaluation b A f)) f
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let sg ≔ cyc_generator b in
    funext C (_ ↦ A) (cyc_extension b A hA (cyc_evaluation b A f)) f (x ↦
      refl ((w ↦ w .fst) : CycLiftData b A (f pt) (refl f sg) x → A)
        (cyc_lift_contractible b A hA (f pt) (refl f sg) (cyc_evaluation b A f .snd .snd) x .contract
          (f x, ((t ↦ refl f t), (t ↦ map_path_concat C A f pt pt x sg t)))))

{` The naturality of the lifts, by path induction. `}
def cyc_lift_naturality (b : Nat) (A : Type) (hA : isGroupoid A) (u : CycSymmetryData b A)
  (x x' : CycleComponent (suc. b)) (al : Id (CycleComponent (suc. b)) x x')
  (t : Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) x)
  : Id (Id A (u .fst) (cyc_extension b A hA u x'))
      (concat A (u .fst) (cyc_extension b A hA u x) (cyc_extension b A hA u x')
        (cyc_lift_contractible b A hA (u .fst) (u .snd .fst) (u .snd .snd) x .center .snd .fst t)
        (refl (cyc_extension b A hA u) al))
      (cyc_lift_contractible b A hA (u .fst) (u .snd .fst) (u .snd .snd) x' .center .snd .fst
        (concat (CycleComponent (suc. b)) (principal_component_point (suc. b)) x x' t al))
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let a ≔ u .fst in let F ≔ cyc_extension b A hA u in
    let pi ≔ ((y ↦ cyc_lift_contractible b A hA (u .fst) (u .snd .fst) (u .snd .snd) y .center .snd .fst)
      : (y : C) → Id C pt y → Id A a (F y)) in
    J C x (x' al ↦ Id (Id A a (F x')) (concat A a (F x) (F x') (pi x t) (refl F al)) (pi x' (concat C pt x x' t al)))
      (concat (Id A a (F x)) (concat A a (F x) (F x) (pi x t) (refl (F x))) (pi x t) (pi x (concat C pt x x t (refl x)))
        (concat_p1 A a (F x) (pi x t))
        (refl (pi x) (inverse (Id C pt x) (concat C pt x x t (refl x)) t (concat_p1 C pt x t))))
      x' al

{` ap_f(sigma_n) p = p s for p = pi_pt(refl), in the book's applicative order. `}
def cyc_lift_coherence (b : Nat) (A : Type) (hA : isGroupoid A) (u : CycSymmetryData b A)
  : Id (Id A (u .fst) (cyc_extension b A hA u (principal_component_point (suc. b))))
      (concat A (u .fst) (cyc_extension b A hA u (principal_component_point (suc. b)))
        (cyc_extension b A hA u (principal_component_point (suc. b)))
        (cyc_lift_contractible b A hA (u .fst) (u .snd .fst) (u .snd .snd) (principal_component_point (suc. b))
          .center .snd .fst (refl (principal_component_point (suc. b))))
        (refl (cyc_extension b A hA u) (cyc_generator b)))
      (concat A (u .fst) (u .fst) (cyc_extension b A hA u (principal_component_point (suc. b))) (u .snd .fst)
        (cyc_lift_contractible b A hA (u .fst) (u .snd .fst) (u .snd .snd) (principal_component_point (suc. b))
          .center .snd .fst (refl (principal_component_point (suc. b)))))
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let sg ≔ cyc_generator b in
    let center ≔ cyc_lift_contractible b A hA (u .fst) (u .snd .fst) (u .snd .snd) pt .center in
    let pi ≔ center .snd .fst in
    calc
      concat A (u .fst) (cyc_extension b A hA u pt) (cyc_extension b A hA u pt) (pi (refl pt)) (refl (cyc_extension b A hA u) sg)
      = pi (concat C pt pt pt (refl pt) sg) by cyc_lift_naturality b A hA u pt pt sg (refl pt)
      = pi sg by refl pi (concat_1p C pt pt sg)
      = pi (concat C pt pt pt sg (refl pt)) by refl pi (inverse (Id C pt pt) (concat C pt pt pt sg (refl pt)) sg (concat_p1 C pt pt sg))
      = concat A (u .fst) (u .fst) (cyc_extension b A hA u pt) (u .snd .fst) (pi (refl pt)) by center .snd .snd (refl pt) ∎

{` A path (y, l, !) = (a, s, !) in the codomain of ev_{n,A} from P : a = y
   with l P = P s in the book's applicative order. `}
def cyc_symmetry_path (b : Nat) (A : Type) (hA : isGroupoid A) (u : CycSymmetryData b A) (y : A) (l : Id A y y)
  (k : Id (Id A y y) (refl y) (loop_power_nat A y l (suc. b))) (P : Id A (u .fst) y)
  (coh : Id (Id A (u .fst) y) (concat A (u .fst) y y P l) (concat A (u .fst) (u .fst) y (u .snd .fst) P))
  : Id (CycSymmetryData b A) (y, (l, k)) u
  ≔ let a ≔ u .fst in let s ≔ u .snd .fst in
    let Q ≔ inverse A a y P in
    let H ≔ ((x ↦ (m ↦ Id (Id A x x) (refl x) (loop_power_nat A x m (suc. b)))) : (x : A) → Id A x x → Type) in
    let Fam ≔ ((x ↦ Σ (Id A x x) (H x)) : A → Type) in
    let eq1 ≔ calc
        transport A ((z ↦ Id A z z) : A → Type) y a Q l
        = concat A a y a (concat A a y y (inverse A y a Q) l) Q by transport_loop_family A y a Q l
        = concat A a y a (concat A a y y P l) Q
          by refl ((r ↦ concat A a y a (concat A a y y r l) Q) : Id A a y → Id A a a) (inverse_inverse A a y P)
        = concat A a y a (concat A a a y s P) Q by refl ((r ↦ concat A a y a r Q) : Id A a y → Id A a a) coh
        = concat A a a a s (concat A a y a P Q) by concat_assoc A a a y a s P Q
        = concat A a a a s (refl a) by refl (concat A a a a s) (concat_inverse_right A a y P)
        = s by concat_p1 A a a s ∎ in
    (Q, pathover_of_eq A Fam y a Q (l, k) (u .snd)
      (subtype_equal (Id A a a) (H a) (m ↦ hA a a (refl a) (loop_power_nat A a m (suc. b)))
        (transport A Fam y a Q (l, k)) (u .snd) eq1))

def cyc_evaluation_extension (b : Nat) (A : Type) (hA : isGroupoid A) (u : CycSymmetryData b A)
  : Id (CycSymmetryData b A) (cyc_evaluation b A (cyc_extension b A hA u)) u
  ≔ let pt ≔ principal_component_point (suc. b) in
    cyc_symmetry_path b A hA u (cyc_extension b A hA u pt) (refl (cyc_extension b A hA u) (cyc_generator b))
      (cyc_evaluation b A (cyc_extension b A hA u) .snd .snd)
      (cyc_lift_contractible b A hA (u .fst) (u .snd .fst) (u .snd .snd) pt .center .snd .fst (refl pt))
      (cyc_lift_coherence b A hA u)

{` prop:ump-cycn-into-groupoids: for n = suc b > 0 and every groupoid A,
   ev_{n,A} : (Cyc_n → A) → Σ(a:A) Σ(s : a = a) (refl a = s^n) is an equivalence. `}
def cyc_universal_property (b : Nat) (A : Type) (hA : isGroupoid A)
  : BookEquiv (CycleComponent (suc. b) → A) (CycSymmetryData b A)
  ≔ book_quasi_inverse_equiv (CycleComponent (suc. b) → A) (CycSymmetryData b A) (cyc_evaluation b A)
      (cyc_extension b A hA) (cyc_extension_evaluation b A hA) (cyc_evaluation_extension b A hA)

def cyc_evaluation_is_equiv (b : Nat) (A : Type) (hA : isGroupoid A)
  : BookIsEquiv (CycleComponent (suc. b) → A) (CycSymmetryData b A) (cyc_evaluation b A)
  ≔ cyc_universal_property b A hA .equiv
