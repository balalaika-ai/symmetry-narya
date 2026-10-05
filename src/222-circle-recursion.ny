export "221-circle-loops"

{` T(x) = Σ(y:A) maps π : (base = x) → (a = y) with π(loop·τ) = s·π(τ). `}
def CircleLiftData (A : Type) (a : A) (s : Id A a a) (x : CycleComponent zero.) : Type
  ≔ Σ A (y ↦ PermutationMap (Id (CycleComponent zero.) (principal_component_point zero.) x) (Id A a y)
      (loop_concat_equiv (CycleComponent zero.) (principal_component_point zero.) x circle_loop)
      (loop_concat_equiv A a y s))

{` T(base) is contractible for every type A: it is equivalent to Σ(y:A)(a = y). `}
def circle_lift_base_contractible (A : Type) (a : A) (s : Id A a a)
  : isContr (CircleLiftData A a s (principal_component_point zero.))
  ≔ let C ≔ CycleComponent zero. in let pt ≔ principal_component_point zero. in
    hlevel_equiv zero. (Σ A (y ↦ Id A a y)) (CircleLiftData A a s pt)
      (canonical_inverse_equiv (CircleLiftData A a s pt) (Σ A (y ↦ Id A a y))
        (family_equiv A
          (y ↦ PermutationMap (Id C pt pt) (Id A a y) (loop_concat_equiv C pt pt circle_loop) (loop_concat_equiv A a y s))
          (y ↦ Id A a y)
          (y ↦ circle_loop_actions (Id A a y) (loop_concat_equiv A a y s))))
      (based_paths_from_contractible A a)

{` T(x) is contractible for every x of the connected type Cyc_0. `}
def circle_lift_contractible (A : Type) (a : A) (s : Id A a a) (x : CycleComponent zero.)
  : BookIsContr (CircleLiftData A a s x)
  ≔ let pt ≔ principal_component_point zero. in
    mere_rec (Id Cycles infinite_cycle (x .fst)) (BookIsContr (CircleLiftData A a s x))
      (book_iscontr_isprop (CircleLiftData A a s x))
      (p ↦ transport (CycleComponent zero.) (y ↦ BookIsContr (CircleLiftData A a s y)) pt x
        (subtype_equal Cycles (c ↦ Mere (Id Cycles infinite_cycle c)) circle_component_prop pt x p)
        (book_contraction (CircleLiftData A a s pt) (circle_lift_base_contractible A a s)))
      (x .snd)

{` ev_A(f) = (f(base), ap_f(loop)). `}
def circle_evaluation (A : Type) (f : CycleComponent zero. → A) : FreeLoop A
  ≔ (f (principal_component_point zero.), refl f circle_loop)

def circle_extension (A : Type) (u : FreeLoop A) (x : CycleComponent zero.) : A
  ≔ circle_lift_contractible A (u .fst) (u .snd) x .center .fst

def circle_extension_evaluation (A : Type) (f : CycleComponent zero. → A)
  : Id (CycleComponent zero. → A) (circle_extension A (circle_evaluation A f)) f
  ≔ let C ≔ CycleComponent zero. in let pt ≔ principal_component_point zero. in
    funext C (_ ↦ A) (circle_extension A (circle_evaluation A f)) f (x ↦
      refl ((w ↦ w .fst) : CircleLiftData A (f pt) (refl f circle_loop) x → A)
        (circle_lift_contractible A (f pt) (refl f circle_loop) x .contract
          (f x, ((t ↦ refl f t), (t ↦ map_path_concat C A f pt pt x circle_loop t)))))

def circle_lift_naturality (A : Type) (u : FreeLoop A)
  (x x' : CycleComponent zero.) (al : Id (CycleComponent zero.) x x')
  (t : Id (CycleComponent zero.) (principal_component_point zero.) x)
  : Id (Id A (u .fst) (circle_extension A u x'))
      (concat A (u .fst) (circle_extension A u x) (circle_extension A u x')
        (circle_lift_contractible A (u .fst) (u .snd) x .center .snd .fst t)
        (refl (circle_extension A u) al))
      (circle_lift_contractible A (u .fst) (u .snd) x' .center .snd .fst
        (concat (CycleComponent zero.) (principal_component_point zero.) x x' t al))
  ≔ let C ≔ CycleComponent zero. in let pt ≔ principal_component_point zero. in
    let a ≔ u .fst in let F ≔ circle_extension A u in
    let pi ≔ ((y ↦ circle_lift_contractible A (u .fst) (u .snd) y .center .snd .fst)
      : (y : C) → Id C pt y → Id A a (F y)) in
    J C x (x' al ↦ Id (Id A a (F x')) (concat A a (F x) (F x') (pi x t) (refl F al)) (pi x' (concat C pt x x' t al)))
      (concat (Id A a (F x)) (concat A a (F x) (F x) (pi x t) (refl (F x))) (pi x t) (pi x (concat C pt x x t (refl x)))
        (concat_p1 A a (F x) (pi x t))
        (refl (pi x) (inverse (Id C pt x) (concat C pt x x t (refl x)) t (concat_p1 C pt x t))))
      x' al

def circle_lift_coherence (A : Type) (u : FreeLoop A)
  : Id (Id A (u .fst) (circle_extension A u (principal_component_point zero.)))
      (concat A (u .fst) (circle_extension A u (principal_component_point zero.))
        (circle_extension A u (principal_component_point zero.))
        (circle_lift_contractible A (u .fst) (u .snd) (principal_component_point zero.)
          .center .snd .fst (refl (principal_component_point zero.)))
        (refl (circle_extension A u) circle_loop))
      (concat A (u .fst) (u .fst) (circle_extension A u (principal_component_point zero.)) (u .snd)
        (circle_lift_contractible A (u .fst) (u .snd) (principal_component_point zero.)
          .center .snd .fst (refl (principal_component_point zero.))))
  ≔ let C ≔ CycleComponent zero. in let pt ≔ principal_component_point zero. in
    let center ≔ circle_lift_contractible A (u .fst) (u .snd) pt .center in
    let pi ≔ center .snd .fst in
    calc
      concat A (u .fst) (circle_extension A u pt) (circle_extension A u pt) (pi (refl pt)) (refl (circle_extension A u) circle_loop)
      = pi (concat C pt pt pt (refl pt) circle_loop) by circle_lift_naturality A u pt pt circle_loop (refl pt)
      = pi circle_loop by refl pi (concat_1p C pt pt circle_loop)
      = pi (concat C pt pt pt circle_loop (refl pt))
        by refl pi (inverse (Id C pt pt) (concat C pt pt pt circle_loop (refl pt)) circle_loop (concat_p1 C pt pt circle_loop))
      = concat A (u .fst) (u .fst) (circle_extension A u pt) (u .snd) (pi (refl pt)) by center .snd .snd (refl pt) ∎

{` A path (y, l) = (a, s) in the free loop type from P : a = y with l·P = P·s
   written as concat P l = concat s P. `}
def free_loop_path (A : Type) (u : FreeLoop A) (y : A) (l : Id A y y) (P : Id A (u .fst) y)
  (coh : Id (Id A (u .fst) y) (concat A (u .fst) y y P l) (concat A (u .fst) (u .fst) y (u .snd) P))
  : Id (FreeLoop A) (y, l) u
  ≔ let a ≔ u .fst in let s ≔ u .snd in
    let Q ≔ inverse A a y P in
    (Q, pathover_of_eq A ((z ↦ Id A z z) : A → Type) y a Q l s (calc
        transport A ((z ↦ Id A z z) : A → Type) y a Q l
        = concat A a y a (concat A a y y (inverse A y a Q) l) Q by transport_loop_family A y a Q l
        = concat A a y a (concat A a y y P l) Q
          by refl ((r ↦ concat A a y a (concat A a y y r l) Q) : Id A a y → Id A a a) (inverse_inverse A a y P)
        = concat A a y a (concat A a a y s P) Q by refl ((r ↦ concat A a y a r Q) : Id A a y → Id A a a) coh
        = concat A a a a s (concat A a y a P Q) by concat_assoc A a a y a s P Q
        = concat A a a a s (refl a) by refl (concat A a a a s) (concat_inverse_right A a y P)
        = s by concat_p1 A a a s ∎))

def circle_evaluation_extension (A : Type) (u : FreeLoop A)
  : Id (FreeLoop A) (circle_evaluation A (circle_extension A u)) u
  ≔ let pt ≔ principal_component_point zero. in
    free_loop_path A u (circle_extension A u pt) (refl (circle_extension A u) circle_loop)
      (circle_lift_contractible A (u .fst) (u .snd) pt .center .snd .fst (refl pt))
      (circle_lift_coherence A u)

{` lem:freeloopspace for the constructed circle: for EVERY type A,
   ev : (Cyc_0 → A) → Σ(a:A)(a = a) is an equivalence. `}
def circle_universal_equiv (A : Type) : BookEquiv (CycleComponent zero. → A) (FreeLoop A)
  ≔ book_quasi_inverse_equiv (CycleComponent zero. → A) (FreeLoop A) (circle_evaluation A)
      (circle_extension A) (circle_extension_evaluation A) (circle_evaluation_extension A)
