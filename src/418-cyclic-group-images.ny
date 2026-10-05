export "417-cyclic-groups"
export "413-group-motivation"

{` Chapter 4, ex:Cm, xca:CG2isSG2, xca:RmloopCGm and ex:groups-morphisms item 4
   (group.tex 568-663, 1180-1199), for every circle C and m = n+1.

   Notation: C_m = cyclic_group_fin n with BC_m = (Cyc_m, (m, s)) on the
   literal standard cycle (Fin m, s); Σ_m = symmetric_group m with
   BΣ_m = (FinSet_m, m). `}

{` General lemmas. Ω k preserves integer powers. `}
def loops_map_power_nat (X Y : Pointed) (k : BookPointedMap X Y) (l : Loop X) (m : Nat)
  : Id (Loop Y) (loops_map X Y k (loop_power_nat (X .carrier) (X .point) l m))
      (loop_power_nat (Y .carrier) (Y .point) (loops_map X Y k l) m)
  ≔ match m [
  | zero. ↦ loops_map_unit X Y k
  | suc. m ↦ concat (Loop Y)
      (loops_map X Y k (concat (X .carrier) (X .point) (X .point) (X .point) (loop_power_nat (X .carrier) (X .point) l m) l))
      (concat (Y .carrier) (Y .point) (Y .point) (Y .point)
        (loops_map X Y k (loop_power_nat (X .carrier) (X .point) l m)) (loops_map X Y k l))
      (concat (Y .carrier) (Y .point) (Y .point) (Y .point)
        (loop_power_nat (Y .carrier) (Y .point) (loops_map X Y k l) m) (loops_map X Y k l))
      (loops_map_concat X Y k (loop_power_nat (X .carrier) (X .point) l m) l)
      (refl ((r ↦ concat (Y .carrier) (Y .point) (Y .point) (Y .point) r (loops_map X Y k l)) : Loop Y → Loop Y)
        (loops_map_power_nat X Y k l m)) ]

def loops_map_power (X Y : Pointed) (k : BookPointedMap X Y) (l : Loop X) (z : Int)
  : Id (Loop Y) (loops_map X Y k (loop_power (X .carrier) (X .point) l z))
      (loop_power (Y .carrier) (Y .point) (loops_map X Y k l) z)
  ≔ match z [
  | pos. m ↦ loops_map_power_nat X Y k l m
  | neg. m ↦ concat (Loop Y)
      (loops_map X Y k (loop_power_nat (X .carrier) (X .point) (inverse (X .carrier) (X .point) (X .point) l) (suc. m)))
      (loop_power_nat (Y .carrier) (Y .point) (loops_map X Y k (inverse (X .carrier) (X .point) (X .point) l)) (suc. m))
      (loop_power_nat (Y .carrier) (Y .point) (inverse (Y .carrier) (Y .point) (Y .point) (loops_map X Y k l)) (suc. m))
      (loops_map_power_nat X Y k (inverse (X .carrier) (X .point) (X .point) l) (suc. m))
      (refl ((r ↦ loop_power_nat (Y .carrier) (Y .point) r (suc. m)) : Loop Y → Loop Y)
        (loops_map_inverse X Y k l)) ]

{` A pointed map f between connected types whose action on loops is
   surjective has connected fibers (it is 0-connected). `}
def loop_conjugate_solve (B : Type) (b c : B) (fp : Id B b c) (k : Id B c c) (p : Id B b c)
  (e : Id (Id B b b) (pointed_loop_conjugate B b c fp k) (concat B b c b p (inverse B b c fp)))
  : Id (Id B b c) (concat B b c c fp k) p
  ≔ calc
      concat B b c c fp k
      = concat B b b c (concat B b c b (concat B b c c fp k) (inverse B b c fp)) fp
        by inverse (Id B b c) (concat B b b c (concat B b c b (concat B b c c fp k) (inverse B b c fp)) fp)
          (concat B b c c fp k) (concat_cancel_final_inverse_general B b c (concat B b c c fp k) fp)
      = concat B b b c (pointed_loop_conjugate B b c fp k) fp
        by refl ((l ↦ concat B b b c l fp) : Id B b b → Id B b c)
          (concat_assoc B b c c b fp k (inverse B b c fp))
      = concat B b b c (concat B b c b p (inverse B b c fp)) fp
        by refl ((l ↦ concat B b b c l fp) : Id B b b → Id B b c) e
      = p by concat_cancel_final_inverse_general B b c p fp ∎

def LoopsSurjective (A : Type) (a : A) (B : Type) (b : B) (f : A → B) (fp : Id B b (f a)) : Type
  ≔ (q : Id B b b) → Mere (Σ (Id A a a) (l ↦ Id (Id B b b) (pointed_loop_conjugate B b (f a) fp (refl f l)) q))

def base_fiber_reachable (A : Type) (a : A) (B : Type) (b : B) (f : A → B) (fp : Id B b (f a))
  (h : LoopsSurjective A a B b f fp) (p : Id B b (f a))
  : Mere (Id (BookFiber A B f b) (a, fp) (a, p))
  ≔ mere_rec (Σ (Id A a a) (l ↦ Id (Id B b b) (pointed_loop_conjugate B b (f a) fp (refl f l))
        (concat B b (f a) b p (inverse B b (f a) fp))))
      (Mere (Id (BookFiber A B f b) (a, fp) (a, p))) (mere_isprop (Id (BookFiber A B f b) (a, fp) (a, p)))
      (w ↦ mere (Id (BookFiber A B f b) (a, fp) (a, p))
        (w .fst, pathover_of_eq A (x ↦ Id B b (f x)) a a (w .fst) fp p
          (loop_conjugate_solve B b (f a) fp (refl f (w .fst)) p (w .snd))))
      (h (concat B b (f a) b p (inverse B b (f a) fp)))

def fiber_point_reachable (A : Type) (a : A) (hA : Connected A) (B : Type) (b : B) (f : A → B) (fp : Id B b (f a))
  (h : LoopsSurjective A a B b f fp) (u : BookFiber A B f b)
  : Mere (Id (BookFiber A B f b) (a, fp) u)
  ≔ mere_rec (Id A a (u .fst)) (Mere (Id (BookFiber A B f b) (a, fp) u)) (mere_isprop (Id (BookFiber A B f b) (a, fp) u))
      (r ↦ J A a (x r ↦ (p : Id B b (f x)) → Mere (Id (BookFiber A B f b) (a, fp) (x, p)))
        (base_fiber_reachable A a B b f fp h) (u .fst) r (u .snd))
      (hA .snd a (u .fst))

def connected_fibers_from_loops (A : Type) (a : A) (hA : Connected A) (B : Type) (b : B) (hB : Connected B)
  (f : A → B) (fp : Id B b (f a)) (h : LoopsSurjective A a B b f fp)
  : ConnectedFibers A B f
  ≔ y ↦ mere_rec (Id B b y) (Connected (BookFiber A B f y)) (connected_prop (BookFiber A B f y))
      (r ↦ transport B (z ↦ Connected (BookFiber A B f z)) b y r
        (based_to_connected (BookFiber A B f b) (a, fp) (fiber_point_reachable A a hA B b f fp h)))
      (hB .snd b y)

{` The forgetful map prj : Cyc_m → FinSet_m, ((X, t), !) ↦ (X, !), pointed by
   reflexivity; it is the forgetful homomorphism C_m → Σ_m. `}
def CycFin (n : Nat) : Type ≔ NativeComponent Cycles (finite_fin_cycle n)

def cycfin_point (n : Nat) : CycFin n ≔ component_point Cycles (finite_fin_cycle n)

def cycle_forget_set (n : Nat) (u : CycFin n) : BookFiniteSetsAt (suc. n)
  ≔ (u .fst .fst .fst,
     mere_rec (Id Cycles (finite_fin_cycle n) (u .fst))
       (Mere (Id SetTypes (standard_set (suc. n)) (u .fst .fst .fst)))
       (mere_isprop (Id SetTypes (standard_set (suc. n)) (u .fst .fst .fst)))
       (p ↦ mere (Id SetTypes (standard_set (suc. n)) (u .fst .fst .fst)) (refl ((c ↦ c .fst .fst) : Cycles → SetTypes) p))
       (u .snd))

def cycle_forget_pointed (n : Nat) : BookPointedMap (BG (cyclic_group_fin n)) (BG (symmetric_group (suc. n)))
  ≔ (cycle_forget_set n, refl (shape (symmetric_group (suc. n))))

def cyclic_forget_hom (n : Nat) : GroupHom (cyclic_group_fin n) (symmetric_group (suc. n))
  ≔ mkhom (cyclic_group_fin n) (symmetric_group (suc. n)) (cycle_forget_pointed n)

{` The fiber of prj at X is the set of cycle structures on X:
   Σ(t : X ≃ X) ‖(m, s) = (X, t)‖ (identification in Σ(X:Set)(X ≃ X)). `}
def CycleStructuresOn (n : Nat) (X : BookFiniteSetsAt (suc. n)) : Type
  ≔ Σ (Equiv (X .fst .fst) (X .fst .fst)) (t ↦ Mere (Id Permutations (finite_fin_cycle n .fst) (X .fst, t)))

def cycle_structures_set (n : Nat) (X : BookFiniteSetsAt (suc. n)) : isSet (CycleStructuresOn n X)
  ≔ sigma_set (Equiv (X .fst .fst) (X .fst .fst)) (t ↦ Mere (Id Permutations (finite_fin_cycle n .fst) (X .fst, t)))
      (equivalences_set (X .fst .fst) (X .fst .fst) (X .fst .snd))
      (t ↦ prop_is_set (Mere (Id Permutations (finite_fin_cycle n .fst) (X .fst, t)))
        (mere_isprop (Id Permutations (finite_fin_cycle n .fst) (X .fst, t))))

def cyc_fin_split (n : Nat) (u : CycFin n) : Σ (BookFiniteSetsAt (suc. n)) (CycleStructuresOn n)
  ≔ (cycle_forget_set n u, (u .fst .fst .snd,
      mere_rec (Id Cycles (finite_fin_cycle n) (u .fst))
        (Mere (Id Permutations (finite_fin_cycle n .fst) (u .fst .fst)))
        (mere_isprop (Id Permutations (finite_fin_cycle n .fst) (u .fst .fst)))
        (p ↦ mere (Id Permutations (finite_fin_cycle n .fst) (u .fst .fst)) (refl ((c ↦ c .fst) : Cycles → Permutations) p))
        (u .snd)))

def structure_cyclic (n : Nat) (S : SetTypes) (t : Equiv (S .fst) (S .fst))
  (w : Mere (Id Permutations (finite_fin_cycle n .fst) (S, t))) : Cyclic (S .fst) t
  ≔ mere_rec (Id Permutations (finite_fin_cycle n .fst) (S, t)) (Cyclic (S .fst) t) (cyclic_prop (S .fst) t)
      (q ↦ transport Permutations cyclic_permutation (finite_fin_cycle n .fst) (S, t) q (finite_fin_cycle n .snd)) w

def cyc_fin_join (n : Nat) (y : Σ (BookFiniteSetsAt (suc. n)) (CycleStructuresOn n)) : CycFin n
  ≔ let S ≔ y .fst .fst in let t ≔ y .snd .fst in let w ≔ y .snd .snd in
    let c : Cycles ≔ ((S, t), structure_cyclic n S t w) in
    (c, mere_rec (Id Permutations (finite_fin_cycle n .fst) (S, t)) (Mere (Id Cycles (finite_fin_cycle n) c))
      (mere_isprop (Id Cycles (finite_fin_cycle n) c))
      (q ↦ mere (Id Cycles (finite_fin_cycle n) c)
        (subtype_equal Permutations cyclic_permutation (p ↦ cyclic_prop (p .fst .fst) (p .snd)) (finite_fin_cycle n) c q))
      w)

def cyc_fin_split_equiv (n : Nat) : Equiv (CycFin n) (Σ (BookFiniteSetsAt (suc. n)) (CycleStructuresOn n))
  ≔ quasi_inverse_equiv (CycFin n) (Σ (BookFiniteSetsAt (suc. n)) (CycleStructuresOn n)) (cyc_fin_split n) (cyc_fin_join n)
      (u ↦ component_path Cycles (finite_fin_cycle n) (cyc_fin_join n (cyc_fin_split n u)) u
        (subtype_equal Permutations cyclic_permutation (p ↦ cyclic_prop (p .fst .fst) (p .snd))
          (cyc_fin_join n (cyc_fin_split n u) .fst) (u .fst) (refl (u .fst .fst))))
      (y ↦ ((refl (y .fst .fst), mere_isprop (Id SetTypes (standard_set (suc. n)) (y .fst .fst))
              (cyc_fin_split n (cyc_fin_join n y) .fst .snd) (y .fst .snd)),
            (refl (y .snd .fst), mere_isprop (Id Permutations (finite_fin_cycle n .fst) (y .fst .fst, y .snd .fst))
              (cyc_fin_split n (cyc_fin_join n y) .snd .snd) (y .snd .snd))))

def cycle_forget_fiber_equiv (n : Nat) (X : BookFiniteSetsAt (suc. n))
  : Equiv (BookFiber (CycFin n) (BookFiniteSetsAt (suc. n)) (cycle_forget_set n) X) (CycleStructuresOn n X)
  ≔ compose_equiv (BookFiber (CycFin n) (BookFiniteSetsAt (suc. n)) (cycle_forget_set n) X)
      (BookFiber (Σ (BookFiniteSetsAt (suc. n)) (CycleStructuresOn n)) (BookFiniteSetsAt (suc. n)) (y ↦ y .fst) X)
      (CycleStructuresOn n X)
      (preequivalence_fiber_equiv (CycFin n) (Σ (BookFiniteSetsAt (suc. n)) (CycleStructuresOn n)) (BookFiniteSetsAt (suc. n))
        (cyc_fin_split_equiv n) (y ↦ y .fst) X)
      (projection_book_fiber_equiv (BookFiniteSetsAt (suc. n)) (CycleStructuresOn n) X)

def cycle_forget_covering (n : Nat) : IsCovering (CycFin n) (BookFiniteSetsAt (suc. n)) (cycle_forget_set n)
  ≔ X ↦ hlevel_two_to_set (BookFiber (CycFin n) (BookFiniteSetsAt (suc. n)) (cycle_forget_set n) X)
      (hlevel_equiv (suc. (suc. zero.)) (CycleStructuresOn n X)
        (BookFiber (CycFin n) (BookFiniteSetsAt (suc. n)) (cycle_forget_set n) X)
        (canonical_inverse_equiv (BookFiber (CycFin n) (BookFiniteSetsAt (suc. n)) (cycle_forget_set n) X)
          (CycleStructuresOn n X) (cycle_forget_fiber_equiv n X))
        (set_to_hlevel_two (CycleStructuresOn n X) (cycle_structures_set n X)))

{` R_m : BZ → BΣ_m (def:RmtoS1 lifted to FinSet_m): the circle recursor with
   base ↦ m and loop ↦ s (the symmetry of m given by the successor of the
   standard cycle), pointed by its computation rule (an identification; the
   book has R_m(base) ≡ m). Its underlying set family is ch3's R_m. `}
def finite_successor_symmetry (n : Nat) : USym (symmetric_group (suc. n))
  ≔ permutation_symmetry (standard_set (suc. n)) (finite_fin_successor n)

def power_finset_map (C : CircleSignature) (n : Nat) : C .carrier → BookFiniteSetsAt (suc. n)
  ≔ circle_rec C (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n)), finite_successor_symmetry n)

def power_finset_pointed (C : CircleSignature) (n : Nat)
  : BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n)))
  ≔ pointed_circle_loop_rec C (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n)

def power_finset_hom (C : CircleSignature) (n : Nat) : GroupHom (circle_group C) (symmetric_group (suc. n))
  ≔ mkhom (circle_group C) (symmetric_group (suc. n)) (power_finset_pointed C n)

def power_finset_loop (C : CircleSignature) (n : Nat)
  : Id (USym (symmetric_group (suc. n)))
      (usym_hom (circle_group C) (symmetric_group (suc. n)) (power_finset_hom C n) (C .loop))
      (finite_successor_symmetry n)
  ≔ pointed_circle_loop_rec_beta C (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n)

def finset_free_loop_forget (n : Nat) (d : FreeLoop (BookFiniteSetsAt (suc. n))) : FreeLoop SetTypes
  ≔ (d .fst .fst, refl ((X ↦ X .fst) : BookFiniteSetsAt (suc. n) → SetTypes) (d .snd))

def power_finset_underlying (C : CircleSignature) (n : Nat)
  : Id (C .carrier → SetTypes) (z ↦ power_finset_map C n z .fst) (power_circle_family C n)
  ≔ equivalence_injective (C .carrier → SetTypes) (FreeLoop SetTypes) (circle_universal_property C SetTypes)
      (z ↦ power_finset_map C n z .fst) (power_circle_family C n)
      (concat (FreeLoop SetTypes) (circle_eval C SetTypes (z ↦ power_finset_map C n z .fst))
        (power_fiber_set n, power_fiber_rotation n) (circle_eval C SetTypes (power_circle_family C n))
        (refl (finset_free_loop_forget n)
          (circle_rec_beta C (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n)), finite_successor_symmetry n)))
        (inverse (FreeLoop SetTypes) (circle_eval C SetTypes (power_circle_family C n)) (power_fiber_set n, power_fiber_rotation n)
          (power_circle_family_beta C n)))

{` ex:groups-morphisms (4): mod_m : Z → C_m, classified by the circle
   recursor base ↦ (m, s), loop ↦ s (the generating symmetry), pointed by its
   computation rule (the book: by reflexivity). `}
def cyclic_fin_generator (n : Nat) : USym (cyclic_group_fin n) ≔ cycle_group_generator (finite_fin_cycle n)

def mod_map (C : CircleSignature) (n : Nat) : C .carrier → CycFin n
  ≔ circle_rec C (CycFin n) (cycfin_point n, cyclic_fin_generator n)

def mod_pointed (C : CircleSignature) (n : Nat) : BookPointedMap (circle_pointed C) (BG (cyclic_group_fin n))
  ≔ pointed_circle_loop_rec C (CycFin n) (cycfin_point n) (cyclic_fin_generator n)

def mod_hom (C : CircleSignature) (n : Nat) : GroupHom (circle_group C) (cyclic_group_fin n)
  ≔ mkhom (circle_group C) (cyclic_group_fin n) (mod_pointed C n)

def mod_hom_loop (C : CircleSignature) (n : Nat)
  : Id (USym (cyclic_group_fin n)) (usym_hom (circle_group C) (cyclic_group_fin n) (mod_hom C n) (C .loop))
      (cyclic_fin_generator n)
  ≔ pointed_circle_loop_rec_beta C (CycFin n) (cycfin_point n) (cyclic_fin_generator n)

{` prj sends the generating symmetry (s, !) of (m, s) to s. `}
def cycfin_carrier (n : Nat) (u : CycFin n) : Type ≔ u .fst .fst .fst .fst

def forget_generator_type_path (n : Nat)
  : Id (Id Type (Fin (suc. n)) (Fin (suc. n))) (refl (cycfin_carrier n) (cyclic_fin_generator n))
      (ua (Fin (suc. n)) (Fin (suc. n)) (finite_fin_successor n))
  ≔ equivalence_injective (Id Type (Fin (suc. n)) (Fin (suc. n))) (Equiv (Fin (suc. n)) (Fin (suc. n)))
      (transport_univalence_equiv (Fin (suc. n)) (Fin (suc. n)))
      (refl (cycfin_carrier n) (cyclic_fin_generator n)) (ua (Fin (suc. n)) (Fin (suc. n)) (finite_fin_successor n))
      (equiv_homotopy (Fin (suc. n)) (Fin (suc. n))
        (transport_equiv (Fin (suc. n)) (Fin (suc. n)) (refl (cycfin_carrier n) (cyclic_fin_generator n)))
        (transport_equiv (Fin (suc. n)) (Fin (suc. n)) (ua (Fin (suc. n)) (Fin (suc. n)) (finite_fin_successor n)))
        (x ↦ cycle_generating_loop_action (finite_fin_cycle n) x))

def cycfin_set (n : Nat) (u : CycFin n) : SetTypes ≔ u .fst .fst .fst

def forget_generator_set_path (n : Nat)
  : Id (Id SetTypes (standard_set (suc. n)) (standard_set (suc. n))) (refl (cycfin_set n) (cyclic_fin_generator n))
      (set_types_path (standard_set (suc. n)) (standard_set (suc. n)) (finite_fin_successor n))
  ≔ equivalence_injective (Id SetTypes (standard_set (suc. n)) (standard_set (suc. n)))
      (Id Type (Fin (suc. n)) (Fin (suc. n)))
      (subtype_path_equiv Type isSet isset_isprop (standard_set (suc. n)) (standard_set (suc. n)))
      (refl (cycfin_set n) (cyclic_fin_generator n))
      (set_types_path (standard_set (suc. n)) (standard_set (suc. n)) (finite_fin_successor n))
      (forget_generator_type_path n)

def forget_generator (n : Nat)
  : Id (USym (symmetric_group (suc. n))) (refl (cycle_forget_set n) (cyclic_fin_generator n)) (finite_successor_symmetry n)
  ≔ equivalence_injective (USym (symmetric_group (suc. n))) (Id SetTypes (standard_set (suc. n)) (standard_set (suc. n)))
      (component_path_equiv SetTypes (standard_set (suc. n)) (shape (symmetric_group (suc. n))) (shape (symmetric_group (suc. n))))
      (refl (cycle_forget_set n) (cyclic_fin_generator n)) (finite_successor_symmetry n)
      (forget_generator_set_path n)

def forget_hom_generator (n : Nat)
  : Id (USym (symmetric_group (suc. n)))
      (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) (cyclic_fin_generator n))
      (finite_successor_symmetry n)
  ≔ concat (USym (symmetric_group (suc. n)))
      (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) (cyclic_fin_generator n))
      (refl (cycle_forget_set n) (cyclic_fin_generator n)) (finite_successor_symmetry n)
      (loop_conjugate_at_refl (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n)))
        (refl (cycle_forget_set n) (cyclic_fin_generator n)))
      (forget_generator n)

{` ex:groups-morphisms (4) and ex:Cm: R_m = prj ∘ mod_m as pointed maps,
   i.e. the homomorphism Z → Σ_m classified by R_m factors through C_m via mod_m. `}
def mod_forget_pointed (C : CircleSignature) (n : Nat) : BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n)))
  ≔ book_pointed_compose (circle_pointed C) (BG (cyclic_group_fin n)) (BG (symmetric_group (suc. n)))
      (mod_pointed C n) (cycle_forget_pointed n)

def mod_forget_factorization (C : CircleSignature) (n : Nat)
  : Id (BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n)))) (mod_forget_pointed C n) (power_finset_pointed C n)
  ≔ let M ≔ BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n))) in
    let L ≔ USym (symmetric_group (suc. n)) in
    let Ωf ≔ ((k ↦ loops_map (circle_pointed C) (BG (symmetric_group (suc. n))) k (C .loop)) : M → L) in
    equivalence_injective M L (pointed_circle_universal_property C (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))))
      (mod_forget_pointed C n) (power_finset_pointed C n)
      (calc
        Ωf (mod_forget_pointed C n)
        = loops_map (BG (cyclic_group_fin n)) (BG (symmetric_group (suc. n))) (cycle_forget_pointed n)
            (loops_map (circle_pointed C) (BG (cyclic_group_fin n)) (mod_pointed C n) (C .loop))
          by loops_map_compose_pointwise (circle_pointed C) (BG (cyclic_group_fin n)) (BG (symmetric_group (suc. n)))
            (mod_pointed C n) (cycle_forget_pointed n) (C .loop)
        = usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) (cyclic_fin_generator n)
          by refl (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n)) (mod_hom_loop C n)
        = finite_successor_symmetry n by forget_hom_generator n
        = Ωf (power_finset_pointed C n)
          by inverse L (Ωf (power_finset_pointed C n)) (finite_successor_symmetry n) (power_finset_loop C n) ∎)

def mod_forget_hom_factorization (C : CircleSignature) (n : Nat)
  : Id (GroupHom (circle_group C) (symmetric_group (suc. n)))
      (group_hom_compose (circle_group C) (cyclic_group_fin n) (symmetric_group (suc. n)) (mod_hom C n) (cyclic_forget_hom n))
      (power_finset_hom C n)
  ≔ (classifying_map ≔ mod_forget_factorization C n)

def mod_forget_map_factorization (C : CircleSignature) (n : Nat)
  : Id (C .carrier → BookFiniteSetsAt (suc. n))
      (compose (C .carrier) (CycFin n) (BookFiniteSetsAt (suc. n)) (cycle_forget_set n) (mod_map C n))
      (power_finset_map C n)
  ≔ refl ((k ↦ k .fst) : BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n))) → C .carrier → BookFiniteSetsAt (suc. n))
      (mod_forget_factorization C n)

{` mod_m is 0-connected: every symmetry of C_m is a power of the generator,
   which is the image of loop. `}
def mod_loops_surjective (C : CircleSignature) (n : Nat)
  : LoopsSurjective (C .carrier) (C .base) (CycFin n) (cycfin_point n) (mod_map C n) (mod_pointed C n .snd)
  ≔ q ↦ mere_rec (Σ Int (z ↦ Id (USym (cyclic_group_fin n)) (cycle_group_power (finite_fin_cycle n) z) q))
      (Mere (Σ (Id (C .carrier) (C .base) (C .base)) (l ↦ Id (USym (cyclic_group_fin n))
        (loops_map (circle_pointed C) (BG (cyclic_group_fin n)) (mod_pointed C n) l) q)))
      (mere_isprop (Σ (Id (C .carrier) (C .base) (C .base)) (l ↦ Id (USym (cyclic_group_fin n))
        (loops_map (circle_pointed C) (BG (cyclic_group_fin n)) (mod_pointed C n) l) q)))
      (w ↦ mere (Σ (Id (C .carrier) (C .base) (C .base)) (l ↦ Id (USym (cyclic_group_fin n))
          (loops_map (circle_pointed C) (BG (cyclic_group_fin n)) (mod_pointed C n) l) q))
        (loop_power (C .carrier) (C .base) (C .loop) (w .fst),
         calc
           loops_map (circle_pointed C) (BG (cyclic_group_fin n)) (mod_pointed C n)
             (loop_power (C .carrier) (C .base) (C .loop) (w .fst))
           = loop_power (CycFin n) (cycfin_point n)
               (loops_map (circle_pointed C) (BG (cyclic_group_fin n)) (mod_pointed C n) (C .loop)) (w .fst)
             by loops_map_power (circle_pointed C) (BG (cyclic_group_fin n)) (mod_pointed C n) (C .loop) (w .fst)
           = cycle_group_power (finite_fin_cycle n) (w .fst)
             by refl ((r ↦ loop_power (CycFin n) (cycfin_point n) r (w .fst)) : USym (cyclic_group_fin n) → USym (cyclic_group_fin n))
               (mod_hom_loop C n)
           = q by w .snd ∎))
      (cycle_group_symmetries_are_powers (finite_fin_cycle n) q)

def mod_connected_fibers (C : CircleSignature) (n : Nat) : ConnectedFibers (C .carrier) (CycFin n) (mod_map C n)
  ≔ connected_fibers_from_loops (C .carrier) (C .base) (native_circle_connected C) (CycFin n) (cycfin_point n)
      (native_component_connected Cycles (finite_fin_cycle n)) (mod_map C n) (mod_pointed C n .snd)
      (mod_loops_surjective C n)

{` ex:Cm. C'_m ≔ mkgroup(BC'_m, sh) with BC'_m ≔ Σ(X : FinSet_m) ‖R_m⁻¹(X)‖_0 the
   0-image of R_m (ZeroImage, module 106), pointed at (m, |(base, β)|_0), β
   the pointing path of R_m (the book: refl_m). It is connected (images of
   connected types) and a groupoid (its inclusion has set fibers). The
   construction is done for any pointed map k : BZ →* BΣ_m. `}
def circle_map_image_pcg (C : CircleSignature) (n : Nat) (k : BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n))))
  : PointedConnectedGroupoid
  ≔ (ZeroImage (C .carrier) (BookFiniteSetsAt (suc. n)) (k .fst),
     (shape (symmetric_group (suc. n)),
      set_trunc (BookFiber (C .carrier) (BookFiniteSetsAt (suc. n)) (k .fst) (shape (symmetric_group (suc. n)))) (C .base, k .snd)),
     zero_image_connected (C .carrier) (BookFiniteSetsAt (suc. n)) (k .fst) (native_circle_connected C),
     covering_domain_groupoid (ZeroImage (C .carrier) (BookFiniteSetsAt (suc. n)) (k .fst)) (BookFiniteSetsAt (suc. n))
       (zero_image_include (C .carrier) (BookFiniteSetsAt (suc. n)) (k .fst))
       (zero_image_include_covering (C .carrier) (BookFiniteSetsAt (suc. n)) (k .fst))
       (bg_groupoid (symmetric_group (suc. n))))

def circle_map_image_group (C : CircleSignature) (n : Nat) (k : BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n))))
  : Group ≔ mkgroup (circle_map_image_pcg C n k)

def cyclic_image_group (C : CircleSignature) (n : Nat) : Group ≔ circle_map_image_group C n (power_finset_pointed C n)

{` The induced pointed equivalence g : BC'_m ≃ BC_m. For the 0-image of
   prj ∘ mod_m it is explicit: ‖(prj ∘ mod_m)⁻¹(X)‖_0 ≃ prj⁻¹(X) since mod_m is
   0-connected and prj has set fibers (composite_truncated_fiber_equiv), and
   Σ_X prj⁻¹(X) ≃ Cyc_m; the base point goes to mod_m(base), which is
   identified with (m, s) by the pointing of mod_m. Then BC'_m is transported
   along R_m = prj ∘ mod_m. (Uniqueness of the induced equivalence is
   zero_image_universal_property: 0-image factorizations form a contractible type.) `}
def mod_forget_image_equiv (C : CircleSignature) (n : Nat)
  : Equiv (ZeroImage (C .carrier) (BookFiniteSetsAt (suc. n)) (mod_forget_pointed C n .fst)) (CycFin n)
  ≔ let F ≔ BookFiniteSetsAt (suc. n) in
    compose_equiv (ZeroImage (C .carrier) F (mod_forget_pointed C n .fst))
      (Σ F (X ↦ BookFiber (CycFin n) F (cycle_forget_set n) X)) (CycFin n)
      (family_equiv F (X ↦ SetTrunc (BookFiber (C .carrier) F (mod_forget_pointed C n .fst) X))
        (X ↦ BookFiber (CycFin n) F (cycle_forget_set n) X)
        (X ↦ composite_truncated_fiber_equiv (C .carrier) (CycFin n) F (mod_map C n) (mod_connected_fibers C n)
          (cycle_forget_set n) (cycle_forget_covering n) X))
      (sum_of_fibers_equiv (CycFin n) F (cycle_forget_set n))

def mod_forget_image_pointed_equiv (C : CircleSignature) (n : Nat)
  : BookPointedEquiv (BG (circle_map_image_group C n (mod_forget_pointed C n))) (BG (cyclic_group_fin n))
  ≔ ((mod_forget_image_equiv C n .map, mod_pointed C n .snd),
      book_equivalence (ZeroImage (C .carrier) (BookFiniteSetsAt (suc. n)) (mod_forget_pointed C n .fst)) (CycFin n)
        (mod_forget_image_equiv C n) .equiv)

def cyclic_image_path (C : CircleSignature) (n : Nat) : Id Group (cyclic_image_group C n) (cyclic_group_fin n)
  ≔ concat Group (cyclic_image_group C n) (circle_map_image_group C n (mod_forget_pointed C n)) (cyclic_group_fin n)
      (refl (circle_map_image_group C n) (inverse (BookPointedMap (circle_pointed C) (BG (symmetric_group (suc. n))))
        (mod_forget_pointed C n) (power_finset_pointed C n) (mod_forget_factorization C n)))
      (group_path_from_pointed_equiv (circle_map_image_group C n (mod_forget_pointed C n)) (cyclic_group_fin n)
        (mod_forget_image_pointed_equiv C n))

{` ex:Cm, last sentence: ‖R_m⁻¹(X)‖_0 is the set of cycle structures on X. `}
def power_fiber_cycle_structures (C : CircleSignature) (n : Nat) (X : BookFiniteSetsAt (suc. n))
  : Equiv (SetTrunc (BookFiber (C .carrier) (BookFiniteSetsAt (suc. n)) (power_finset_map C n) X)) (CycleStructuresOn n X)
  ≔ let F ≔ BookFiniteSetsAt (suc. n) in
    compose_equiv (SetTrunc (BookFiber (C .carrier) F (power_finset_map C n) X))
      (SetTrunc (BookFiber (C .carrier) F (compose (C .carrier) (CycFin n) F (cycle_forget_set n) (mod_map C n)) X))
      (CycleStructuresOn n X)
      (transport_equiv (SetTrunc (BookFiber (C .carrier) F (power_finset_map C n) X))
        (SetTrunc (BookFiber (C .carrier) F (compose (C .carrier) (CycFin n) F (cycle_forget_set n) (mod_map C n)) X))
        (refl ((f ↦ SetTrunc (BookFiber (C .carrier) F f X)) : (C .carrier → F) → Type)
          (inverse (C .carrier → F) (compose (C .carrier) (CycFin n) F (cycle_forget_set n) (mod_map C n))
            (power_finset_map C n) (mod_forget_map_factorization C n))))
      (compose_equiv (SetTrunc (BookFiber (C .carrier) F (compose (C .carrier) (CycFin n) F (cycle_forget_set n) (mod_map C n)) X))
        (BookFiber (CycFin n) F (cycle_forget_set n) X) (CycleStructuresOn n X)
        (composite_truncated_fiber_equiv (C .carrier) (CycFin n) F (mod_map C n) (mod_connected_fibers C n)
          (cycle_forget_set n) (cycle_forget_covering n) X)
        (cycle_forget_fiber_equiv n X))
