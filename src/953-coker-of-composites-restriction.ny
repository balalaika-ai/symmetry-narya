export "952-cokernels-of-composites"

{` cor:cokermaps (5). For u : BKer(f2), H'(u) : BF1⁻¹(u) → Bf1⁻¹(fst u) has
   the code of H: H'(u)((c,!), e) ≔ (c.1, e.1.1). The printed claim
   coker(F1) = coker(f1) ∘ Bker(f2) is FALSE in general: BF1 is the map of
   components, so BF1⁻¹(sh) only contains the elements of F1⁻¹(x1,p2) whose
   first component lies in the component of the kernel shape of f2 f1, and
   the book's step "H'(sh) ≡ H" fails. Counterexample below (G0 = 1,
   G1 = G2 = Σ3, f2 = id). Corrected statement: if the fiber
   (Bf2f1)⁻¹(sh_G2) is connected (e.g. f2 f1 has connected fibers), H'(u)
   is an equivalence for every u and coker(F1) = coker(f1) ∘ Bker(f2). `}
def kc_H_prime (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) (u : BG (kernel_group G1 G2 f2) .carrier)
  (t : HomFiber (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2) u)
  : HomFiber G0 G1 f1 (hom_function (kernel_group G1 G2 f2) G1 (kernel_inclusion G1 G2 f2) u)
  ≔ (t .fst .fst .fst, t .snd .fst .fst)

def ch9w2_drop_contractible_prop (A : Type) (P : A → Type) (hP : (a : A) → isProp (P a)) (s : (a : A) → P a)
  : Equiv (Σ A P) A
  ≔ quasi_inverse_equiv (Σ A P) A (u ↦ u .fst) (a ↦ (a, s a))
      (u ↦ (refl (u .fst), hP (u .fst) (s (u .fst)) (u .snd))) (a ↦ refl a)

def kc_H_prime_equiv (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (hT : Connected (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2))) (u : BG (kernel_group G1 G2 f2) .carrier)
  : Equiv (HomFiber (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2) u)
      (HomFiber G0 G1 f1 (hom_function (kernel_group G1 G2 f2) G1 (kernel_inclusion G1 G2 f2) u))
  ≔ let X0 ≔ BG G0 .carrier in let X1 ≔ BG G1 .carrier in let X2 ≔ BG G2 .carrier in
    let Bf1 ≔ hom_function G0 G1 f1 in let Bf2 ≔ hom_function G1 G2 f2 in
    let T ≔ HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2) in
    let t0 ≔ kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let S ≔ HomFiber G1 G2 f2 (shape G2) in let s0 ≔ kernel_shape G1 G2 f2 in
    let F1 ≔ fibcomp_F1 X0 X1 X2 Bf1 Bf2 (shape G2) in
    let D ≔ HomFiber (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2) u in
    let W ≔ BookFiber T S F1 (u .fst) in
    compose_equiv D (Σ W (w ↦ Mere (Id T t0 (w .fst)))) (HomFiber G0 G1 f1 (u .fst .fst))
      (ch9w2_component_fiber_equiv T S F1 t0 s0 (kc_F1_point G0 G1 G2 f1 f2) u)
      (compose_equiv (Σ W (w ↦ Mere (Id T t0 (w .fst)))) W (HomFiber G0 G1 f1 (u .fst .fst))
        (ch9w2_drop_contractible_prop W (w ↦ Mere (Id T t0 (w .fst))) (w ↦ mere_isprop (Id T t0 (w .fst)))
          (w ↦ hT .snd t0 (w .fst)))
        (fibcomp_H_equiv X0 X1 X2 Bf1 Bf2 (u .fst .fst) (shape G2) (u .fst .snd)))

{` The underlying map of this equivalence is H'(u). `}
def kc_H_prime_equiv_map (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (hT : Connected (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2))) (u : BG (kernel_group G1 G2 f2) .carrier)
  (t : HomFiber (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2) u)
  : Id (HomFiber G0 G1 f1 (hom_function (kernel_group G1 G2 f2) G1 (kernel_inclusion G1 G2 f2) u))
      (kc_H_prime_equiv G0 G1 G2 f1 f2 hT u .map t) (kc_H_prime G0 G1 G2 f1 f2 u t)
  ≔ refl (kc_H_prime G0 G1 G2 f1 f2 u t)

def kc_coker_restriction_path (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (hT : Connected (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2)))
  : Id (GSet (kernel_group G1 G2 f2))
      (cokernel (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2))
      (gset_restrict (kernel_group G1 G2 f2) G1 (kernel_inclusion G1 G2 f2) (cokernel G0 G1 f1))
  ≔ let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in let K2 ≔ kernel_group G1 G2 f2 in
    gset_path_from_equivs K2 (cokernel K K2 (kc_F1 G0 G1 G2 f1 f2))
      (gset_restrict K2 G1 (kernel_inclusion G1 G2 f2) (cokernel G0 G1 f1))
      (u ↦ ch9w2_set_trunc_equiv (HomFiber K K2 (kc_F1 G0 G1 G2 f1 f2) u)
        (HomFiber G0 G1 f1 (hom_function K2 G1 (kernel_inclusion G1 G2 f2) u))
        (kc_H_prime_equiv G0 G1 G2 f1 f2 hT u))

{` The counterexample: G0 = 1, G1 = G2 = G with a nontrivial symmetry g
   (instance: Σ3 and τ), f1 the inclusion of 1, f2 = id. `}
def ch9w2_sigma3_tau_nontrivial
  (e : Id (USym (symmetric_group three)) (usym_unit (symmetric_group three)) sigma3_tau) : Empty
  ≔ let S ≔ symmetric_group three in let A ≔ BG S .carrier in let a ≔ shape S in
    sigma3_tau_sigma_noncommuting
      (calc
        usym_mul S sigma3_sigma sigma3_tau
        = usym_mul S sigma3_sigma (refl a)
          by refl (usym_mul S sigma3_sigma) (inverse (USym S) (refl a) sigma3_tau e)
        = sigma3_sigma by concat_1p A a a sigma3_sigma
        = usym_mul S (refl a) sigma3_sigma
          by inverse (USym S) (usym_mul S (refl a) sigma3_sigma) sigma3_sigma (concat_p1 A a a sigma3_sigma)
        = usym_mul S sigma3_tau sigma3_sigma
          by refl ((g ↦ usym_mul S g sigma3_sigma) : USym S → USym S) e ∎)

def ch9w2_set_trunc_prop (A : Type) (h : isProp A) : isProp (SetTrunc A)
  ≔ set_trunc_induction A (z ↦ (z' : SetTrunc A) → Id (SetTrunc A) z z')
      (z ↦ pi_set (SetTrunc A) (z' ↦ Id (SetTrunc A) z z') (z' ↦ prop_is_set (Id (SetTrunc A) z z') (set_trunc_set A z z')))
      (a ↦ set_trunc_induction A (z' ↦ Id (SetTrunc A) (set_trunc A a) z')
        (z' ↦ prop_is_set (Id (SetTrunc A) (set_trunc A a) z') (set_trunc_set A (set_trunc A a) z'))
        (b ↦ refl (set_trunc A) (h a b)))

def kc_counter_D_prop (G : Group)
  : isProp (HomFiber (kernel_group unit_group G (kc_compose unit_group G G (group_hom_from_unit G) (group_hom_id G)))
      (kernel_group G G (group_hom_id G)) (kc_F1 unit_group G G (group_hom_from_unit G) (group_hom_id G))
      (shape (kernel_group G G (group_hom_id G))))
  ≔ let X ≔ BG G .carrier in let x ≔ shape G in
    let f1 ≔ group_hom_from_unit G in let f2 ≔ group_hom_id G in
    let T ≔ HomFiber unit_group G (kc_compose unit_group G G f1 f2) x in
    let t0 ≔ kernel_shape unit_group G (kc_compose unit_group G G f1 f2) in
    let S ≔ HomFiber G G f2 x in let s0 ≔ kernel_shape G G f2 in
    let F1 ≔ fibcomp_F1 Unit X X (hom_function unit_group G f1) (hom_function G G f2) x in
    let W ≔ BookFiber T S F1 s0 in
    let P : W → Type ≔ w ↦ Mere (Id T t0 (w .fst)) in
    let hTset : isSet T ≔ sigma_set Unit (_ ↦ Id X x x) unit_set (_ ↦ bg_groupoid G x x) in
    let cS ≔ book_pathspace_contractible X x in
    let hS : isProp S ≔ s s' ↦ concat S s (cS .center) s' (inverse S (cS .center) s (cS .contract s)) (cS .contract s') in
    let hW : (u v : Σ W P) → Id W (u .fst) (v .fst)
      ≔ u v ↦ subtype_equal T (c ↦ Id S s0 (F1 c)) (c ↦ prop_is_set S hS s0 (F1 c)) (u .fst) (v .fst)
          (mere_rec (Id T t0 (u .fst .fst)) (Id T (u .fst .fst) (v .fst .fst)) (hTset (u .fst .fst) (v .fst .fst))
            (q ↦ mere_rec (Id T t0 (v .fst .fst)) (Id T (u .fst .fst) (v .fst .fst)) (hTset (u .fst .fst) (v .fst .fst))
              (q' ↦ concat T (u .fst .fst) t0 (v .fst .fst) (inverse T t0 (u .fst .fst) q) q') (v .snd)) (u .snd)) in
    let hSub : isProp (Σ W P) ≔ u v ↦ subtype_equal W P (w ↦ mere_isprop (Id T t0 (w .fst))) u v (hW u v) in
    let L ≔ ch9w2_component_fiber_equiv T S F1 t0 s0 (kc_F1_point unit_group G G f1 f2) (component_point S s0) in
    d d' ↦ equivalence_injective (HomFiber (kernel_group unit_group G (kc_compose unit_group G G f1 f2)) (kernel_group G G f2)
        (kc_F1 unit_group G G f1 f2) (shape (kernel_group G G f2))) (Σ W P) L d d' (hSub (L .map d) (L .map d'))

def KcCokerRestrictionClaim (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) : Type
  ≔ Id (GSet (kernel_group G1 G2 f2))
      (cokernel (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2))
      (gset_restrict (kernel_group G1 G2 f2) G1 (kernel_inclusion G1 G2 f2) (cokernel G0 G1 f1))

def kc_counter_D (G : Group) : Type
  ≔ HomFiber (kernel_group unit_group G (kc_compose unit_group G G (group_hom_from_unit G) (group_hom_id G)))
      (kernel_group G G (group_hom_id G)) (kc_F1 unit_group G G (group_hom_from_unit G) (group_hom_id G))
      (shape (kernel_group G G (group_hom_id G)))

def kc_counter_E (G : Group) : Type ≔ HomFiber unit_group G (group_hom_from_unit G) (shape G)

def kc_counter_equiv (G : Group) (p : KcCokerRestrictionClaim unit_group G G (group_hom_from_unit G) (group_hom_id G))
  : Equiv (SetTrunc (kc_counter_D G)) (SetTrunc (kc_counter_E G))
  ≔ let f1 ≔ group_hom_from_unit G in let f2 ≔ group_hom_id G in
    let K ≔ kernel_group unit_group G (kc_compose unit_group G G f1 f2) in let K2 ≔ kernel_group G G f2 in
    gset_path_equiv K2 (cokernel K K2 (kc_F1 unit_group G G f1 f2))
      (gset_restrict K2 G (kernel_inclusion G G f2) (cokernel unit_group G f1)) .map p (shape K2)

{` An equivalence from a proposition identifies any two elements. `}
def ch9w2_prop_equiv_paths (A B : Type) (hA : isProp A) (e : Equiv A B) (b b' : B) : Id B b b'
  ≔ let g ≔ equiv_inverse_map A B e in
    concat B b (e .map (g b')) b'
      (concat B b (e .map (g b)) (e .map (g b')) (inverse B (e .map (g b)) b (equiv_counit A B e b)) (refl (e .map) (hA (g b) (g b'))))
      (equiv_counit A B e b')

{` |(⋆, refl)|₀ ≠ |(⋆, g)|₀ in ‖Σ_{x:1} (sh = sh)‖₀ for g ≠ refl. `}
def ch9w2_unit_loops_trunc_distinct (X : Type) (x : X) (g : Id X x x) (ng : Id (Id X x x) (refl x) g → Empty)
  (e : Id (SetTrunc (Σ Unit (_ ↦ Id X x x))) (set_trunc (Σ Unit (_ ↦ Id X x x)) (star., refl x))
    (set_trunc (Σ Unit (_ ↦ Id X x x)) (star., g)))
  : Empty
  ≔ let E ≔ Σ Unit (_ ↦ Id X x x) in
    mere_rec (Id E (star., refl x) (star., g)) Empty (e0 e1 ↦ match e0 [])
      (r ↦ ng (refl ((v ↦ v .snd) : E → Id X x x) r))
      (set_trunc_paths E (star., refl x) (star., g) .map e)

def kc_coker_restriction_counterexample_general (G : Group) (g : USym G) (ng : Id (USym G) (usym_unit G) g → Empty)
  (p : KcCokerRestrictionClaim unit_group G G (group_hom_from_unit G) (group_hom_id G))
  : Empty
  ≔ ch9w2_unit_loops_trunc_distinct (BG G .carrier) (shape G) g ng
      (ch9w2_prop_equiv_paths (SetTrunc (kc_counter_D G)) (SetTrunc (kc_counter_E G))
        (ch9w2_set_trunc_prop (kc_counter_D G) (kc_counter_D_prop G)) (kc_counter_equiv G p)
        (set_trunc (kc_counter_E G) (star., refl (shape G))) (set_trunc (kc_counter_E G) (star., g)))

def kc_coker_restriction_counterexample
  (p : KcCokerRestrictionClaim unit_group (symmetric_group three) (symmetric_group three)
    (group_hom_from_unit (symmetric_group three)) (group_hom_id (symmetric_group three)))
  : Empty
  ≔ kc_coker_restriction_counterexample_general (symmetric_group three) sigma3_tau ch9w2_sigma3_tau_nontrivial p
