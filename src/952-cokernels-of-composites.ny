export "951-kernels-of-composites"

{` Chapter 9 (subgroups.tex 486-660): cor:cokermaps, items 5 and 7, and the
   two footnote lemmas of its proof. `}

{` The set-truncation functor on maps, ‖F‖₀(|a|₀) ≡ |F a|₀. `}
def ch9w2_set_trunc_map (A B : Type) (F : A → B) : SetTrunc A → SetTrunc B
  ≔ set_trunc_rec A (SetTrunc B) (set_trunc_set B) (a ↦ set_trunc B (F a))

{` A map with connected fibers induces an equivalence of set truncations. `}
def ch9w2_set_trunc_map_equiv (A B : Type) (F : A → B) (hF : ConnectedFibers A B F)
  : Equiv (SetTrunc A) (SetTrunc B)
  ≔ let g ≔ connected_map_truncated_inverse A B F hF in
    let inv : SetTrunc B → SetTrunc A ≔ set_trunc_rec B (SetTrunc A) (set_trunc_set A) g in
    let m ≔ ch9w2_set_trunc_map A B F in
    quasi_inverse_equiv (SetTrunc A) (SetTrunc B) m inv
      (set_trunc_induction A (z ↦ Id (SetTrunc A) (inv (m z)) z)
        (z ↦ prop_is_set (Id (SetTrunc A) (inv (m z)) z) (set_trunc_set A (inv (m z)) z))
        (a ↦ connected_map_truncated_inverse_beta A B F hF a))
      (set_trunc_induction B (z ↦ Id (SetTrunc B) (m (inv z)) z)
        (z ↦ prop_is_set (Id (SetTrunc B) (m (inv z)) z) (set_trunc_set B (m (inv z)) z))
        (b ↦ mere_rec (BookFiber A B F b) (Id (SetTrunc B) (m (g b)) (set_trunc B b))
          (set_trunc_set B (m (g b)) (set_trunc B b))
          (w ↦ calc
            m (g b)
            = m (set_trunc A (w .fst))
              by refl m (connected_set_map_value_beta (BookFiber A B F b) (SetTrunc A) (hF b) (set_trunc_set A)
                   (v ↦ set_trunc A (v .fst)) w)
            = set_trunc B (F (w .fst)) by refl (set_trunc B (F (w .fst)))
            = set_trunc B b by refl (set_trunc B) (inverse B b (F (w .fst)) (w .snd)) ∎)
          (hF b .fst)))

{` Equivalences have connected (indeed contractible) fibers. `}
def ch9w2_equiv_connected_fibers (A B : Type) (e : Equiv A B) : ConnectedFibers A B (e .map)
  ≔ b ↦
    let c ≔ book_equivalence A B e .equiv b in
    (mere (BookFiber A B (e .map) b) (c .center),
     x y ↦ mere (Id (BookFiber A B (e .map) b) x y)
       (concat (BookFiber A B (e .map) b) x (c .center) y (inverse (BookFiber A B (e .map) b) (c .center) x (c .contract x))
         (c .contract y)))

def ch9w2_set_trunc_equiv (A B : Type) (e : Equiv A B) : Equiv (SetTrunc A) (SetTrunc B)
  ≔ ch9w2_set_trunc_map_equiv A B (e .map) (ch9w2_equiv_connected_fibers A B e)

{` cor:cokermaps (7). F1'(w) : (f2 f1)⁻¹(w) → f2⁻¹(w), (x,q) ↦ (f1 x, q)
   (the code of F1 with the points abstracted), and the map of G2-sets
   tot(‖F1'(-)‖₀) : Hom_{G2}(coker(f2 f1), coker(f2)). `}
def kc_F1_general (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) (w : BG G2 .carrier)
  : HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) w → HomFiber G1 G2 f2 w
  ≔ fibcomp_F1 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2) w

def kc_coker_hom (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GSetHom G2 (cokernel G0 G2 (kc_compose G0 G1 G2 f1 f2)) (cokernel G1 G2 f2)
  ≔ w ↦ ch9w2_set_trunc_map (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) w) (HomFiber G1 G2 f2 w)
      (kc_F1_general G0 G1 G2 f1 f2 w)

{` If f1 is an epimorphism (here: Bf1 has connected fibers, condition (3')
   of lem:epi-surj; the epi form is kc_coker_hom_equiv_of_epi when module
   934 is available), each F1'(w) has connected fibers (module 112), so
   tot(‖F1'‖₀) is an equivalence of G2-sets: precomposing with an
   epimorphism does not change the cokernel. `}
def kc_coker_hom_equiv (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (c : IsConnectedHom G0 G1 f1) (w : BG G2 .carrier)
  : Equiv (SetTrunc (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) w)) (SetTrunc (HomFiber G1 G2 f2 w))
  ≔ ch9w2_set_trunc_map_equiv (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) w) (HomFiber G1 G2 f2 w)
      (kc_F1_general G0 G1 G2 f1 f2 w)
      (composite_fiber_map_connected (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) c
        (hom_function G1 G2 f2) w)

def kc_coker_hom_is_equiv (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (c : IsConnectedHom G0 G1 f1) (w : BG G2 .carrier)
  : BookIsEquiv (SetTrunc (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) w)) (SetTrunc (HomFiber G1 G2 f2 w))
      (kc_coker_hom G0 G1 G2 f1 f2 w)
  ≔ book_equivalence (SetTrunc (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) w)) (SetTrunc (HomFiber G1 G2 f2 w))
      (kc_coker_hom_equiv G0 G1 G2 f1 f2 c w) .equiv

{` Hence coker(f2 f1) = coker(f2) as G2-sets. `}
def kc_coker_path (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) (c : IsConnectedHom G0 G1 f1)
  : Id (GSet G2) (cokernel G0 G2 (kc_compose G0 G1 G2 f1 f2)) (cokernel G1 G2 f2)
  ≔ gset_path_from_equivs G2 (cokernel G0 G2 (kc_compose G0 G1 G2 f1 f2)) (cokernel G1 G2 f2)
      (kc_coker_hom_equiv G0 G1 G2 f1 f2 c)

{` Footnote to (c) in the proof of (7): for P : ‖A‖₀ → Prop, the map
   e(|(a,p)|₀) ≔ (|a|₀, p) is an equivalence ‖Σ_{a:A} P(|a|₀)‖₀ ≃ Σ_{b:‖A‖₀} P(b). `}
def ch9w2_trunc_sigma_prop_map (A : Type) (P : SetTrunc A → Type) (hP : (b : SetTrunc A) → isProp (P b))
  : SetTrunc (Σ A (a ↦ P (set_trunc A a))) → Σ (SetTrunc A) P
  ≔ set_trunc_rec (Σ A (a ↦ P (set_trunc A a))) (Σ (SetTrunc A) P)
      (sigma_set (SetTrunc A) P (set_trunc_set A) (b ↦ prop_is_set (P b) (hP b)))
      (u ↦ (set_trunc A (u .fst), u .snd))

def ch9w2_trunc_sigma_prop_map_beta (A : Type) (P : SetTrunc A → Type) (hP : (b : SetTrunc A) → isProp (P b))
  (a : A) (p : P (set_trunc A a))
  : Id (Σ (SetTrunc A) P) (ch9w2_trunc_sigma_prop_map A P hP (set_trunc (Σ A (a ↦ P (set_trunc A a))) (a, p)))
      (set_trunc A a, p)
  ≔ refl ((set_trunc A a, p) : Σ (SetTrunc A) P)

def ch9w2_trunc_sigma_prop_equiv (A : Type) (P : SetTrunc A → Type) (hP : (b : SetTrunc A) → isProp (P b))
  : Equiv (SetTrunc (Σ A (a ↦ P (set_trunc A a)))) (Σ (SetTrunc A) P)
  ≔ let S ≔ Σ A (a ↦ P (set_trunc A a)) in
    let e ≔ ch9w2_trunc_sigma_prop_map A P hP in
    let hT : isSet (Σ (SetTrunc A) P) ≔ sigma_set (SetTrunc A) P (set_trunc_set A) (b ↦ prop_is_set (P b) (hP b)) in
    let inv0 : (b : SetTrunc A) → P b → SetTrunc S
      ≔ set_trunc_induction A (b ↦ P b → SetTrunc S) (b ↦ pi_set (P b) (_ ↦ SetTrunc S) (_ ↦ set_trunc_set S))
          (a p ↦ set_trunc S (a, p)) in
    let inv : Σ (SetTrunc A) P → SetTrunc S ≔ u ↦ inv0 (u .fst) (u .snd) in
    let inv_beta : (a : A) (p : P (set_trunc A a)) → Id (SetTrunc S) (inv0 (set_trunc A a) p) (set_trunc S (a, p))
      ≔ a p ↦ happly (P (set_trunc A a)) (_ ↦ SetTrunc S) (inv0 (set_trunc A a)) (q ↦ set_trunc S (a, q))
          (set_trunc_induction_beta A (b ↦ P b → SetTrunc S) (b ↦ pi_set (P b) (_ ↦ SetTrunc S) (_ ↦ set_trunc_set S))
            (a q ↦ set_trunc S (a, q)) a) p in
    quasi_inverse_equiv (SetTrunc S) (Σ (SetTrunc A) P) e inv
      (set_trunc_induction S (z ↦ Id (SetTrunc S) (inv (e z)) z)
        (z ↦ prop_is_set (Id (SetTrunc S) (inv (e z)) z) (set_trunc_set S (inv (e z)) z))
        (u ↦ inv_beta (u .fst) (u .snd)))
      (u ↦ set_trunc_induction A (b ↦ (p : P b) → Id (Σ (SetTrunc A) P) (e (inv (b, p))) (b, p))
          (b ↦ pi_set (P b) (p ↦ Id (Σ (SetTrunc A) P) (e (inv (b, p))) (b, p))
            (p ↦ prop_is_set (Id (Σ (SetTrunc A) P) (e (inv (b, p))) (b, p)) (hT (e (inv (b, p))) (b, p))))
          (a p ↦ refl e (inv_beta a p)) (u .fst) (u .snd))

{` Footnote to (e): if ‖Σ_{a:A} T(a)‖₀ is contractible, so is
   ‖Σ_{a:A} ‖T(a)‖‖₀. `}
def ch9w2_trunc_sigma_mere_contractible (A : Type) (T : A → Type)
  (h : BookIsContr (SetTrunc (Σ A T))) : BookIsContr (SetTrunc (Σ A (a ↦ Mere (T a))))
  ≔ let S ≔ Σ A T in let S' ≔ Σ A (a ↦ Mere (T a)) in
    let m : SetTrunc S → SetTrunc S'
      ≔ set_trunc_rec S (SetTrunc S') (set_trunc_set S') (u ↦ set_trunc S' (u .fst, mere (T (u .fst)) (u .snd))) in
    let pts : (u v : S) → Id (SetTrunc S') (set_trunc S' (u .fst, mere (T (u .fst)) (u .snd))) (set_trunc S' (v .fst, mere (T (v .fst)) (v .snd)))
      ≔ u v ↦ equiv_inverse_map (Id (SetTrunc S') (set_trunc S' (u .fst, mere (T (u .fst)) (u .snd))) (set_trunc S' (v .fst, mere (T (v .fst)) (v .snd))))
          (Mere (Id S' (u .fst, mere (T (u .fst)) (u .snd)) (v .fst, mere (T (v .fst)) (v .snd))))
          (set_trunc_paths S' (u .fst, mere (T (u .fst)) (u .snd)) (v .fst, mere (T (v .fst)) (v .snd)))
          (mere_rec (Id S u v) (Mere (Id S' (u .fst, mere (T (u .fst)) (u .snd)) (v .fst, mere (T (v .fst)) (v .snd))))
            (mere_isprop (Id S' (u .fst, mere (T (u .fst)) (u .snd)) (v .fst, mere (T (v .fst)) (v .snd))))
            (r ↦ mere (Id S' (u .fst, mere (T (u .fst)) (u .snd)) (v .fst, mere (T (v .fst)) (v .snd)))
              (refl ((t ↦ (t .fst, mere (T (t .fst)) (t .snd))) : S → S') r))
            (set_trunc_paths S u v .map
              (concat (SetTrunc S) (set_trunc S u) (h .center) (set_trunc S v)
                (inverse (SetTrunc S) (h .center) (set_trunc S u) (h .contract (set_trunc S u))) (h .contract (set_trunc S v))))) in
    let pts' : (a : A) (t : Mere (T a)) (v : S) → Id (SetTrunc S') (set_trunc S' (a, t)) (set_trunc S' (v .fst, mere (T (v .fst)) (v .snd)))
      ≔ a t v ↦ mere_rec (T a) (Id (SetTrunc S') (set_trunc S' (a, t)) (set_trunc S' (v .fst, mere (T (v .fst)) (v .snd))))
          (set_trunc_set S' (set_trunc S' (a, t)) (set_trunc S' (v .fst, mere (T (v .fst)) (v .snd))))
          (s ↦ concat (SetTrunc S') (set_trunc S' (a, t)) (set_trunc S' (a, mere (T a) s)) (set_trunc S' (v .fst, mere (T (v .fst)) (v .snd)))
            (refl ((r ↦ set_trunc S' (a, r)) : Mere (T a) → SetTrunc S') (mere_isprop (T a) t (mere (T a) s)))
            (pts (a, s) v)) t in
    let c ≔ m (h .center) in
    let hc : (z : SetTrunc S') → Id (SetTrunc S') c z
      ≔ set_trunc_induction S' (z ↦ Id (SetTrunc S') c z)
          (z ↦ prop_is_set (Id (SetTrunc S') c z) (set_trunc_set S' c z))
          (u ↦ set_trunc_induction S (y ↦ Id (SetTrunc S') (m y) (set_trunc S' u))
              (y ↦ prop_is_set (Id (SetTrunc S') (m y) (set_trunc S' u)) (set_trunc_set S' (m y) (set_trunc S' u)))
              (v ↦ inverse (SetTrunc S') (set_trunc S' u) (set_trunc S' (v .fst, mere (T (v .fst)) (v .snd)))
                (pts' (u .fst) (u .snd) v))
              (h .center)) in
    (c, hc)
