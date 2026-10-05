export "113-factorization-comparisons"
export "162-pointed-maps"
export "22-boolean-symmetry"

{` Chapter 9 (subgroups.tex 425-484): lem:fibersofcomposites, the running
   text after it, and xca:ptd-fibersofcomposites.

   Conventions: fibers are BookFiber (b = f a). For f1 : X0 → X1,
   f2 : X1 → X2, x1 : X1, x2 : X2, p2 : x2 = f2 x1, the book's composite
   path f2(p)p2 (first p2, then ap_{f2}(p)) is concat p2 (ap f2 p). A path
   (x1,p2) = (f1 x,q) in f2⁻¹(x2) is natively a pair (p, r) with
   r : Id (z ↦ x2 = f2 z) p p2 q a dependent path; the book's
   pathpair(p, r) with r : f2(p)p2 = q corresponds to it through
   pathover_mapped_paths_type (module 23). `}

{` F1 : (f2f1)⁻¹(x2) → f2⁻¹(x2), F1(x,q) ≔ (f1 x, q): this is
   composite_fiber_map of module 112. `}
def fibcomp_F1 (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x2 : X2)
  : BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2 → BookFiber X1 X2 f2 x2
  ≔ composite_fiber_map X0 X1 X2 f1 f2 x2

def fibcomp_F1_value (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x2 : X2)
  (w : BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2)
  : Id (BookFiber X1 X2 f2 x2) (fibcomp_F1 X0 X1 X2 f1 f2 x2 w) (f1 (w .fst), w .snd)
  ≔ refl (fibcomp_F1 X0 X1 X2 f1 f2 x2 w)

{` F2 : f1⁻¹(x1) → (f2f1)⁻¹(x2), F2(x,p) ≔ (x, f2(p)p2). `}
def fibcomp_F2 (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : BookFiber X0 X1 f1 x1 → BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2
  ≔ w ↦ (w .fst, concat X2 x2 (f2 x1) (f2 (f1 (w .fst))) p2 (map_path X1 X2 f2 x1 (f1 (w .fst)) (w .snd)))

{` The fiber F1⁻¹(x1,p2). `}
def FibcompF1Fiber (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1)) : Type
  ≔ BookFiber (BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2) (BookFiber X1 X2 f2 x2) (fibcomp_F1 X0 X1 X2 f1 f2 x2) (x1, p2)

{` H(x,q,pathpair(p,r)) ≔ (x,p). `}
def fibcomp_H (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2 → BookFiber X0 X1 f1 x1
  ≔ t ↦ (t .fst .fst, t .snd .fst)

{` The dependent path over p from p2 to f2(p)p2 (the book's
   pathpair(p, refl_{f2(p)p2})). `}
def fibcomp_pathover (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  (x : X0) (p : Id X1 x1 (f1 x))
  : Id (z ↦ Id X2 x2 (f2 z)) p p2 (concat X2 x2 (f2 x1) (f2 (f1 x)) p2 (map_path X1 X2 f2 x1 (f1 x) p))
  ≔ mapped_pathover_append X1 X2 f2 x2 x1 (f1 x) p p2

{` H⁻¹(x,p) ≔ ((x, f2(p)p2), pathpair(p, refl)). `}
def fibcomp_H_inv (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : BookFiber X0 X1 f1 x1 → FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2
  ≔ v ↦ ((v .fst, concat X2 x2 (f2 x1) (f2 (f1 (v .fst))) p2 (map_path X1 X2 f2 x1 (f1 (v .fst)) (v .snd))),
         (v .snd, fibcomp_pathover X0 X1 X2 f1 f2 x1 x2 p2 (v .fst) (v .snd)))

{` Dependent paths out of a fixed point form a contractible type. `}
def ch9w2_pathover_from_contractible (B : Type) (P : B → Type) (b c : B) (q : Id B b c) (u : P b)
  : isContr (Σ (P c) (v ↦ Id P q u v))
  ≔ J B b (c q ↦ isContr (Σ (P c) (v ↦ Id P q u v))) (iscontr_idfrom (P b) u) c q

{` "H contracts away q": for fixed x and p the pairs (q, r) form a
   contractible type. `}
def fibcomp_contract_type (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  (x : X0) (p : Id X1 x1 (f1 x)) : Type
  ≔ Σ (Id X2 x2 (f2 (f1 x))) (q ↦ Id (z ↦ Id X2 x2 (f2 z)) p p2 q)

def fibcomp_contract_prop (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  (x : X0) (p : Id X1 x1 (f1 x)) : isProp (fibcomp_contract_type X0 X1 X2 f1 f2 x1 x2 p2 x p)
  ≔ contractible_prop (fibcomp_contract_type X0 X1 X2 f1 f2 x1 x2 p2 x p)
      (ch9w2_pathover_from_contractible X1 (z ↦ Id X2 x2 (f2 z)) x1 (f1 x) p p2)

def fibcomp_H_inv_H (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  (t : FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2)
  : Id (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2)
      (fibcomp_H_inv X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2 t)) t
  ≔ let x ≔ t .fst .fst in let p ≔ t .snd .fst in
    let S ≔ fibcomp_contract_type X0 X1 X2 f1 f2 x1 x2 p2 x p in
    let m : S → FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2 ≔ s ↦ ((x, s .fst), (p, s .snd)) in
    refl m (fibcomp_contract_prop X0 X1 X2 f1 f2 x1 x2 p2 x p
      (concat X2 x2 (f2 x1) (f2 (f1 x)) p2 (map_path X1 X2 f2 x1 (f1 x) p), fibcomp_pathover X0 X1 X2 f1 f2 x1 x2 p2 x p)
      (t .fst .snd, t .snd .snd))

{` lem:fibersofcomposites (1): H is an equivalence with the printed inverse
   (H ∘ H⁻¹ = id holds judgmentally). `}
def fibcomp_H_equiv (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : Equiv (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2) (BookFiber X0 X1 f1 x1)
  ≔ quasi_inverse_equiv (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2) (BookFiber X0 X1 f1 x1)
      (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2) (fibcomp_H_inv X0 X1 X2 f1 f2 x1 x2 p2)
      (fibcomp_H_inv_H X0 X1 X2 f1 f2 x1 x2 p2) (v ↦ refl v)

def fibcomp_H_H_inv (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  (v : BookFiber X0 X1 f1 x1)
  : Id (BookFiber X0 X1 f1 x1) (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H_inv X0 X1 X2 f1 f2 x1 x2 p2 v)) v
  ≔ refl v

def fibcomp_H_book_equiv (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : BookEquiv (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2) (BookFiber X0 X1 f1 x1)
  ≔ book_equivalence (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2) (BookFiber X0 X1 f1 x1)
      (fibcomp_H_equiv X0 X1 X2 f1 f2 x1 x2 p2)

{` lem:fibersofcomposites (2): the lower square and its adjacent triangles
   commute by definition: f1 ∘ fst ≡ fst ∘ F1, fst ∘ F2 ≡ fst, and
   id ∘ (f2 f1) ≡ f2 ∘ f1. `}
def fibcomp_lower_square (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x2 : X2)
  : Id (BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2 → X1)
      (w ↦ f1 (w .fst)) (w ↦ fibcomp_F1 X0 X1 X2 f1 f2 x2 w .fst)
  ≔ refl ((w ↦ f1 (w .fst)) : BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2 → X1)

def fibcomp_right_triangle (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : Id (BookFiber X0 X1 f1 x1 → X0) (w ↦ fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 w .fst) (w ↦ w .fst)
  ≔ refl ((w ↦ w .fst) : BookFiber X0 X1 f1 x1 → X0)

def fibcomp_right_square (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2)
  : Id (X0 → X2) (x ↦ identity X2 (compose X0 X1 X2 f2 f1 x)) (x ↦ f2 (f1 x))
  ≔ refl ((x ↦ f2 (f1 x)) : X0 → X2)

{` lem:fibersofcomposites (3): the upper-left triangle F2 ∘ H = fst. At
   t = (x, q, pathpair(p, r)) the two pairs (x, f2(p)p2) and (x, q) are
   identified through r (here through the contraction of the pairs (q, r)
   of fibcomp_contract_type). `}
def fibcomp_triangle_point (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  (t : FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2)
  : Id (BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2)
      (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2 t)) (t .fst)
  ≔ let x ≔ t .fst .fst in let p ≔ t .snd .fst in
    let S ≔ fibcomp_contract_type X0 X1 X2 f1 f2 x1 x2 p2 x p in
    let m : S → BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2 ≔ s ↦ (x, s .fst) in
    refl m (fibcomp_contract_prop X0 X1 X2 f1 f2 x1 x2 p2 x p
      (concat X2 x2 (f2 x1) (f2 (f1 x)) p2 (map_path X1 X2 f2 x1 (f1 x) p), fibcomp_pathover X0 X1 X2 f1 f2 x1 x2 p2 x p)
      (t .fst .snd, t .snd .snd))

def fibcomp_upper_triangle (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : Id (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2 → BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2)
      (t ↦ fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2 t)) (t ↦ t .fst)
  ≔ funext (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2) (_ ↦ BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2)
      (t ↦ fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2 t)) (t ↦ t .fst)
      (fibcomp_triangle_point X0 X1 X2 f1 f2 x1 x2 p2)

{` The book's form of the identification: r turns into r' : f2(p)p2 = q
   (pathover_mapped_paths_type), and (refl_x, r') : (x, f2(p)p2) = (x, q). `}
def fibcomp_triangle_point_printed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  (t : FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2)
  : Id (BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2)
      (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2 t)) (t .fst)
  ≔ let x ≔ t .fst .fst in let p ≔ t .snd .fst in
    (refl x, transport Type (Z ↦ Z) (Id (z ↦ Id X2 x2 (f2 z)) p p2 (t .fst .snd))
        (Id (Id X2 x2 (f2 (f1 x))) (concat X2 x2 (f2 x1) (f2 (f1 x)) p2 (map_path X1 X2 f2 x1 (f1 x) p)) (t .fst .snd))
        (pathover_mapped_paths_type X1 X2 f2 x2 x1 (f1 x) p p2 (t .fst .snd)) (t .snd .snd))

{` Running text: through univalence, H gives an identification
   (F1⁻¹(x1,p2), fst) = (f1⁻¹(x1), F2) in Σ_{X:U} (X → (f2f1)⁻¹(x2)).
   First a general principle: an equivalence e : X ≃ Y with u = v ∘ e
   gives (X, u) = (Y, v) (equivalence induction). `}
def ch9w2_slice_path (X T : Type) (u : X → T) (Y : Type) (e : Equiv X Y) (v : Y → T)
  (h : Id (X → T) u (compose X Y T v (e .map)))
  : Id (Σ Type (Z ↦ Z → T)) (X, u) (Y, v)
  ≔ equivalence_induction X
      (Y e ↦ (v : Y → T) → Id (X → T) u (compose X Y T v (e .map)) → Id (Σ Type (Z ↦ Z → T)) (X, u) (Y, v))
      (v h ↦ refl ((w ↦ (X, w)) : (X → T) → Σ Type (Z ↦ Z → T)) h) Y e v h

def fibcomp_slice_path (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : Id (Σ Type (Z ↦ Z → BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2))
      (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2, (t ↦ t .fst))
      (BookFiber X0 X1 f1 x1, fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2)
  ≔ let T ≔ BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2 in
    let A ≔ FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2 in
    ch9w2_slice_path A T (t ↦ t .fst) (BookFiber X0 X1 f1 x1) (fibcomp_H_equiv X0 X1 X2 f1 f2 x1 x2 p2)
      (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2)
      (inverse (A → T) (t ↦ fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2 t)) (t ↦ t .fst)
        (fibcomp_upper_triangle X0 X1 X2 f1 f2 x1 x2 p2))

{` Running text: "F2 is the unique map such that fst ∘ F2 = fst, and H⁻¹ is
   similarly unique with fst ∘ H⁻¹ = F2" (universal property of the
   pullback). As printed this is false: a map g into a fiber BookFiber A B f b
   with fst ∘ g = k is determined by k together with its path component,
   and the maps over k form the type Π_c (b = f(k c)), which need not be a
   proposition. Corrected statement (the universal property of the fiber as
   a pullback): `}
def ch9w2_maps_over_choice (C A B : Type) (f : A → B) (b : B)
  : Equiv (C → BookFiber A B f b) (Σ (C → A) (h ↦ (c : C) → Id B b (f (h c))))
  ≔ choice_equiv C (_ ↦ A) (_ a ↦ Id B b (f a))

def ch9w2_maps_over_regroup (C A B : Type) (f : A → B) (b : B) (k : C → A)
  : Equiv (Σ (Σ (C → A) (h ↦ (c : C) → Id B b (f (h c)))) (u ↦ Id (C → A) k (u .fst)))
      (Σ (C → A) (h ↦ Product (Id (C → A) k h) ((c : C) → Id B b (f (h c)))))
  ≔ quasi_inverse_equiv (Σ (Σ (C → A) (h ↦ (c : C) → Id B b (f (h c)))) (u ↦ Id (C → A) k (u .fst)))
      (Σ (C → A) (h ↦ Product (Id (C → A) k h) ((c : C) → Id B b (f (h c)))))
      (u ↦ (u .fst .fst, (u .snd, u .fst .snd))) (u ↦ ((u .fst, u .snd .snd), u .snd .fst))
      (u ↦ refl u) (u ↦ refl u)

def fiber_maps_over_equiv (C A B : Type) (f : A → B) (b : B) (k : C → A)
  : Equiv (Σ (C → BookFiber A B f b) (g ↦ Id (C → A) k (c ↦ g c .fst))) ((c : C) → Id B b (f (k c)))
  ≔ let M ≔ Σ (C → A) (h ↦ (c : C) → Id B b (f (h c))) in
    compose_equiv (Σ (C → BookFiber A B f b) (g ↦ Id (C → A) k (c ↦ g c .fst)))
      (Σ M (u ↦ Id (C → A) k (u .fst))) ((c : C) → Id B b (f (k c)))
      (sigma_pullback_equiv (C → BookFiber A B f b) M (ch9w2_maps_over_choice C A B f b) (u ↦ Id (C → A) k (u .fst)))
      (compose_equiv (Σ M (u ↦ Id (C → A) k (u .fst)))
        (Σ (C → A) (h ↦ Product (Id (C → A) k h) ((c : C) → Id B b (f (h c)))))
        ((c : C) → Id B b (f (k c)))
        (ch9w2_maps_over_regroup C A B f b k)
        (contract_away_simple (C → A) k (h ↦ (c : C) → Id B b (f (h c)))))

{` Hence F2 is the unique map over fst whose path component is
   (x,p) ↦ f2(p)p2, and H⁻¹ the unique map over F2 whose path component is
   (x,p) ↦ pathpair(p, refl): the type of maps over fst (resp. over F2) is
   the stated Π-type, of which these path components are elements. `}
def fibcomp_F2_maps_over_equiv (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2)
  : Equiv (Σ (BookFiber X0 X1 f1 x1 → BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2)
        (g ↦ Id (BookFiber X0 X1 f1 x1 → X0) (w ↦ w .fst) (c ↦ g c .fst)))
      ((c : BookFiber X0 X1 f1 x1) → Id X2 x2 (f2 (f1 (c .fst))))
  ≔ fiber_maps_over_equiv (BookFiber X0 X1 f1 x1) X0 X2 (compose X0 X1 X2 f2 f1) x2 (w ↦ w .fst)

def fibcomp_H_inv_maps_over_equiv (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : Equiv (Σ (BookFiber X0 X1 f1 x1 → FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2)
        (g ↦ Id (BookFiber X0 X1 f1 x1 → BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2)
          (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2) (c ↦ g c .fst)))
      ((c : BookFiber X0 X1 f1 x1) → Id (BookFiber X1 X2 f2 x2) (x1, p2)
        (fibcomp_F1 X0 X1 X2 f1 f2 x2 (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 c)))
  ≔ fiber_maps_over_equiv (BookFiber X0 X1 f1 x1) (BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2)
      (BookFiber X1 X2 f2 x2) (fibcomp_F1 X0 X1 X2 f1 f2 x2) (x1, p2) (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2)

{` Counterexample to the printed uniqueness of F2: X0 = X1 = 1, X2 = U,
   f2 constant at Bool, x2 = Bool, p2 = refl. The map g(x,p) ≔ (x, swap)
   satisfies fst ∘ g ≡ fst but differs from F2 (swap ≠ refl in Bool = Bool). `}
def fibcomp_counter_g
  : BookFiber Unit Unit (identity Unit) star. → BookFiber Unit Type (compose Unit Unit Type (_ ↦ Bool) (identity Unit)) Bool
  ≔ w ↦ (w .fst, bool_swap)

def fibcomp_counter_over
  : Id (BookFiber Unit Unit (identity Unit) star. → Unit) (w ↦ w .fst) (w ↦ fibcomp_counter_g w .fst)
  ≔ refl ((w ↦ w .fst) : BookFiber Unit Unit (identity Unit) star. → Unit)

def fibcomp_F2_not_unique
  (e : Id (BookFiber Unit Unit (identity Unit) star. → BookFiber Unit Type (compose Unit Unit Type (_ ↦ Bool) (identity Unit)) Bool)
    (fibcomp_F2 Unit Unit Type (identity Unit) (_ ↦ Bool) star. Bool (refl Bool)) fibcomp_counter_g)
  : Empty
  ≔ let w0 : BookFiber Unit Unit (identity Unit) star. ≔ (star., refl star.) in
    let e0 : Id (Id Type Bool Bool) (concat Type Bool Bool Bool (refl Bool) (refl Bool)) bool_swap
      ≔ refl ((g ↦ g w0 .snd) : (BookFiber Unit Unit (identity Unit) star. → BookFiber Unit Type (compose Unit Unit Type (_ ↦ Bool) (identity Unit)) Bool) → Id Type Bool Bool) e in
    bool_swap_nontrivial
      (inverse (Id Type Bool Bool) (refl Bool) bool_swap
        (concat (Id Type Bool Bool) (refl Bool) (concat Type Bool Bool Bool (refl Bool) (refl Bool)) bool_swap
          (inverse (Id Type Bool Bool) (concat Type Bool Bool Bool (refl Bool) (refl Bool)) (refl Bool) (concat_1p Type Bool Bool (refl Bool)))
          e0))

{` xca:ptd-fibersofcomposites: the diagram with all maps pointed. Points:
   x0 : X0, x1, x2 with p1 : x1 = f1 x0, p2 : x2 = f2 x1; the fibers are
   pointed at (x0, f2(p1)p2), (x0, p1), (x1, p2) and H⁻¹(x0, p1). `}
def fibcomp_pt_comp (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1)) : Pointed
  ≔ (BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2, fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1))

def fibcomp_pt_fib1 (X0 X1 : Type) (f1 : X0 → X1) (x0 : X0) (x1 : X1) (p1 : Id X1 x1 (f1 x0)) : Pointed
  ≔ (BookFiber X0 X1 f1 x1, (x0, p1))

def fibcomp_pt_fib2 (X1 X2 : Type) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1)) : Pointed
  ≔ (BookFiber X1 X2 f2 x2, (x1, p2))

def fibcomp_pt_fibF1 (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1)) : Pointed
  ≔ (FibcompF1Fiber X0 X1 X2 f1 f2 x1 x2 p2, fibcomp_H_inv X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1))

def fibcomp_F1_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : BookPointedMap (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_pt_fib2 X1 X2 f2 x1 x2 p2)
  ≔ (fibcomp_F1 X0 X1 X2 f1 f2 x2, (p1, fibcomp_pathover X0 X1 X2 f1 f2 x1 x2 p2 x0 p1))

def fibcomp_F2_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : BookPointedMap (fibcomp_pt_fib1 X0 X1 f1 x0 x1 p1) (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2)
  ≔ (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2, refl (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1)))

def fibcomp_H_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : BookPointedMap (fibcomp_pt_fibF1 X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_pt_fib1 X0 X1 f1 x0 x1 p1)
  ≔ (fibcomp_H X0 X1 X2 f1 f2 x1 x2 p2, refl ((x0, p1) : BookFiber X0 X1 f1 x1))

def fibcomp_H_pointed_equiv (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : BookPointedEquiv (fibcomp_pt_fibF1 X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_pt_fib1 X0 X1 f1 x0 x1 p1)
  ≔ (fibcomp_H_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2, fibcomp_H_book_equiv X0 X1 X2 f1 f2 x1 x2 p2 .equiv)

def fibcomp_fst_comp_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : BookPointedMap (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (X0, x0)
  ≔ ((w ↦ w .fst), refl x0)

def fibcomp_fst_fib1_pointed (X0 X1 : Type) (f1 : X0 → X1) (x0 : X0) (x1 : X1) (p1 : Id X1 x1 (f1 x0))
  : BookPointedMap (fibcomp_pt_fib1 X0 X1 f1 x0 x1 p1) (X0, x0)
  ≔ ((w ↦ w .fst), refl x0)

def fibcomp_fst_fib2_pointed (X1 X2 : Type) (f2 : X1 → X2) (x1 : X1) (x2 : X2) (p2 : Id X2 x2 (f2 x1))
  : BookPointedMap (fibcomp_pt_fib2 X1 X2 f2 x1 x2 p2) (X1, x1)
  ≔ ((w ↦ w .fst), refl x1)

def fibcomp_fst_fibF1_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : BookPointedMap (fibcomp_pt_fibF1 X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2)
  ≔ ((t ↦ t .fst), refl (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1)))

{` Lower square, pointed: fst ∘ F1 = f1 ∘ fst as pointed maps. The
   pointings are refl·p1 and p1·refl. `}
def fibcomp_lower_square_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : PointedHomotopy (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (X1, x1)
      (book_pointed_compose (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_pt_fib2 X1 X2 f2 x1 x2 p2) (X1, x1)
        (fibcomp_F1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_fst_fib2_pointed X1 X2 f2 x1 x2 p2))
      (book_pointed_compose (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (X0, x0) (X1, x1)
        (fibcomp_fst_comp_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (f1, p1))
  ≔ ((w ↦ refl (f1 (w .fst))),
     calc
       concat X1 x1 (f1 x0) (f1 x0) (concat X1 x1 x1 (f1 x0) (refl x1) p1) (refl (f1 x0))
       = concat X1 x1 x1 (f1 x0) (refl x1) p1 by concat_p1 X1 x1 (f1 x0) (concat X1 x1 x1 (f1 x0) (refl x1) p1)
       = p1 by concat_1p X1 x1 (f1 x0) p1
       = concat X1 x1 (f1 x0) (f1 x0) p1 (refl (f1 x0))
         by inverse (Id X1 x1 (f1 x0)) (concat X1 x1 (f1 x0) (f1 x0) p1 (refl (f1 x0))) p1 (concat_p1 X1 x1 (f1 x0) p1) ∎)

{` Upper-right triangle, pointed: fst ∘ F2 = fst. `}
def fibcomp_right_triangle_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : PointedHomotopy (fibcomp_pt_fib1 X0 X1 f1 x0 x1 p1) (X0, x0)
      (book_pointed_compose (fibcomp_pt_fib1 X0 X1 f1 x0 x1 p1) (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (X0, x0)
        (fibcomp_F2_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_fst_comp_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
      (fibcomp_fst_fib1_pointed X0 X1 f1 x0 x1 p1)
  ≔ ((w ↦ refl (w .fst)),
     calc
       concat X0 x0 x0 x0 (concat X0 x0 x0 x0 (refl x0) (refl x0)) (refl x0)
       = concat X0 x0 x0 x0 (refl x0) (refl x0) by concat_p1 X0 x0 x0 (concat X0 x0 x0 x0 (refl x0) (refl x0))
       = refl x0 by concat_1p X0 x0 x0 (refl x0) ∎)

{` Upper-left triangle, pointed: F2 ∘ H = fst. At the base point the
   homotopy is the image of a loop in a contractible type, hence trivial. `}
def fibcomp_triangle_point_base (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : Id (Id (BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2) (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1))
        (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1)))
      (fibcomp_triangle_point X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H_inv X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1)))
      (refl (fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1)))
  ≔ let S ≔ fibcomp_contract_type X0 X1 X2 f1 f2 x1 x2 p2 x0 p1 in
    let s0 : S ≔ (concat X2 x2 (f2 x1) (f2 (f1 x0)) p2 (map_path X1 X2 f2 x1 (f1 x0) p1), fibcomp_pathover X0 X1 X2 f1 f2 x1 x2 p2 x0 p1) in
    let m : S → BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2 ≔ s ↦ (x0, s .fst) in
    let hS ≔ fibcomp_contract_prop X0 X1 X2 f1 f2 x1 x2 p2 x0 p1 in
    refl (map_path S (BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2) m s0 s0)
      (prop_is_set S hS s0 s0 (hS s0 s0) (refl s0))

def fibcomp_upper_triangle_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : PointedHomotopy (fibcomp_pt_fibF1 X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2)
      (book_pointed_compose (fibcomp_pt_fibF1 X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_pt_fib1 X0 X1 f1 x0 x1 p1)
        (fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2)
        (fibcomp_H_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_F2_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
      (fibcomp_fst_fibF1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2)
  ≔ let T ≔ BookFiber X0 X2 (compose X0 X1 X2 f2 f1) x2 in
    let c ≔ fibcomp_F2 X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1) in
    (fibcomp_triangle_point X0 X1 X2 f1 f2 x1 x2 p2,
     calc
       concat T c c c (concat T c c c (refl c) (refl c))
         (fibcomp_triangle_point X0 X1 X2 f1 f2 x1 x2 p2 (fibcomp_H_inv X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1)))
       = concat T c c c (concat T c c c (refl c) (refl c)) (refl c)
         by refl (concat T c c c (concat T c c c (refl c) (refl c))) (fibcomp_triangle_point_base X0 X1 X2 f1 f2 x0 x1 x2 p1 p2)
       = concat T c c c (refl c) (refl c) by concat_p1 T c c (concat T c c c (refl c) (refl c))
       = refl c by concat_1p T c c (refl c) ∎)

{` Right column, pointed: id ∘ (f2 ∘ f1) = f2 ∘ f1 as pointed maps. `}
def fibcomp_right_square_pointed (X0 X1 X2 : Type) (f1 : X0 → X1) (f2 : X1 → X2) (x0 : X0) (x1 : X1) (x2 : X2)
  (p1 : Id X1 x1 (f1 x0)) (p2 : Id X2 x2 (f2 x1))
  : PointedHomotopy (X0, x0) (X2, x2)
      (book_pointed_compose (X0, x0) (X2, x2) (X2, x2)
        (book_pointed_compose (X0, x0) (X1, x1) (X2, x2) (f1, p1) (f2, p2)) (book_pointed_identity (X2, x2)))
      (book_pointed_compose (X0, x0) (X1, x1) (X2, x2) (f1, p1) (f2, p2))
  ≔ let q ≔ concat X2 x2 (f2 x1) (f2 (f1 x0)) p2 (map_path X1 X2 f2 x1 (f1 x0) p1) in
    ((x ↦ refl (f2 (f1 x))),
     calc
       concat X2 x2 (f2 (f1 x0)) (f2 (f1 x0)) (concat X2 x2 x2 (f2 (f1 x0)) (refl x2) q) (refl (f2 (f1 x0)))
       = concat X2 x2 x2 (f2 (f1 x0)) (refl x2) q by concat_p1 X2 x2 (f2 (f1 x0)) (concat X2 x2 x2 (f2 (f1 x0)) (refl x2) q)
       = q by concat_1p X2 x2 (f2 (f1 x0)) q ∎)
