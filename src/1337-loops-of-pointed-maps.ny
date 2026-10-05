export "1335-swap-and-loops"

{` Chapter 13 (fields.tex 714-780), rem:grpHomOK: the pointed map
   Ω : (X →* Y) →* (ΩX →* ΩY) with the pointing path Ω_pt, the map Ω(Ω) and
   the square fig:ulrik relating it to ptw_* (rem:loops-at-ptd-cst) and path
   reversal i on Ω²Y. The square is filled in full generality (all pointed
   X, Y). Strategy: both composites land in ΩX →* Ω(ΩY), so only the
   underlying functions have to be identified (cor:Id-(B->*loopsA), as the
   book's TODO suggests). Pointwise, path induction on q (with free end
   point) expresses ap_{f ↦ Ω(f)(p)}(q) through the naturality of ptw_*(q)
   along p, which for constant maps is (ap_{ptw_*(q)}(p))⁻¹ up to
   conjugation; all remaining conjugations are removed with Eckmann-Hilton
   in Ω²Y. `}

{` Path algebra helpers. `}
def ulrik_group_cancel (T : Type) (r s : T) (X : Id T r s) (Y Y' : Id T s s) (Z : Id T s r)
  : Id (Id T r r)
      (concat T r r r (inverse T r r (concat T r s r X (concat T s s r Y Z))) (concat T r s r X (concat T s s r Y' Z)))
      (pointed_loop_conjugate T r s (inverse T s r Z) (concat T s s s (inverse T s s Y) Y'))
  ≔ let YZ ≔ concat T s s r Y Z in let Y'Z ≔ concat T s s r Y' Z in
    calc
      concat T r r r (inverse T r r (concat T r s r X YZ)) (concat T r s r X Y'Z)
        = concat T r r r (concat T r s r (inverse T s r YZ) (inverse T r s X)) (concat T r s r X Y'Z)
        by refl ((w ↦ concat T r r r w (concat T r s r X Y'Z)) : Id T r r → Id T r r) (inverse_concat T r s r X YZ)
      = concat T r s r (inverse T s r YZ) (concat T s r r (inverse T r s X) (concat T r s r X Y'Z))
        by concat_assoc T r s r r (inverse T s r YZ) (inverse T r s X) (concat T r s r X Y'Z)
      = concat T r s r (inverse T s r YZ) Y'Z
        by refl (concat T r s r (inverse T s r YZ)) (concat_left_inverse T r s r X Y'Z)
      = concat T r s r (concat T r s s (inverse T s r Z) (inverse T s s Y)) Y'Z
        by refl ((w ↦ concat T r s r w Y'Z) : Id T r s → Id T r r) (inverse_concat T s s r Y Z)
      = concat T r s r (inverse T s r Z) (concat T s s r (inverse T s s Y) Y'Z)
        by concat_assoc T r s s r (inverse T s r Z) (inverse T s s Y) Y'Z
      = concat T r s r (inverse T s r Z) (concat T s s r (concat T s s s (inverse T s s Y) Y') Z)
        by refl (concat T r s r (inverse T s r Z))
          (inverse (Id T s r) (concat T s s r (concat T s s s (inverse T s s Y) Y') Z) (concat T s s r (inverse T s s Y) Y'Z)
            (concat_assoc T s s s r (inverse T s s Y) Y' Z))
      = pointed_loop_conjugate T r s (inverse T s r Z) (concat T s s s (inverse T s s Y) Y')
        by refl ((w ↦ concat T r s r (inverse T s r Z) (concat T s s r (concat T s s s (inverse T s s Y) Y') w)) : Id T s r → Id T r r)
          (inverse (Id T s r) (inverse T r s (inverse T s r Z)) Z (inverse_inverse T s r Z)) ∎

{` ap preserves conjugation. `}
def ulrik_map_conjugate (A A' : Type) (F : A → A') (s t : A) (j : Id A s t) (x : Id A t t)
  : Id (Id A' (F s) (F s)) (refl F (pointed_loop_conjugate A s t j x))
      (pointed_loop_conjugate A' (F s) (F t) (refl F j) (refl F x))
  ≔ J A s (t j ↦ (x : Id A t t) → Id (Id A' (F s) (F s)) (refl F (pointed_loop_conjugate A s t j x))
        (pointed_loop_conjugate A' (F s) (F t) (refl F j) (refl F x)))
      (x ↦ calc
        refl F (pointed_loop_conjugate A s s (refl s) x) = refl F x
          by refl ((w ↦ refl F w) : Id A s s → Id A' (F s) (F s)) (loop_conjugate_at_refl A s x)
        = pointed_loop_conjugate A' (F s) (F s) (refl (F s)) (refl F x)
          by inverse (Id A' (F s) (F s)) (pointed_loop_conjugate A' (F s) (F s) (refl (F s)) (refl F x)) (refl F x)
            (loop_conjugate_at_refl A' (F s) (refl F x)) ∎)
      t j x

{` Eckmann-Hilton: in Ω²Y conjugation does not depend on the conjugating
   path: conj_j(x) = conj_{j'}(x) for j, j' : refl = t in Ω Y. `}
def ulrik_conjugate_independent (B : Type) (y : B) (t : Id B y y) (j j' : Id (Id B y y) (refl y) t) (x : Id (Id B y y) t t)
  : Id (Id (Id B y y) (refl y) (refl y))
      (pointed_loop_conjugate (Id B y y) (refl y) t j x) (pointed_loop_conjugate (Id B y y) (refl y) t j' x)
  ≔ let T ≔ Id B y y in let r ≔ refl y in
    J T r (t j' ↦ (j : Id T r t) (x : Id T t t)
        → Id (Id T r r) (pointed_loop_conjugate T r t j x) (pointed_loop_conjugate T r t j' x))
      (j x ↦ calc
        pointed_loop_conjugate T r r j x = concat T r r r j (concat T r r r (inverse T r r j) x)
          by refl (concat T r r r j) (eckmann_hilton B y x (inverse T r r j))
        = x by concat_left_right_inverse T r r r j x
        = pointed_loop_conjugate T r r (refl r) x
          by inverse (Id T r r) (pointed_loop_conjugate T r r (refl r) x) x (loop_conjugate_at_refl T r x) ∎)
      t j' j x

{` ΩY-level data for a pointed homotopy k from the constant map to g:
   R(g) ≔ Ω(g)(p) = g_pt·ap_g(p)·g_pt⁻¹ (concatenation order), and the
   explicit path F*(u, ℓ, gp, n, c) : Ω(cst)(p) = R(g) built from u = k(pt),
   ℓ = ap_g(p), the naturality n of k along p and the pointing c of k. `}
def ulrik_whisker (B : Type) (y b : B) (u : Id B y b) (w : Id B y b) : Id B y y
  ≔ concat B y b y w (inverse B y b (concat B y y b (refl y) u))

def ulrik_path (B : Type) (y b : B) (u : Id B y b) (l : Id B b b) (gp : Id B y b)
  (n : Id (Id B y b) (concat B y y b (refl y) u) (concat B y b b u l))
  (c : Id (Id B y b) (concat B y y b (refl y) u) gp)
  : Id (Id B y y) (pointed_loop_conjugate B y y (refl y) (refl y)) (pointed_loop_conjugate B y b gp l)
  ≔ let T ≔ Id B y y in let L ≔ Id B y b in
    let u1 ≔ concat B y y b (refl y) u in
    let H ≔ ulrik_whisker B y b u in
    let R0 ≔ pointed_loop_conjugate B y y (refl y) (refl y) in
    let J1 : Id T R0 (H u1)
      ≔ concat T R0 (refl y) (H u1) (loop_conjugate_unit B y y (refl y))
          (inverse T (H u1) (refl y) (concat_inverse_right B y b u1)) in
    let J2 : Id T (H (concat B y b b u l)) (pointed_loop_conjugate B y b gp l)
      ≔ concat T (H (concat B y b b u l)) (concat B y b y u (concat B b b y l (inverse B y b u1)))
          (pointed_loop_conjugate B y b gp l)
          (concat_assoc B y b b y u l (inverse B y b u1))
          (concat T (concat B y b y u (concat B b b y l (inverse B y b u1)))
            (concat B y b y u1 (concat B b b y l (inverse B y b u1))) (pointed_loop_conjugate B y b gp l)
            (refl ((r ↦ concat B y b y r (concat B b b y l (inverse B y b u1))) : L → T)
              (inverse L u1 u (concat_1p B y b u)))
            (refl ((r ↦ concat B y b y r (concat B b b y l (inverse B y b r))) : L → T) c)) in
    concat T R0 (H u1) (pointed_loop_conjugate B y b gp l) J1
      (concat T (H u1) (H (concat B y b b u l)) (pointed_loop_conjugate B y b gp l) (refl H n) J2)

{` Naturality of a homotopy k between constant maps along p, in terms of
   ap_k(p): n(k, p) = λ_{k x} · ap_k(p)⁻¹ · ρ_{k pt}⁻¹ (concatenation order). `}
def ulrik_constant_naturality (A B : Type) (y : B) (a : A) (k : (z : A) → Id B y y) (x : A) (p : Id A a x)
  : Id (Id (Id B y y) (concat B y y y (refl y) (k x)) (concat B y y y (k a) (refl y)))
      (naturality A B (constant A B y) (constant A B y) k a x p)
      (concat (Id B y y) (concat B y y y (refl y) (k x)) (k x) (concat B y y y (k a) (refl y))
        (concat_1p B y y (k x))
        (concat (Id B y y) (k x) (k a) (concat B y y y (k a) (refl y))
          (inverse (Id B y y) (k a) (k x) (refl k p)) (inverse (Id B y y) (concat B y y y (k a) (refl y)) (k a) (concat_p1 B y y (k a)))))
  ≔ let T ≔ Id B y y in
    J A a (x p ↦ Id (Id T (concat B y y y (refl y) (k x)) (concat B y y y (k a) (refl y)))
        (naturality A B (constant A B y) (constant A B y) k a x p)
        (concat T (concat B y y y (refl y) (k x)) (k x) (concat B y y y (k a) (refl y))
          (concat_1p B y y (k x))
          (concat T (k x) (k a) (concat B y y y (k a) (refl y))
            (inverse T (k a) (k x) (refl k p)) (inverse T (concat B y y y (k a) (refl y)) (k a) (concat_p1 B y y (k a))))))
      (let ka ≔ k a in let ρi ≔ inverse T (concat B y y y ka (refl y)) ka (concat_p1 B y y ka) in
       calc
         naturality A B (constant A B y) (constant A B y) k a a (refl a)
           = concat T (concat B y y y (refl y) ka) ka (concat B y y y ka (refl y)) (concat_1p B y y ka) ρi
           by inverse (Id T (concat B y y y (refl y) ka) (concat B y y y ka (refl y)))
             (concat T (concat B y y y (refl y) ka) ka (concat B y y y ka (refl y)) (concat_1p B y y ka) ρi)
             (naturality A B (constant A B y) (constant A B y) k a a (refl a))
             (Jβ A a (y' p' ↦ Id T (concat B y y y (refl (constant A B y) p') (k y')) (concat B y y y (k a) (refl (constant A B y) p')))
               (concat T (concat B y y y (refl y) ka) ka (concat B y y y ka (refl y)) (concat_1p B y y ka) ρi))
         = concat T (concat B y y y (refl y) ka) ka (concat B y y y ka (refl y)) (concat_1p B y y ka)
             (concat T ka ka (concat B y y y ka (refl y)) (refl ka) ρi)
           by refl (concat T (concat B y y y (refl y) ka) ka (concat B y y y ka (refl y)) (concat_1p B y y ka))
             (inverse (Id T ka (concat B y y y ka (refl y))) (concat T ka ka (concat B y y y ka (refl y)) (refl ka) ρi) ρi
               (concat_1p T ka (concat B y y y ka (refl y)) ρi))
         = concat T (concat B y y y (refl y) ka) ka (concat B y y y ka (refl y)) (concat_1p B y y ka)
             (concat T ka ka (concat B y y y ka (refl y)) (inverse T ka ka (refl ka)) ρi)
           by refl ((w ↦ concat T (concat B y y y (refl y) ka) ka (concat B y y y ka (refl y)) (concat_1p B y y ka)
                 (concat T ka ka (concat B y y y ka (refl y)) w ρi)) : Id T ka ka → Id (Id B y y) (concat B y y y (refl y) ka) (concat B y y y ka (refl y)))
             (inverse (Id T ka ka) (inverse T ka ka (refl ka)) (refl ka) (inverse_refl T ka)) ∎)
      x p

{` rem:grpHomOK: h(p) : refl = ap_cst(p)·refl for p : pt_X = x, by path
   induction (the book's h(refl) ≔ refl_refl; in Narya the endpoint is the
   conjugate refl⁻¹·ap_cst(p)·refl, so the base case is the unit law of
   conjugation). `}
def loops_constant_pointing (X Y : Pointed) (x : X .carrier) (p : Id (X .carrier) (X .point) x)
  : Id (Loop Y) (refl (Y .point))
      (pointed_loop_conjugate (Y .carrier) (Y .point) (Y .point) (refl (Y .point)) (refl (constant (X .carrier) (Y .carrier) (Y .point)) p))
  ≔ let B ≔ Y .carrier in let y ≔ Y .point in
    J (X .carrier) (X .point)
      (x p ↦ Id (Loop Y) (refl y) (pointed_loop_conjugate B y y (refl y) (refl (constant (X .carrier) B y) p)))
      (inverse (Loop Y) (pointed_loop_conjugate B y y (refl y) (refl y)) (refl y) (loop_conjugate_unit B y y (refl y)))
      x p

{` rem:grpHomOK: Ω_pt ≔ ptw_*⁻¹(h, ·) : cst_{ΩX→*ΩY} = Ω(cst_{X→*Y}); the
   book's pointing refl_refl_refl becomes the computation rule of h at refl. `}
def loops_functor_point (X Y : Pointed)
  : Id (BookPointedMap (Omega X) (Omega Y)) (book_pointed_constant (Omega X) (Omega Y))
      (loops_pointed_map X Y (book_pointed_constant X Y))
  ≔ let B ≔ Y .carrier in let y ≔ Y .point in let a ≔ X .point in
    let c0 ≔ book_pointed_constant (Omega X) (Omega Y) in
    let L ≔ loops_pointed_map X Y (book_pointed_constant X Y) in
    let hb ≔ inverse (Loop Y) (pointed_loop_conjugate B y y (refl y) (refl y)) (refl y) (loop_conjugate_unit B y y (refl y)) in
    let h ≔ loops_constant_pointing X Y a in
    equiv_inverse_map (Id (BookPointedMap (Omega X) (Omega Y)) c0 L) (PointedHomotopy (Omega X) (Omega Y) c0 L)
      (pointed_map_path_equiv (Omega X) (Omega Y) c0 L)
      (h,
       concat (Id (Loop Y) (refl y) (pointed_loop_conjugate B y y (refl y) (refl y)))
         (concat (Loop Y) (refl y) (refl y) (pointed_loop_conjugate B y y (refl y) (refl y)) (refl (refl y)) (h (refl a)))
         (h (refl a)) hb
         (concat_1p (Loop Y) (refl y) (pointed_loop_conjugate B y y (refl y) (refl y)) (h (refl a)))
         (inverse (Id (Loop Y) (refl y) (pointed_loop_conjugate B y y (refl y) (refl y))) hb (h (refl a))
           (Jβ (X .carrier) a
             (x p ↦ Id (Loop Y) (refl y) (pointed_loop_conjugate B y y (refl y) (refl (constant (X .carrier) B y) p))) hb)))

{` rem:grpHomOK: Ω as a pointed map (X →* Y) →* (ΩX →* ΩY), and
   Ω(Ω)(q) ≔ Ω_pt⁻¹ · ap_Ω(q) · Ω_pt (def:loops-map). `}
def loops_functor_pointed (X Y : Pointed)
  : BookPointedMap (pointed_maps_pointed X Y) (pointed_maps_pointed (Omega X) (Omega Y))
  ≔ (loops_pointed_map X Y, loops_functor_point X Y)

def loops_of_loops_functor (X Y : Pointed) (q : Loop (pointed_maps_pointed X Y))
  : Loop (pointed_maps_pointed (Omega X) (Omega Y))
  ≔ loops_map (pointed_maps_pointed X Y) (pointed_maps_pointed (Omega X) (Omega Y)) (loops_functor_pointed X Y) q

{` Path reversal i : Ω²Y →* Ω²Y. `}
def double_loop_inverse (Y : Pointed) : BookPointedMap (Omega (Omega Y)) (Omega (Omega Y))
  ≔ let r ≔ refl (Y .point) in
    ((w ↦ inverse (Loop Y) r r w),
     inverse (Id (Loop Y) r r) (inverse (Loop Y) r r (refl r)) (refl r) (inverse_refl (Loop Y) r))

{` The two composites of fig:ulrik, Ω(X →* Y) → (ΩX →* Ω(ΩY)). `}
def ulrik_left (X Y : Pointed) (q : Loop (pointed_maps_pointed X Y)) : BookPointedMap (Omega X) (Omega (Omega Y))
  ≔ constant_loops_pointed_equiv (Omega X) (Omega Y) .map (loops_of_loops_functor X Y q)

def ulrik_right (X Y : Pointed) (q : Loop (pointed_maps_pointed X Y)) : BookPointedMap (Omega X) (Omega (Omega Y))
  ≔ book_pointed_compose (Omega X) (Omega (Omega Y)) (Omega (Omega Y))
      (loops_pointed_map X (Omega Y) (constant_loops_pointed_equiv X Y .map q)) (double_loop_inverse Y)

{` Path induction on q : cst = g: ap_{f ↦ Ω(f)(p)}(q) = F_ref⁻¹ · F*(ptw_*(q)),
   where F* = ulrik_path and F_ref is its value at q = refl. `}
def ulrik_ap_loops (X Y : Pointed) (p : Loop X) (g : BookPointedMap X Y)
  (q : Id (BookPointedMap X Y) (book_pointed_constant X Y) g)
  : Id (Id (Loop Y) (loops_map X Y (book_pointed_constant X Y) p) (loops_map X Y g p))
      (refl ((f ↦ loops_map X Y f p) : BookPointedMap X Y → Loop Y) q)
      (concat (Loop Y) (loops_map X Y (book_pointed_constant X Y) p) (loops_map X Y (book_pointed_constant X Y) p)
        (loops_map X Y g p)
        (inverse (Loop Y) (loops_map X Y (book_pointed_constant X Y) p) (loops_map X Y (book_pointed_constant X Y) p)
          (ulrik_path (Y .carrier) (Y .point) (Y .point) (refl (Y .point)) (refl (Y .point)) (refl (Y .point))
            (naturality (X .carrier) (Y .carrier) (constant (X .carrier) (Y .carrier) (Y .point)) (constant (X .carrier) (Y .carrier) (Y .point))
              (_ ↦ refl (Y .point)) (X .point) (X .point) p)
            (pathover_transport_equiv (X .carrier → Y .carrier) (k ↦ Id (Y .carrier) (Y .point) (k (X .point)))
              (constant (X .carrier) (Y .carrier) (Y .point)) (constant (X .carrier) (Y .carrier) (Y .point))
              (refl (constant (X .carrier) (Y .carrier) (Y .point))) (refl (Y .point)) (refl (Y .point)) .map (refl (refl (Y .point))))))
        (ulrik_path (Y .carrier) (Y .point) (g .fst (X .point)) (q .fst (refl (X .point))) (refl (g .fst) p) (g .snd)
          (naturality (X .carrier) (Y .carrier) (constant (X .carrier) (Y .carrier) (Y .point)) (g .fst) (z ↦ q .fst (refl z))
            (X .point) (X .point) p)
          (pathover_transport_equiv (X .carrier → Y .carrier) (k ↦ Id (Y .carrier) (Y .point) (k (X .point)))
            (constant (X .carrier) (Y .carrier) (Y .point)) (g .fst) (q .fst) (refl (Y .point)) (g .snd) .map (q .snd))))
  ≔ let A ≔ X .carrier in let B ≔ Y .carrier in let y ≔ Y .point in let a ≔ X .point in
    let M ≔ BookPointedMap X Y in let cst ≔ book_pointed_constant X Y in
    let c0 ≔ constant A B y in
    let T' ≔ (k ↦ Id B y (k a)) : (A → B) → Type in
    let R ≔ (f ↦ loops_map X Y f p) : M → Loop Y in
    let Fs ≔ (g ↦ (q ↦ ulrik_path B y (g .fst a) (q .fst (refl a)) (refl (g .fst) p) (g .snd)
          (naturality A B c0 (g .fst) (z ↦ q .fst (refl z)) a a p)
          (pathover_transport_equiv (A → B) T' c0 (g .fst) (q .fst) (refl y) (g .snd) .map (q .snd))))
      : (g : M) → (q : Id M cst g) → Id (Loop Y) (R cst) (R g) in
    let Fref ≔ Fs cst (refl cst) in
    J M cst (g q ↦ Id (Id (Loop Y) (R cst) (R g)) (refl R q)
        (concat (Loop Y) (R cst) (R cst) (R g) (inverse (Loop Y) (R cst) (R cst) Fref) (Fs g q)))
      (inverse (Id (Loop Y) (R cst) (R cst)) (concat (Loop Y) (R cst) (R cst) (R cst) (inverse (Loop Y) (R cst) (R cst) Fref) Fref)
        (refl (R cst)) (concat_inverse_left (Loop Y) (R cst) (R cst) Fref))
      g q

{` The final computation in Ω²Y. For u = k(pt) : y = y, e : refl = u,
   m = ap_k(p) : u = u, c' : refl = u and ω : refl = Ω(cst)(p):
   conj_ω(F_ref⁻¹ · F*(u, n(u, m), λ_u·e⁻¹)) = (conj_{c'}(m))⁻¹, where n is
   the naturality of ulrik_constant_naturality. By path induction on e;
   then everything is a conjugate of m⁻¹ and Eckmann-Hilton removes the
   conjugating loops. `}
def ulrik_naturality_form (B : Type) (y : B) (u : Id B y y) (m : Id (Id B y y) u u)
  : Id (Id B y y) (concat B y y y (refl y) u) (concat B y y y u (refl y))
  ≔ concat (Id B y y) (concat B y y y (refl y) u) u (concat B y y y u (refl y))
      (concat_1p B y y u)
      (concat (Id B y y) u u (concat B y y y u (refl y)) (inverse (Id B y y) u u m)
        (inverse (Id B y y) (concat B y y y u (refl y)) u (concat_p1 B y y u)))

def ulrik_final (B : Type) (y : B) (u : Id B y y) (e : Id (Id B y y) (refl y) u) (m : Id (Id B y y) u u)
  (c' : Id (Id B y y) (refl y) u)
  (ω : Id (Id B y y) (refl y) (pointed_loop_conjugate B y y (refl y) (refl y)))
  : Id (Id (Id B y y) (refl y) (refl y))
      (pointed_loop_conjugate (Id B y y) (refl y) (pointed_loop_conjugate B y y (refl y) (refl y)) ω
        (concat (Id B y y) (pointed_loop_conjugate B y y (refl y) (refl y)) (pointed_loop_conjugate B y y (refl y) (refl y))
          (pointed_loop_conjugate B y y (refl y) (refl y))
          (inverse (Id B y y) (pointed_loop_conjugate B y y (refl y) (refl y)) (pointed_loop_conjugate B y y (refl y) (refl y))
            (ulrik_path B y y (refl y) (refl y) (refl y) (ulrik_naturality_form B y (refl y) (refl (refl y))) (concat_p1 B y y (refl y))))
          (ulrik_path B y y u (refl y) (refl y) (ulrik_naturality_form B y u m)
            (concat (Id B y y) (concat B y y y (refl y) u) u (refl y) (concat_1p B y y u) (inverse (Id B y y) (refl y) u e)))))
      (inverse (Id B y y) (refl y) (refl y) (pointed_loop_conjugate (Id B y y) (refl y) u c' m))
  ≔ let T ≔ Id B y y in let r ≔ refl y in
    let R0 ≔ pointed_loop_conjugate B y y r r in
    let P1 ≔ concat B y y y r r in
    let ρ0 ≔ concat_p1 B y y r in let λ0 ≔ concat_1p B y y r in
    J T r (u e ↦ (m : Id T u u) (c' : Id T r u) (ω : Id T r R0)
        → Id (Id T r r)
            (pointed_loop_conjugate T r R0 ω
              (concat T R0 R0 R0 (inverse T R0 R0 (ulrik_path B y y r r r (ulrik_naturality_form B y r (refl r)) ρ0))
                (ulrik_path B y y u r r (ulrik_naturality_form B y u m)
                  (concat T (concat B y y y r u) u r (concat_1p B y y u) (inverse T r u e)))))
            (inverse T r r (pointed_loop_conjugate T r u c' m)))
      (m c' ω ↦
        let H ≔ ulrik_whisker B y y r in
        let F ≔ (n c ↦ ulrik_path B y y r r r n c) : Id T P1 P1 → Id T P1 r → Id T R0 R0 in
        let n0 ≔ ulrik_naturality_form B y r (refl r) in
        let nm ≔ ulrik_naturality_form B y r m in
        let c0 ≔ concat T P1 r r λ0 (inverse T r r (refl r)) in
        let ec : Id (Id T P1 r) c0 ρ0
          ≔ calc
              c0 = concat T P1 r r λ0 (refl r)
                by refl (concat T P1 r r λ0) (inverse_refl T r)
              = λ0 by concat_p1 T P1 r λ0
              = ρ0 by inverse (Id T P1 r) ρ0 λ0 (concat_p1_1p_refl B y) ∎ in
        let J1 : Id T R0 (H P1)
          ≔ concat T R0 r (H P1) (loop_conjugate_unit B y y r) (inverse T (H P1) r (concat_inverse_right B y y P1)) in
        let J2 : Id T (H P1) R0
          ≔ concat T (H P1) (concat B y y y r (concat B y y y r (inverse B y y P1))) R0
              (concat_assoc B y y y y r r (inverse B y y P1))
              (concat T (concat B y y y r (concat B y y y r (inverse B y y P1))) (concat B y y y P1 (concat B y y y r (inverse B y y P1))) R0
                (refl ((w ↦ concat B y y y w (concat B y y y r (inverse B y y P1))) : T → T) (inverse T P1 r (concat_1p B y y r)))
                (refl ((w ↦ concat B y y y w (concat B y y y r (inverse B y y w))) : T → T) ρ0)) in
        let ζ : Id T r (inverse B y y P1)
          ≔ concat T r (inverse B y y r) (inverse B y y P1) (inverse T (inverse B y y r) r (inverse_refl B y))
              (refl (inverse B y y) (inverse T P1 r ρ0)) in
        let ι ≔ (w ↦ concat T w (concat B y y y w r) (H w) (inverse T (concat B y y y w r) w (concat_p1 B y y w))
              (refl (concat B y y y w) ζ)) : (w : T) → Id T w (H w) in
        let mi ≔ inverse T r r m in
        let V0 ≔ pointed_loop_conjugate T P1 r (inverse T r P1 (inverse T P1 r ρ0)) mi in
        let aρ ≔ refl H (inverse T r P1 (inverse T P1 r ρ0)) in
        let iJ2 ≔ inverse T (H P1) R0 J2 in
        let iι ≔ inverse T r (H r) (ι r) in
        let W ≔ concat T r R0 r ω (concat T R0 (H P1) r iJ2 (concat T (H P1) (H r) r aρ iι)) in
        calc
          pointed_loop_conjugate T r R0 ω (concat T R0 R0 R0 (inverse T R0 R0 (F n0 ρ0)) (F nm c0))
            = pointed_loop_conjugate T r R0 ω (concat T R0 R0 R0 (inverse T R0 R0 (F n0 ρ0)) (F nm ρ0))
            by refl ((c ↦ pointed_loop_conjugate T r R0 ω (concat T R0 R0 R0 (inverse T R0 R0 (F n0 ρ0)) (F nm c))) : Id T P1 r → Id T r r) ec
          = pointed_loop_conjugate T r R0 ω
              (pointed_loop_conjugate T R0 (H P1) iJ2 (concat T (H P1) (H P1) (H P1) (inverse T (H P1) (H P1) (refl H n0)) (refl H nm)))
            by refl (pointed_loop_conjugate T r R0 ω) (ulrik_group_cancel T R0 (H P1) J1 (refl H n0) (refl H nm) J2)
          = pointed_loop_conjugate T r R0 ω
              (pointed_loop_conjugate T R0 (H P1) iJ2 (refl H (concat T P1 P1 P1 (inverse T P1 P1 n0) nm)))
            by refl ((z ↦ pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2 z)) : Id T (H P1) (H P1) → Id T r r)
              (calc
                concat T (H P1) (H P1) (H P1) (inverse T (H P1) (H P1) (refl H n0)) (refl H nm)
                  = concat T (H P1) (H P1) (H P1) (refl H (inverse T P1 P1 n0)) (refl H nm)
                  by refl ((z ↦ concat T (H P1) (H P1) (H P1) z (refl H nm)) : Id T (H P1) (H P1) → Id T (H P1) (H P1))
                    (inverse (Id T (H P1) (H P1)) (refl H (inverse T P1 P1 n0)) (inverse T (H P1) (H P1) (refl H n0))
                      (map_path_inverse T T H P1 P1 n0))
                = refl H (concat T P1 P1 P1 (inverse T P1 P1 n0) nm)
                  by inverse (Id T (H P1) (H P1)) (refl H (concat T P1 P1 P1 (inverse T P1 P1 n0) nm))
                    (concat T (H P1) (H P1) (H P1) (refl H (inverse T P1 P1 n0)) (refl H nm))
                    (map_path_concat T T H P1 P1 P1 (inverse T P1 P1 n0) nm) ∎)
          = pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2 (refl H V0))
            by refl ((z ↦ pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2 (refl H z))) : Id T P1 P1 → Id T r r)
              (calc
                concat T P1 P1 P1 (inverse T P1 P1 n0) nm
                  = pointed_loop_conjugate T P1 r (inverse T r P1 (inverse T P1 r ρ0)) (concat T r r r (inverse T r r (inverse T r r (refl r))) mi)
                  by ulrik_group_cancel T P1 r λ0 (inverse T r r (refl r)) mi (inverse T P1 r ρ0)
                = V0
                  by refl (pointed_loop_conjugate T P1 r (inverse T r P1 (inverse T P1 r ρ0)))
                    (calc
                      concat T r r r (inverse T r r (inverse T r r (refl r))) mi = concat T r r r (refl r) mi
                        by refl ((z ↦ concat T r r r z mi) : Id T r r → Id T r r) (inverse_inverse T r r (refl r))
                      = mi by concat_1p T r r mi ∎) ∎)
          = pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2
              (pointed_loop_conjugate T (H P1) (H r) aρ (refl H mi)))
            by refl ((z ↦ pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2 z)) : Id T (H P1) (H P1) → Id T r r)
              (ulrik_map_conjugate T T H P1 r (inverse T r P1 (inverse T P1 r ρ0)) mi)
          = pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2
              (pointed_loop_conjugate T (H P1) (H r) aρ (pointed_loop_conjugate T (H r) r iι mi)))
            by refl ((z ↦ pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2
                  (pointed_loop_conjugate T (H P1) (H r) aρ z))) : Id T (H r) (H r) → Id T r r)
              (calc
                refl H mi = pointed_loop_conjugate T (H r) r iι (pointed_loop_conjugate T r (H r) (ι r) (refl H mi))
                  by inverse (Id T (H r) (H r)) (pointed_loop_conjugate T (H r) r iι (pointed_loop_conjugate T r (H r) (ι r) (refl H mi)))
                    (refl H mi) (loop_conjugate_cancel_inverse T r (H r) (ι r) (refl H mi))
                = pointed_loop_conjugate T (H r) r iι mi
                  by refl (pointed_loop_conjugate T (H r) r iι) (loops_map_homotopic_identity T H ι r mi) ∎)
          = pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2
              (pointed_loop_conjugate T (H P1) r (concat T (H P1) (H r) r aρ iι) mi))
            by refl ((z ↦ pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 (H P1) iJ2 z)) : Id T (H P1) (H P1) → Id T r r)
              (inverse (Id T (H P1) (H P1)) (pointed_loop_conjugate T (H P1) r (concat T (H P1) (H r) r aρ iι) mi)
                (pointed_loop_conjugate T (H P1) (H r) aρ (pointed_loop_conjugate T (H r) r iι mi))
                (loop_conjugate_compose T (H P1) (H r) r aρ iι mi))
          = pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 r (concat T R0 (H P1) r iJ2 (concat T (H P1) (H r) r aρ iι)) mi)
            by refl (pointed_loop_conjugate T r R0 ω)
              (inverse (Id T R0 R0) (pointed_loop_conjugate T R0 r (concat T R0 (H P1) r iJ2 (concat T (H P1) (H r) r aρ iι)) mi)
                (pointed_loop_conjugate T R0 (H P1) iJ2 (pointed_loop_conjugate T (H P1) r (concat T (H P1) (H r) r aρ iι) mi))
                (loop_conjugate_compose T R0 (H P1) r iJ2 (concat T (H P1) (H r) r aρ iι) mi))
          = pointed_loop_conjugate T r r W mi
            by inverse (Id T r r) (pointed_loop_conjugate T r r W mi)
              (pointed_loop_conjugate T r R0 ω (pointed_loop_conjugate T R0 r (concat T R0 (H P1) r iJ2 (concat T (H P1) (H r) r aρ iι)) mi))
              (loop_conjugate_compose T r R0 r ω (concat T R0 (H P1) r iJ2 (concat T (H P1) (H r) r aρ iι)) mi)
          = pointed_loop_conjugate T r r c' mi by ulrik_conjugate_independent B y r W c' mi
          = inverse T r r (pointed_loop_conjugate T r r c' m) by loop_conjugate_inverse T r r c' m ∎)
      u e m c' ω

{` rem:grpHomOK, the square fig:ulrik filled: for q : Ω(X →* Y),
   ptw_*(Ω(Ω)(q)) = i ∘ Ω(ptw_*(q)) as pointed maps ΩX →* Ω(ΩY), for all
   pointed X, Y. `}
def ulrik_square (X Y : Pointed) (q : Loop (pointed_maps_pointed X Y))
  : Id (BookPointedMap (Omega X) (Omega (Omega Y))) (ulrik_left X Y q) (ulrik_right X Y q)
  ≔ let A ≔ X .carrier in let B ≔ Y .carrier in let y ≔ Y .point in let a ≔ X .point in
    let T ≔ Id B y y in let r ≔ refl y in
    let M ≔ BookPointedMap X Y in let cst ≔ book_pointed_constant X Y in
    let c0f ≔ constant A B y in
    let PΩ ≔ BookPointedMap (Omega X) (Omega Y) in
    let ω0 ≔ loops_functor_point X Y in
    let Ω0 ≔ loops_pointed_map X Y in
    let k ≔ (z ↦ q .fst (refl z)) : A → T in
    let u ≔ k a in
    let T' ≔ (h ↦ Id B y (h a)) : (A → B) → Type in
    let cq ≔ pathover_transport_equiv (A → B) T' c0f c0f (q .fst) r r .map (q .snd) in
    let PTr ≔ pathover_transport_equiv (A → B) T' c0f c0f (refl c0f) r r .map (refl r) in
    let K ≔ constant_loops_pointed_equiv X Y .map q in
    let R0 ≔ pointed_loop_conjugate B y y r r in
    loops_pointed_map_path_from_underlying (Omega Y) (Omega X) (ulrik_left X Y q) (ulrik_right X Y q)
      (funext (Loop X) (_ ↦ Id T r r) (ulrik_left X Y q .fst) (ulrik_right X Y q .fst)
        (p ↦
          let G ≔ (φ ↦ φ .fst p) : PΩ → T in
          let ω ≔ refl G ω0 in
          let d ≔ concat T u (concat B y y y r u) r (inverse T (concat B y y y r u) u (concat_1p B y y u)) cq in
          calc
            ulrik_left X Y q .fst p
              = pointed_loop_conjugate T r R0 ω (refl G (refl Ω0 q))
              by ulrik_map_conjugate PΩ T G (book_pointed_constant (Omega X) (Omega Y)) (Ω0 cst) ω0 (refl Ω0 q)
            = pointed_loop_conjugate T r R0 ω
                (concat T R0 R0 R0
                  (inverse T R0 R0 (ulrik_path B y y r r r (naturality A B c0f c0f (_ ↦ r) a a p) PTr))
                  (ulrik_path B y y u r r (naturality A B c0f c0f k a a p) cq))
              by refl (pointed_loop_conjugate T r R0 ω) (ulrik_ap_loops X Y p cst q)
            = pointed_loop_conjugate T r R0 ω
                (concat T R0 R0 R0
                  (inverse T R0 R0 (ulrik_path B y y r r r (ulrik_naturality_form B y r (refl r)) (concat_p1 B y y r)))
                  (ulrik_path B y y u r r (ulrik_naturality_form B y u (refl k p))
                    (concat T (concat B y y y r u) u r (concat_1p B y y u) (inverse T r u (inverse T u r d)))))
              by refl ((n0 nk c1 c2 ↦ pointed_loop_conjugate T r R0 ω
                    (concat T R0 R0 R0 (inverse T R0 R0 (ulrik_path B y y r r r n0 c1)) (ulrik_path B y y u r r nk c2)))
                  : Id T (concat B y y y r r) (concat B y y y r r) → Id T (concat B y y y r u) (concat B y y y u r)
                    → Id T (concat B y y y r r) r → Id T (concat B y y y r u) r → Id T r r)
                (ulrik_constant_naturality A B y a (_ ↦ r) a p)
                (ulrik_constant_naturality A B y a k a p)
                (pathover_transport_refl_value (A → B) T' c0f r)
                (calc
                  cq = concat T (concat B y y y r u) u r (concat_1p B y y u) d
                    by inverse (Id T (concat B y y y r u) r) (concat T (concat B y y y r u) u r (concat_1p B y y u) d) cq
                      (concat_left_right_inverse T (concat B y y y r u) u r (concat_1p B y y u) cq)
                  = concat T (concat B y y y r u) u r (concat_1p B y y u) (inverse T r u (inverse T u r d))
                    by refl (concat T (concat B y y y r u) u r (concat_1p B y y u))
                      (inverse (Id T u r) (inverse T r u (inverse T u r d)) d (inverse_inverse T u r d)) ∎)
            = inverse T r r (pointed_loop_conjugate T r u (K .snd) (refl k p))
              by ulrik_final B y u (inverse T u r d) (refl k p) (K .snd) ω
            = ulrik_right X Y q .fst p by refl (ulrik_right X Y q .fst p) ∎))
