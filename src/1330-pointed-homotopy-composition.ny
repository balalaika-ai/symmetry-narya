export "289-book-equivalence-maps-two"

{` Chapter 13 (fields.tex), subsection "Move to a better place",
   lines 174-279: pointwise composition of pointed homotopies, its
   compatibility with ptw_*, and pointed constant maps.

   Conventions. ptw_* is the map of pointed_map_path_equiv (module 162,
   con:identity-ptd-maps), with values in PointedHomotopy X Y f g = H(f, g)
   = Σ (k : f ~ g) (k(pt)·f_pt = g_pt); the book's k(pt)·f_pt is
   concat f_pt (k pt) (module 162). Paths are in concatenation order:
   concat p q first follows p. In Narya neither unit law of concat holds
   judgmentally, so the book's judgmental steps "refl·r ≡ r" become
   concat_1p / concat_p1. `}

{` def:ptd-homotopy-compo. The pointwise composition k' ·ptw k of
   k : H(f, g) and k' : H(g, h), written with k first (concatenation
   order): first component x ↦ k'(x)·k(x) = concat (k x) (k' x); pointing
   path k'_pt · ap_{(k'(pt)·-)}(k_pt), preceded by the associativity
   identification that the book leaves implicit
   ((k'(pt)·k(pt))·f_pt = k'(pt)·(k(pt)·f_pt)). `}
def pointed_homotopy_compose (X Y : Pointed) (f g h : BookPointedMap X Y)
  (k : PointedHomotopy X Y f g) (k' : PointedHomotopy X Y g h) : PointedHomotopy X Y f h
  ≔ let B ≔ Y .carrier in let y ≔ Y .point in let a ≔ X .point in
    let fa ≔ f .fst a in let ga ≔ g .fst a in let ha ≔ h .fst a in
    ((x ↦ concat B (f .fst x) (g .fst x) (h .fst x) (k .fst x) (k' .fst x)),
     concat (Id B y ha)
       (concat B y fa ha (f .snd) (concat B fa ga ha (k .fst a) (k' .fst a)))
       (concat B y ga ha (concat B y fa ga (f .snd) (k .fst a)) (k' .fst a))
       (h .snd)
       (inverse (Id B y ha)
         (concat B y ga ha (concat B y fa ga (f .snd) (k .fst a)) (k' .fst a))
         (concat B y fa ha (f .snd) (concat B fa ga ha (k .fst a) (k' .fst a)))
         (concat_assoc B y fa ga ha (f .snd) (k .fst a) (k' .fst a)))
       (concat (Id B y ha)
         (concat B y ga ha (concat B y fa ga (f .snd) (k .fst a)) (k' .fst a))
         (concat B y ga ha (g .snd) (k' .fst a))
         (h .snd)
         (refl ((r ↦ concat B y ga ha r (k' .fst a)) : Id B y ga → Id B y ha) (k .snd))
         (k' .snd)))

{` Identifications in H(f, g) from a pointwise identification e of the
   homotopies and a coherence for the pointing paths. `}
def pointed_homotopy_path (X Y : Pointed) (f g : BookPointedMap X Y) (k k' : PointedHomotopy X Y f g)
  (e : (x : X .carrier) → Id (Id (Y .carrier) (f .fst x) (g .fst x)) (k .fst x) (k' .fst x))
  (c : Id (Id (Id (Y .carrier) (Y .point) (g .fst (X .point)))
            (concat (Y .carrier) (Y .point) (f .fst (X .point)) (g .fst (X .point)) (f .snd) (k .fst (X .point)))
            (g .snd))
         (k .snd)
         (concat (Id (Y .carrier) (Y .point) (g .fst (X .point)))
           (concat (Y .carrier) (Y .point) (f .fst (X .point)) (g .fst (X .point)) (f .snd) (k .fst (X .point)))
           (concat (Y .carrier) (Y .point) (f .fst (X .point)) (g .fst (X .point)) (f .snd) (k' .fst (X .point)))
           (g .snd)
           (refl (concat (Y .carrier) (Y .point) (f .fst (X .point)) (g .fst (X .point)) (f .snd)) (e (X .point)))
           (k' .snd)))
  : Id (PointedHomotopy X Y f g) k k'
  ≔ let A ≔ X .carrier in let B ≔ Y .carrier in let y ≔ Y .point in let a ≔ X .point in
    let fa ≔ f .fst a in let ga ≔ g .fst a in
    let Hm ≔ Homotopy A (_ ↦ B) (f .fst) (g .fst) in
    let cf ≔ concat B y fa ga (f .snd) in
    let P : Hm → Type ≔ m ↦ Id (Id B y ga) (cf (m a)) (g .snd) in
    let M : (m : Hm) → Id Hm (k .fst) m → Type
      ≔ m E ↦ (s : P m)
        → Id (P (k .fst)) (k .snd) (concat (Id B y ga) (cf (k .fst a)) (cf (m a)) (g .snd) (refl cf (E (refl a))) s)
        → Id (PointedHomotopy X Y f g) k (m, s) in
    let base : M (k .fst) (refl (k .fst))
      ≔ s d ↦ (refl (k .fst),
          concat (P (k .fst)) (k .snd) (concat (Id B y ga) (cf (k .fst a)) (cf (k .fst a)) (g .snd) (refl (cf (k .fst a))) s) s
            d (concat_1p (Id B y ga) (cf (k .fst a)) (g .snd) s)) in
    let E ≔ funext A (x ↦ Id B (f .fst x) (g .fst x)) (k .fst) (k' .fst) e in
    J Hm (k .fst) M base (k' .fst) E (k' .snd)
      (concat (P (k .fst)) (k .snd)
        (concat (Id B y ga) (cf (k .fst a)) (cf (k' .fst a)) (g .snd) (refl cf (e a)) (k' .snd))
        (concat (Id B y ga) (cf (k .fst a)) (cf (k' .fst a)) (g .snd) (refl cf (E (refl a))) (k' .snd))
        c
        (refl ((r ↦ concat (Id B y ga) (cf (k .fst a)) (cf (k' .fst a)) (g .snd) (refl cf r) (k' .snd))
            : Id (Id B fa ga) (k .fst a) (k' .fst a) → P (k .fst))
          (funext_beta A (x ↦ Id B (f .fst x) (g .fst x)) (k .fst) (k' .fst) e a)))

{` Path algebra: inverse (ρ · W⁻¹) · ρ = W. `}
def ptd_inverse_concat_cancel (T : Type) (p q r : T) (ρ : Id T p r) (W : Id T q r)
  : Id (Id T q r) (concat T q p r (inverse T p q (concat T p r q ρ (inverse T q r W))) ρ) W
  ≔ J T q (r W ↦ (p : T) (ρ : Id T p r)
        → Id (Id T q r) (concat T q p r (inverse T p q (concat T p r q ρ (inverse T q r W))) ρ) W)
      (p ρ ↦ J T p (q ρ ↦ Id (Id T q q)
            (concat T q p q (inverse T p q (concat T p q q ρ (inverse T q q (refl q)))) ρ) (refl q))
          (calc
            concat T p p p (inverse T p p (concat T p p p (refl p) (inverse T p p (refl p)))) (refl p)
              = inverse T p p (concat T p p p (refl p) (inverse T p p (refl p)))
              by concat_p1 T p p (inverse T p p (concat T p p p (refl p) (inverse T p p (refl p))))
            = inverse T p p (inverse T p p (refl p))
              by refl (inverse T p p) (concat_1p T p p (inverse T p p (refl p)))
            = inverse T p p (refl p) by refl (inverse T p p) (inverse_refl T p)
            = refl p by inverse_refl T p ∎) q ρ) r W p ρ

{` The coherence behind the right unit law: for t : u·v = w (concatenation
   order), assoc⁻¹ · ap_{(-·refl)}(t) · ρ_w = ap_{(u·-)}(ρ_v) · t. `}
def ptd_right_unit_coherence (B : Type) (y b c : B) (u : Id B y b) (v : Id B b c) (w : Id B y c)
  (t : Id (Id B y c) (concat B y b c u v) w)
  : Id (Id (Id B y c) (concat B y b c u (concat B b c c v (refl c))) w)
      (concat (Id B y c) (concat B y b c u (concat B b c c v (refl c)))
        (concat B y c c (concat B y b c u v) (refl c)) w
        (inverse (Id B y c) (concat B y c c (concat B y b c u v) (refl c))
          (concat B y b c u (concat B b c c v (refl c))) (concat_assoc B y b c c u v (refl c)))
        (concat (Id B y c) (concat B y c c (concat B y b c u v) (refl c)) (concat B y c c w (refl c)) w
          (refl ((r ↦ concat B y c c r (refl c)) : Id B y c → Id B y c) t) (concat_p1 B y c w)))
      (concat (Id B y c) (concat B y b c u (concat B b c c v (refl c))) (concat B y b c u v) w
        (refl (concat B y b c u) (concat_p1 B b c v)) t)
  ≔ let L ≔ Id B y c in
    let uv ≔ concat B y b c u v in
    let p ≔ concat B y c c uv (refl c) in
    let q ≔ concat B y b c u (concat B b c c v (refl c)) in
    let W ≔ refl (concat B y b c u) (concat_p1 B b c v) in
    let Z ≔ concat_assoc B y b c c u v (refl c) in
    let Z0 ≔ concat L p uv q (concat_p1 B y c uv) (inverse L q uv W) in
    J L uv (w t ↦ Id (Id L q w)
        (concat L q p w (inverse L p q Z)
          (concat L p (concat B y c c w (refl c)) w
            (refl ((r ↦ concat B y c c r (refl c)) : L → L) t) (concat_p1 B y c w)))
        (concat L q uv w W t))
      (calc
        concat L q p uv (inverse L p q Z) (concat L p p uv (refl p) (concat_p1 B y c uv))
          = concat L q p uv (inverse L p q Z) (concat_p1 B y c uv)
          by refl (concat L q p uv (inverse L p q Z)) (concat_1p L p uv (concat_p1 B y c uv))
        = concat L q p uv (inverse L p q Z0) (concat_p1 B y c uv)
          by refl ((z ↦ concat L q p uv (inverse L p q z) (concat_p1 B y c uv)) : Id L p q → Id L q uv)
            (inverse (Id L p q) Z0 Z
              (Jβ B c (w r ↦ Id (Id B y w) (concat B y c w uv r) (concat B y b w u (concat B b c w v r))) Z0))
        = W by ptd_inverse_concat_cancel L p q uv (concat_p1 B y c uv) W
        = concat L q uv uv W (refl uv) by inverse (Id L q uv) (concat L q uv uv W (refl uv)) W (concat_p1 L q uv W) ∎)
      w t

{` ptw_*(refl_g) is (x ↦ refl, ρ_{g_pt}): the pathover-to-transport map
   sends refl to transport_refl, which is concat_p1 g_pt. `}
def pathover_transport_refl_value (A : Type) (B : A → Type) (x : A) (u : B x)
  : Id (Id (B x) (transport A B x x (refl x) u) u)
      (pathover_transport_equiv A B x x (refl x) u u .map (refl u)) (transport_refl A B x u)
  ≔ let M : (y : A) → Id A x y → Type
      ≔ y p ↦ (v : B y) → Id Type (Id B p u v) (Id (B y) (transport A B x y p u) v) in
    let base : M x (refl x)
      ≔ v ↦ refl ((b ↦ Id (B x) b v) : B x → Type)
        (inverse (B x) (transport A B x x (refl x) u) u (transport_refl A B x u)) in
    let e ≔ inverse (B x) (transport A B x x (refl x) u) u (transport_refl A B x u) in
    let T ≔ Id (B x) (transport A B x x (refl x) u) u in
    calc
      pathover_transport_equiv A B x x (refl x) u u .map (refl u)
        = pathover_transport_type A B x x (refl x) u u .trr (refl u)
        by id_to_equiv_transport (Id (B x) u u) T (pathover_transport_type A B x x (refl x) u u) (refl u)
      = base u .trr (refl u)
        by inverse T (base u .trr (refl u)) (pathover_transport_type A B x x (refl x) u u .trr (refl u))
          (refl ((φ ↦ φ u .trr (refl u)) : M x (refl x) → T) (Jβ A x M base))
      = inverse (B x) u (transport A B x x (refl x) u) e by refl (inverse (B x) u (transport A B x x (refl x) u) e)
      = transport_refl A B x u by inverse_inverse (B x) (transport A B x x (refl x) u) u (transport_refl A B x u) ∎

def pointed_homotopy_refl (X Y : Pointed) (g : BookPointedMap X Y) : PointedHomotopy X Y g g
  ≔ ((x ↦ refl (g .fst x)), concat_p1 (Y .carrier) (Y .point) (g .fst (X .point)) (g .snd))

def ptw_refl_value (X Y : Pointed) (g : BookPointedMap X Y)
  : Id (PointedHomotopy X Y g g) (pointed_map_path_equiv X Y g g .map (refl g)) (pointed_homotopy_refl X Y g)
  ≔ let T : (X .carrier → Y .carrier) → Type ≔ k ↦ Id (Y .carrier) (Y .point) (k (X .point)) in
    concat (PointedHomotopy X Y g g) (pointed_map_path_equiv X Y g g .map (refl g))
      ((x ↦ refl (g .fst x)),
        pathover_transport_equiv (X .carrier → Y .carrier) T (g .fst) (g .fst) (refl (g .fst)) (g .snd) (g .snd)
          .map (refl (g .snd)))
      (pointed_homotopy_refl X Y g)
      (pointed_map_path_equiv_ptw X Y g g (refl g))
      (refl ((x ↦ refl (g .fst x)) : Homotopy (X .carrier) (_ ↦ Y .carrier) (g .fst) (g .fst)),
        pathover_transport_refl_value (X .carrier → Y .carrier) T (g .fst) (g .snd))

{` Right unit law of pointwise composition: k ·ptw ptw_*(refl) = k. `}
def pointed_homotopy_compose_refl (X Y : Pointed) (f g : BookPointedMap X Y) (k : PointedHomotopy X Y f g)
  : Id (PointedHomotopy X Y f g) (pointed_homotopy_compose X Y f g g k (pointed_homotopy_refl X Y g)) k
  ≔ let B ≔ Y .carrier in let a ≔ X .point in
    pointed_homotopy_path X Y f g (pointed_homotopy_compose X Y f g g k (pointed_homotopy_refl X Y g)) k
      (x ↦ concat_p1 B (f .fst x) (g .fst x) (k .fst x))
      (ptd_right_unit_coherence B (Y .point) (f .fst a) (g .fst a) (f .snd) (k .fst a) (g .snd) (k .snd))

{` con:ptd-homotopy-compo: ptw_*(qp) = ptw_*(q) ·ptw ptw_*(p), where the
   book's qp is concat p q. By induction on q, as in the book; the base
   case is the right unit law. `}
def ptw_concat_compose (X Y : Pointed) (f g h : BookPointedMap X Y)
  (p : Id (BookPointedMap X Y) f g) (q : Id (BookPointedMap X Y) g h)
  : Id (PointedHomotopy X Y f h) (pointed_map_path_equiv X Y f h .map (concat (BookPointedMap X Y) f g h p q))
      (pointed_homotopy_compose X Y f g h (pointed_map_path_equiv X Y f g .map p) (pointed_map_path_equiv X Y g h .map q))
  ≔ let M ≔ BookPointedMap X Y in
    let ptw ≔ (u v ↦ pointed_map_path_equiv X Y u v .map) : (u v : M) → Id M u v → PointedHomotopy X Y u v in
    J M g (h q ↦ Id (PointedHomotopy X Y f h) (ptw f h (concat M f g h p q))
        (pointed_homotopy_compose X Y f g h (ptw f g p) (ptw g h q)))
      (calc
        ptw f g (concat M f g g p (refl g)) = ptw f g p by refl (ptw f g) (concat_p1 M f g p)
        = pointed_homotopy_compose X Y f g g (ptw f g p) (pointed_homotopy_refl X Y g)
          by inverse (PointedHomotopy X Y f g)
            (pointed_homotopy_compose X Y f g g (ptw f g p) (pointed_homotopy_refl X Y g)) (ptw f g p)
            (pointed_homotopy_compose_refl X Y f g (ptw f g p))
        = pointed_homotopy_compose X Y f g g (ptw f g p) (ptw g g (refl g))
          by refl (pointed_homotopy_compose X Y f g g (ptw f g p))
            (inverse (PointedHomotopy X Y g g) (ptw g g (refl g)) (pointed_homotopy_refl X Y g) (ptw_refl_value X Y g)) ∎)
      h q

{` def:cst-ptd. The pointed constant map cst_*^A(b, p) ≔ (cst_b, p), a
   function from Σ (x : B) (pt_B = x) to A →* B. `}
def pointed_constant_at (A B : Pointed) (u : Σ (B .carrier) (x ↦ Id (B .carrier) (B .point) x)) : BookPointedMap A B
  ≔ (constant (A .carrier) (B .carrier) (u .fst), u .snd)

{` The point of A →* B is cst_*(pt_B, refl). `}
def pointed_constant_at_point (A B : Pointed)
  : Id (BookPointedMap A B) (pointed_constant_at A B (B .point, refl (B .point))) (book_pointed_constant A B)
  ≔ refl (book_pointed_constant A B)

{` Footnote to def:cst-ptd: Σ (x : B) (pt_B = x) is contractible. `}
def pointed_constant_domain_contractible (B : Pointed)
  : BookIsContr (Σ (B .carrier) (x ↦ Id (B .carrier) (B .point) x))
  ≔ book_pathspace_contractible (B .carrier) (B .point)
