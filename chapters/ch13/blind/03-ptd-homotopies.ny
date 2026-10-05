export "../../../src/401-group-homomorphisms"

{` Blind statements, chapter 13 (fields.tex), pointed homotopies:
   def:ptd-homotopy-compo, con:ptd-homotopy-compo, def:cst-ptd,
   rem:loops-at-ptd-cst.

   Conventions. The book's path product q·p (p first) is concat p q.
   Pointed maps are BookPointedMap (pt_Y = f pt_X). The book's
   H(f, g) = Σ (k : Π_x f x = g x), k(pt_X)·f_pt = g_pt is the type
   PointedHomotopy X Y f g of module 162 (concat f_pt (k pt_X) = g_pt);
   ptw_* of con:identity-ptd-maps is pointed_map_path_equiv (module 162). `}

{` ptw_* : (f = g) → H(f, g) (con:identity-ptd-maps). `}
def blind_ptw (X Y : Pointed) (f g : BookPointedMap X Y) (p : Id (BookPointedMap X Y) f g)
  : PointedHomotopy X Y f g
  ≔ pointed_map_path_equiv X Y f g .map p

{` def:ptd-homotopy-compo. (k' ·ptw k) ≔ (x ↦ k'(x)·k(x), k'_pt · ap_{k'(pt)·-}(k_pt)).
   The book's outer type k'(pt)·k(pt)·f_pt = h_pt is read with the
   association (k'(pt)·k(pt))·f_pt of the pointwise composite, so one
   associativity path (concat_assoc, inverted) precedes the printed
   composite; the book treats this re-bracketing as silent. `}
def blind_ptw_compose (X Y : Pointed) (f g h : BookPointedMap X Y)
  (k : PointedHomotopy X Y f g) (k' : PointedHomotopy X Y g h)
  : PointedHomotopy X Y f h
  ≔ let B ≔ Y .carrier in let y ≔ Y .point in let x0 ≔ X .point in
    (x ↦ concat B (f .fst x) (g .fst x) (h .fst x) (k .fst x) (k' .fst x),
     concat (Id B y (h .fst x0))
       (concat B y (f .fst x0) (h .fst x0) (f .snd)
         (concat B (f .fst x0) (g .fst x0) (h .fst x0) (k .fst x0) (k' .fst x0)))
       (concat B y (g .fst x0) (h .fst x0) (g .snd) (k' .fst x0))
       (h .snd)
       (concat (Id B y (h .fst x0))
         (concat B y (f .fst x0) (h .fst x0) (f .snd)
           (concat B (f .fst x0) (g .fst x0) (h .fst x0) (k .fst x0) (k' .fst x0)))
         (concat B y (g .fst x0) (h .fst x0)
           (concat B y (f .fst x0) (g .fst x0) (f .snd) (k .fst x0)) (k' .fst x0))
         (concat B y (g .fst x0) (h .fst x0) (g .snd) (k' .fst x0))
         (inverse (Id B y (h .fst x0))
           (concat B y (g .fst x0) (h .fst x0)
             (concat B y (f .fst x0) (g .fst x0) (f .snd) (k .fst x0)) (k' .fst x0))
           (concat B y (f .fst x0) (h .fst x0) (f .snd)
             (concat B (f .fst x0) (g .fst x0) (h .fst x0) (k .fst x0) (k' .fst x0)))
           (concat_assoc B y (f .fst x0) (g .fst x0) (h .fst x0) (f .snd) (k .fst x0) (k' .fst x0)))
         (refl ((r : Id B y (g .fst x0)) ↦ concat B y (g .fst x0) (h .fst x0) r (k' .fst x0)) (k .snd)))
       (k' .snd))

{` con:ptd-homotopy-compo: ptw_*(qp) = ptw_*(q) ·ptw ptw_*(p) for p : f = g,
   q : g = h (qp = concat p q). `}
def blind_con_ptd_homotopy_compo : Type
  ≔ (X Y : Pointed) (f g h : BookPointedMap X Y)
    (p : Id (BookPointedMap X Y) f g) (q : Id (BookPointedMap X Y) g h)
    → Id (PointedHomotopy X Y f h)
        (blind_ptw X Y f h (concat (BookPointedMap X Y) f g h p q))
        (blind_ptw_compose X Y f g h (blind_ptw X Y f g p) (blind_ptw X Y g h q))

{` def:cst-ptd: cst_*^A(b, p) ≔ (cst_b^A, p), a function from Σ_{x:B} (pt_B = x)
   to A →* B. `}
def blind_cst_ptd (A B : Pointed) (u : Σ (B .carrier) (x ↦ Id (B .carrier) (B .point) x))
  : BookPointedMap A B
  ≔ (constant (A .carrier) (B .carrier) (u .fst), u .snd)

{` def:cst-ptd, footnote: Σ_{x:B} (pt_B = x) is contractible. `}
def blind_def_cst_ptd_domain_contr : Type
  ≔ (B : Pointed) → BookIsContr (Σ (B .carrier) (x ↦ Id (B .carrier) (B .point) x))

{` The pointed type X →* Y, pointed at (cst_{pt_Y}, refl). `}
def blind_ptd_maps (X Y : Pointed) : Pointed
  ≔ (BookPointedMap X Y, book_pointed_constant X Y)

{` A path equivalence by induction on the two endpoint paths. `}
def blind_path_endpoints_equiv (B : Type) (u u' v v' : B) (p : Id B u' u) (q : Id B v v')
  : Equiv (Id B u v) (Id B u' v')
  ≔ J B u' (u p ↦ Equiv (Id B u v) (Id B u' v'))
      (J B v (v' q ↦ Equiv (Id B u' v) (Id B u' v')) (identity_equiv (Id B u' v)) v' q) u p

{` rem:loops-at-ptd-cst: H(pt, pt) ≃ Σ_{h : X → ΩY} (refl = h(pt_X)) ≡ X →* ΩY,
   replacing (h(pt_X)·refl = refl) (here concat refl (h pt_X) = refl) by
   refl = h(pt_X) "by laws of symmetry and right unit". `}
def blind_H_cst_equiv (X Y : Pointed)
  : Equiv (PointedHomotopy X Y (book_pointed_constant X Y) (book_pointed_constant X Y))
      (BookPointedMap X (Omega Y))
  ≔ let y ≔ Y .point in let L ≔ Id (Y .carrier) y y in
    family_equiv (X .carrier → L)
      (h ↦ Id L (concat (Y .carrier) y y y (refl y) (h (X .point))) (refl y))
      (h ↦ Id L (refl y) (h (X .point)))
      (h ↦ compose_equiv (Id L (concat (Y .carrier) y y y (refl y) (h (X .point))) (refl y))
        (Id L (h (X .point)) (refl y)) (Id L (refl y) (h (X .point)))
        (blind_path_endpoints_equiv L (concat (Y .carrier) y y y (refl y) (h (X .point))) (h (X .point))
          (refl y) (refl y)
          (inverse L (concat (Y .carrier) y y y (refl y) (h (X .point))) (h (X .point))
            (concat_1p (Y .carrier) y y (h (X .point))))
          (refl (refl y)))
        (inverse_path_equiv L (h (X .point)) (refl y)))

{` The variant ptw_* : Ω(X →* Y) ≃ (X →* ΩY) of rem:loops-at-ptd-cst. `}
def blind_ptw_loops (X Y : Pointed) : Equiv (Loop (blind_ptd_maps X Y)) (BookPointedMap X (Omega Y))
  ≔ compose_equiv (Loop (blind_ptd_maps X Y))
      (PointedHomotopy X Y (book_pointed_constant X Y) (book_pointed_constant X Y))
      (BookPointedMap X (Omega Y))
      (pointed_map_path_equiv X Y (book_pointed_constant X Y) (book_pointed_constant X Y))
      (blind_H_cst_equiv X Y)

def blind_ptw_loops_inv (X Y : Pointed) (k : BookPointedMap X (Omega Y)) : Loop (blind_ptd_maps X Y)
  ≔ equiv_inverse_map (Loop (blind_ptd_maps X Y)) (BookPointedMap X (Omega Y)) (blind_ptw_loops X Y) k

{` rem:loops-at-ptd-cst, the claims: H(pt, pt) ≃ (X →* ΩY) and
   Ω(X →* Y) ≃ (X →* ΩY). `}
def blind_rem_loops_at_ptd_cst : Type
  ≔ (X Y : Pointed)
    → Product
        (BookEquiv (PointedHomotopy X Y (book_pointed_constant X Y) (book_pointed_constant X Y))
          (BookPointedMap X (Omega Y)))
        (BookEquiv (Loop (blind_ptd_maps X Y)) (BookPointedMap X (Omega Y)))
