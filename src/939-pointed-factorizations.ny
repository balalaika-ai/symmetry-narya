export "285-chapter-three-completions"

{` Chapter 9 (subgroups.tex), rem:n-im-ptd-map (line 889): factorizations
   of pointed maps. For pointed X, Z and f : X →* Z,
     Fact_*(f) ≔ Σ_{Y : U_*} Σ_{p : X →* Y} Σ_{i : Y →* Z} (f = i ∘ p),
   and Fact_*^n ≔ Σ_{(Y,p,i,h) : Fact_*(f)} (isnconn(p) × isntrunc(i)) is
   contractible for every n ≥ -2. We prove a general statement: for any
   property P(C, g, h) of unpointed factorizations whose type of unpointed
   factorizations Σ_{(C,g,h,e) : Fact(f)} P(C,g,h) is contractible, the
   pointed version is contractible (the pointing data y0, p_pt, i_pt and the
   2-cell b of the remark form a contractible type). Then n-images are the
   instance P = (isnconn × isntrunc) of thm:n-im-univ-prop (module 285, all
   n ≥ -2, n = m - 2). Pointed maps follow the book orientation
   (pt_Y = p(pt_X), BookPointedMap) and f = i ∘ p is an identification of
   pointed maps (book_pointed_compose). `}

def PfactPointed (X Z : Pointed) (f : BookPointedMap X Z) : Type
  ≔ Σ Pointed (Y ↦ Σ (BookPointedMap X Y) (p ↦ Σ (BookPointedMap Y Z) (i ↦
      Id (BookPointedMap X Z) f (book_pointed_compose X Y Z p i))))

def PfactPointedWith (X Z : Pointed) (f : BookPointedMap X Z)
  (P : (C : Type) → (X .carrier → C) → (C → Z .carrier) → Type) : Type
  ≔ Σ (PfactPointed X Z f) (t ↦ P (t .fst .carrier) (t .snd .fst .fst) (t .snd .snd .fst .fst))

{` Unpointed factorizations with a homotopy f ~ h ∘ g. `}
def PfactUnpointedH (A B : Type) (f : A → B) (P : (C : Type) → (A → C) → (C → B) → Type) : Type
  ≔ Σ Type (C ↦ Σ (A → C) (g ↦ Σ (C → B) (h ↦
      Product (Homotopy A (_ ↦ B) f (compose A C B h g)) (P C g h))))

{` The pointing data over an unpointed factorization: y0, p_pt : y0 = g(x0),
   i_pt : z0 = h(y0) and the 2-cell f_pt · H(x0) = i_pt · ap_h(p_pt). `}
def PfactPointData (X Z : Pointed) (f : BookPointedMap X Z)
  (P : (C : Type) → (X .carrier → C) → (C → Z .carrier) → Type)
  (t : PfactUnpointedH (X .carrier) (Z .carrier) (f .fst) P) : Type
  ≔ let C ≔ t .fst in
    let g ≔ t .snd .fst in
    let h ≔ t .snd .snd .fst in
    let H ≔ t .snd .snd .snd .fst in
    let x0 ≔ X .point in
    let z0 ≔ Z .point in
    let Zc ≔ Z .carrier in
    Σ C (y0 ↦ Σ (Id C y0 (g x0)) (pp ↦ Σ (Id Zc z0 (h y0)) (ip ↦
      Id (Id Zc z0 (h (g x0))) (concat Zc z0 (f .fst x0) (h (g x0)) (f .snd) (H x0))
        (concat Zc z0 (h y0) (h (g x0)) ip (refl h pp)))))

{` Fact_* with properties ≃ Σ (unpointed with properties) (pointing data). `}
def pfact_split (X Z : Pointed) (f : BookPointedMap X Z)
  (P : (C : Type) → (X .carrier → C) → (C → Z .carrier) → Type)
  : Equiv (PfactPointedWith X Z f P)
      (Σ (PfactUnpointedH (X .carrier) (Z .carrier) (f .fst) P) (PfactPointData X Z f P))
  ≔ let U ≔ PfactUnpointedH (X .carrier) (Z .carrier) (f .fst) P in
    let D ≔ PfactPointData X Z f P in
    let W ≔ PfactPointedWith X Z f P in
    let pme ≔ pointed_map_path_equiv X Z f in
    quasi_inverse_equiv W (Σ U D)
      (t ↦
        let Y ≔ t .fst .fst in
        let p ≔ t .fst .snd .fst in
        let i ≔ t .fst .snd .snd .fst in
        let ph ≔ pme (book_pointed_compose X Y Z p i) .map (t .fst .snd .snd .snd) in
        ((Y .carrier, (p .fst, (i .fst, (ph .fst, t .snd)))), (Y .point, (p .snd, (i .snd, ph .snd)))))
      (u ↦
        let C ≔ u .fst .fst in
        let g ≔ u .fst .snd .fst in
        let h ≔ u .fst .snd .snd .fst in
        let Y : Pointed ≔ (C, u .snd .fst) in
        let p : BookPointedMap X Y ≔ (g, u .snd .snd .fst) in
        let i : BookPointedMap Y Z ≔ (h, u .snd .snd .snd .fst) in
        let k ≔ book_pointed_compose X Y Z p i in
        (((Y, (p, (i, equiv_inverse_map (Id (BookPointedMap X Z) f k) (PointedHomotopy X Z f k) (pme k)
              (u .fst .snd .snd .snd .fst, u .snd .snd .snd .snd))))),
         u .fst .snd .snd .snd .snd))
      (t ↦
        let Y ≔ t .fst .fst in
        let p ≔ t .fst .snd .fst in
        let i ≔ t .fst .snd .snd .fst in
        let k ≔ book_pointed_compose X Y Z p i in
        let r ≔ t .fst .snd .snd .snd in
        refl ((e ↦ ((Y, (p, (i, e))), t .snd)) : Id (BookPointedMap X Z) f k → W)
          (equiv_retraction (Id (BookPointedMap X Z) f k) (PointedHomotopy X Z f k) (pme k) r))
      (u ↦
        let C ≔ u .fst .fst in
        let g ≔ u .fst .snd .fst in
        let h ≔ u .fst .snd .snd .fst in
        let Y : Pointed ≔ (C, u .snd .fst) in
        let p : BookPointedMap X Y ≔ (g, u .snd .snd .fst) in
        let i : BookPointedMap Y Z ≔ (h, u .snd .snd .snd .fst) in
        let k ≔ book_pointed_compose X Y Z p i in
        refl ((w ↦ ((C, (g, (h, (w .fst, u .fst .snd .snd .snd .snd)))), (u .snd .fst, (u .snd .snd .fst, (u .snd .snd .snd .fst, w .snd)))))
               : PointedHomotopy X Z f k → Σ U D)
          (equiv_counit (Id (BookPointedMap X Z) f k) (PointedHomotopy X Z f k) (pme k)
             (u .fst .snd .snd .snd .fst, u .snd .snd .snd .snd)))

{` Function paths vs homotopies in the triangle. `}
def pfact_unpointed_equiv (A B : Type) (f : A → B) (P : (C : Type) → (A → C) → (C → B) → Type)
  : Equiv (Σ (Factorizations A B f) (t ↦ P (t .fst) (t .snd .fst) (t .snd .snd .fst))) (PfactUnpointedH A B f P)
  ≔ let L ≔ Σ (Factorizations A B f) (t ↦ P (t .fst) (t .snd .fst) (t .snd .snd .fst)) in
    let U ≔ PfactUnpointedH A B f P in
    let fe : (C : Type) (g : A → C) (h : C → B)
          → Equiv (Id (A → B) f (compose A C B h g)) (Homotopy A (_ ↦ B) f (compose A C B h g))
      ≔ C g h ↦ function_extensionality A (_ ↦ B) f (compose A C B h g) in
    quasi_inverse_equiv L U
      (t ↦ (t .fst .fst, (t .fst .snd .fst, (t .fst .snd .snd .fst,
             (fe (t .fst .fst) (t .fst .snd .fst) (t .fst .snd .snd .fst) .map (t .fst .snd .snd .snd), t .snd)))))
      (u ↦ ((u .fst, (u .snd .fst, (u .snd .snd .fst,
             equiv_inverse_map (Id (A → B) f (compose A (u .fst) B (u .snd .snd .fst) (u .snd .fst)))
               (Homotopy A (_ ↦ B) f (compose A (u .fst) B (u .snd .snd .fst) (u .snd .fst)))
               (fe (u .fst) (u .snd .fst) (u .snd .snd .fst)) (u .snd .snd .snd .fst)))),
            u .snd .snd .snd .snd))
      (t ↦
        let C ≔ t .fst .fst in let g ≔ t .fst .snd .fst in let h ≔ t .fst .snd .snd .fst in
        refl ((e ↦ ((C, (g, (h, e))), t .snd)) : Id (A → B) f (compose A C B h g) → L)
          (equiv_retraction (Id (A → B) f (compose A C B h g)) (Homotopy A (_ ↦ B) f (compose A C B h g))
             (fe C g h) (t .fst .snd .snd .snd)))
      (u ↦
        let C ≔ u .fst in let g ≔ u .snd .fst in let h ≔ u .snd .snd .fst in
        refl ((H ↦ (C, (g, (h, (H, u .snd .snd .snd .snd))))) : Homotopy A (_ ↦ B) f (compose A C B h g) → U)
          (equiv_counit (Id (A → B) f (compose A C B h g)) (Homotopy A (_ ↦ B) f (compose A C B h g))
             (fe C g h) (u .snd .snd .snd .fst)))

{` Right concatenation with a fixed path is an equivalence. `}
def pfact_concat_right_equiv (A : Type) (x y z : A) (q : Id A y z) : Equiv (Id A x y) (Id A x z)
  ≔ quasi_inverse_equiv (Id A x y) (Id A x z) (p ↦ concat A x y z p q) (r ↦ concat A x z y r (inverse A y z q))
      (p ↦ calc
         concat A x z y (concat A x y z p q) (inverse A y z q)
         = concat A x y y p (concat A y z y q (inverse A y z q)) by concat_assoc A x y z y p q (inverse A y z q)
         = concat A x y y p (refl y) by refl (concat A x y y p) (concat_inverse_right A y z q)
         = p by concat_p1 A x y p ∎)
      (r ↦ calc
         concat A x y z (concat A x z y r (inverse A y z q)) q
         = concat A x z z r (concat A z y z (inverse A y z q) q) by concat_assoc A x z y z r (inverse A y z q) q
         = concat A x z z r (refl z) by refl (concat A x z z r) (concat_inverse_left A y z q)
         = r by concat_p1 A x z r ∎)

{` The pointing data form a contractible type: (y0, p_pt) ranges over a
   singleton, and then i_pt is determined by the 2-cell. `}
def pfact_point_data_contractible (X Z : Pointed) (f : BookPointedMap X Z)
  (P : (C : Type) → (X .carrier → C) → (C → Z .carrier) → Type)
  (t : PfactUnpointedH (X .carrier) (Z .carrier) (f .fst) P)
  : isContr (PfactPointData X Z f P t)
  ≔ let C ≔ t .fst in
    let g ≔ t .snd .fst in
    let h ≔ t .snd .snd .fst in
    let H ≔ t .snd .snd .snd .fst in
    let x0 ≔ X .point in
    let z0 ≔ Z .point in
    let Zc ≔ Z .carrier in
    let c ≔ concat Zc z0 (f .fst x0) (h (g x0)) (f .snd) (H x0) in
    let Base ≔ Σ C (y0 ↦ Id C y0 (g x0)) in
    let Fam : Base → Type
      ≔ w ↦ BookFiber (Id Zc z0 (h (w .fst))) (Id Zc z0 (h (g x0)))
          (ip ↦ concat Zc z0 (h (w .fst)) (h (g x0)) ip (refl h (w .snd))) c in
    let D ≔ PfactPointData X Z f P t in
    let e : Equiv (Σ Base Fam) D
      ≔ quasi_inverse_equiv (Σ Base Fam) D
          (v ↦ (v .fst .fst, (v .fst .snd, (v .snd .fst, v .snd .snd))))
          (d ↦ ((d .fst, d .snd .fst), (d .snd .snd .fst, d .snd .snd .snd)))
          (v ↦ refl v) (d ↦ refl d) in
    let hb : isContr Base ≔ identity_equiv C .equiv (g x0) in
    let hf : (w : Base) → isContr (Fam w)
      ≔ w ↦ native_contraction (Fam w)
          (book_equivalence (Id Zc z0 (h (w .fst))) (Id Zc z0 (h (g x0)))
             (pfact_concat_right_equiv Zc z0 (h (w .fst)) (h (g x0)) (refl h (w .snd))) .equiv c) in
    native_contraction D
      (book_contractibility_equiv (Σ Base Fam) D e .map
        (book_contraction (Σ Base Fam) (sigma_contractible Base Fam hb hf)))

{` The general statement. `}
def pfact_contractible (X Z : Pointed) (f : BookPointedMap X Z)
  (P : (C : Type) → (X .carrier → C) → (C → Z .carrier) → Type)
  (hU : BookIsContr (Σ (Factorizations (X .carrier) (Z .carrier) (f .fst)) (t ↦ P (t .fst) (t .snd .fst) (t .snd .snd .fst))))
  : BookIsContr (PfactPointedWith X Z f P)
  ≔ let A ≔ X .carrier in let B ≔ Z .carrier in
    let U ≔ PfactUnpointedH A B (f .fst) P in
    let D ≔ PfactPointData X Z f P in
    let hU' : BookIsContr U
      ≔ book_contractibility_equiv (Σ (Factorizations A B (f .fst)) (t ↦ P (t .fst) (t .snd .fst) (t .snd .snd .fst))) U
          (pfact_unpointed_equiv A B (f .fst) P) .map hU in
    book_contractibility_equiv (Σ U D) (PfactPointedWith X Z f P)
      (canonical_inverse_equiv (PfactPointedWith X Z f P) (Σ U D) (pfact_split X Z f P)) .map
      (book_contraction (Σ U D) (sigma_contractible U D (native_contraction U hU') (pfact_point_data_contractible X Z f P)))

{` rem:n-im-ptd-map: Fact_*^n is contractible for every n ≥ -2 (n = m - 2;
   n-connected = NConnectedMapFrom m, n-truncated = TruncatedMap m). `}
def PfactNProperties (m : Nat) (A B : Type) (C : Type) (g : A → C) (h : C → B) : Type
  ≔ Product (NConnectedMapFrom m A C g) (TruncatedMap m C B h)

def PfactPointedN (m : Nat) (X Z : Pointed) (f : BookPointedMap X Z) : Type
  ≔ PfactPointedWith X Z f (PfactNProperties m (X .carrier) (Z .carrier))

def pfact_n_image_pointed_contractible (m : Nat) (X Z : Pointed) (f : BookPointedMap X Z)
  : BookIsContr (PfactPointedN m X Z f)
  ≔ pfact_contractible X Z f (PfactNProperties m (X .carrier) (Z .carrier))
      (n_image_universal_property_all m (X .carrier) (Z .carrier) (f .fst))

{` The case n = 0 in the form used for groups (0-connected map: all
   set-truncated fibers contractible; 0-truncated: covering). `}
def PfactZeroProperties (A B : Type) (C : Type) (g : A → C) (h : C → B) : Type
  ≔ Product (ZeroConnectedMap A C g) (IsCovering C B h)

def pfact_zero_image_pointed_contractible (X Z : Pointed) (f : BookPointedMap X Z)
  : BookIsContr (PfactPointedWith X Z f (PfactZeroProperties (X .carrier) (Z .carrier)))
  ≔ pfact_contractible X Z f (PfactZeroProperties (X .carrier) (Z .carrier))
      (zero_image_book_universal_property (X .carrier) (Z .carrier) (f .fst))

{` The canonical element (the pointed 0-image factorization) lies in the
   contractible type; the pointing of the 0-image factor is as in
   xca:p-epi-i-mono: (f_pt, transport of |(x0, f_pt)|₀), and fst is pointed by
   refl. Litmus: Fact_*^n of the identity of the pointed unit type. `}
def pfact_unit_pointed : Pointed ≔ (Unit, star.)

def pfact_unit_identity_factorization (m : Nat)
  : BookIsContr (PfactPointedN m pfact_unit_pointed pfact_unit_pointed (book_pointed_identity pfact_unit_pointed))
  ≔ pfact_n_image_pointed_contractible m pfact_unit_pointed pfact_unit_pointed (book_pointed_identity pfact_unit_pointed)

{` rem:n-im-ptd-map: "if X and Z are connected groupoids, then so is
   Σ_{z:Z} ‖f⁻¹(z)‖_n", here for n = 0 (the case used for groups): the set
   image of a map from a connected type is connected (module 116) and fst is
   a covering, so over a groupoid it has a groupoid domain (module 118). `}
def pfact_zero_image_connected_groupoid (A B : Type) (f : A → B) (hA : Connected A) (hB : isGroupoid B)
  : Product (Connected (ZeroImage A B f)) (isGroupoid (ZeroImage A B f))
  ≔ (zero_image_connected A B f hA,
     covering_domain_groupoid (ZeroImage A B f) B (zero_image_include A B f) (zero_image_include_covering A B f) hB)
