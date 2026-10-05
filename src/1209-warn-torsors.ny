export "1204-double-delooping"

{` Chapter 12, sec. "Higher deloopings" (abelian.tex 668-777): Wärn's
   X-torsors, his delooping lemma, xca:sections-as-dependent-functions, the
   description of TX through sections of the evaluation map, and
   lem:warn-abelian-group (T(BG) ≃ BB G for abelian G), proved for every
   connected central pointed type as in the footnote. `}

{` Definition (Wärn): TX ≔ Σ(Y : U) ‖Y‖ × Π(y : Y) (Y, y) ≃* X, and
   TX_* ≔ Σ(t : TX) fst t. `}
def WarnTorsor (X : Pointed) : Type ≔ Σ Type (Y ↦ Product (Mere Y) ((y : Y) → BookPointedEquiv (Y, y) X))

def PointedWarnTorsor (X : Pointed) : Type ≔ Σ (WarnTorsor X) (t ↦ t .fst)

{` Composition of pointed equivalences. `}
def book_pointed_equiv_compose (X Y Z : Pointed) (e : BookPointedEquiv X Y) (d : BookPointedEquiv Y Z)
  : BookPointedEquiv X Z
  ≔ (book_pointed_compose X Y Z (e .fst) (d .fst),
     book_equivalence (X .carrier) (Z .carrier)
       (compose_equiv (X .carrier) (Y .carrier) (Z .carrier)
         (native_equivalence (X .carrier) (Y .carrier) (e .fst .fst, e .snd))
         (native_equivalence (Y .carrier) (Z .carrier) (d .fst .fst, d .snd))) .equiv)

{` Lemma (Wärn): if TX_* is contractible then for every pointed X-torsor
   (t, y), (TX, t) is a delooping of X. The equivalence (t = t) ≃ fst t,
   r ↦ trp^{fst}_r(y), is the fiberwise map between the contractible total
   spaces Σ(u : TX) (t = u) and TX_* (the book's two contractions). `}
def warn_loops_map (X : Pointed) (t : WarnTorsor X) (y : t .fst) (u : WarnTorsor X) (r : Id (WarnTorsor X) t u) : u .fst
  ≔ transport (WarnTorsor X) (v ↦ v .fst) t u r y

def warn_loops_equiv (X : Pointed) (h : BookIsContr (PointedWarnTorsor X)) (t : WarnTorsor X) (y : t .fst)
  : BookPointedEquiv (Omega (WarnTorsor X, t)) (t .fst, y)
  ≔ ((warn_loops_map X t y t,
      inverse (t .fst) (transport (WarnTorsor X) (v ↦ v .fst) t t (refl t) y) y
        (transport_refl (WarnTorsor X) (v ↦ v .fst) t y)),
     book_equivalence (Id (WarnTorsor X) t t) (t .fst)
       (warn_loops_map X t y t,
        fiberwise_from_total (WarnTorsor X) (u ↦ Id (WarnTorsor X) t u) (u ↦ u .fst) (warn_loops_map X t y)
          (contractible_map_equiv (Σ (WarnTorsor X) (u ↦ Id (WarnTorsor X) t u)) (PointedWarnTorsor X)
            (totalize (WarnTorsor X) (u ↦ Id (WarnTorsor X) t u) (u ↦ u .fst) (warn_loops_map X t y))
            (book_pathspace_contractible (WarnTorsor X) t) h) t) .equiv)

def warn_delooping (X : Pointed) (h : BookIsContr (PointedWarnTorsor X)) (t : WarnTorsor X) (y : t .fst)
  : BookPointedEquiv (Omega (WarnTorsor X, t)) X
  ≔ book_pointed_equiv_compose (Omega (WarnTorsor X, t)) (t .fst, y) X (warn_loops_equiv X h t y) (t .snd .snd y)

def warn_delooping_path (X : Pointed) (h : BookIsContr (PointedWarnTorsor X)) (t : WarnTorsor X) (y : t .fst)
  : Id Pointed (Omega (WarnTorsor X, t)) X
  ≔ equiv_inverse_map (Id Pointed (Omega (WarnTorsor X, t)) X) (BookPointedEquiv (Omega (WarnTorsor X, t)) X)
      (pointed_path_equiv (Omega (WarnTorsor X, t)) X) (warn_delooping X h t y)

{` xca:sections-as-dependent-functions. sec(f) ≔ Σ(s : B → A) (f ∘ s = id_B)
   is equivalent to Π(b : B) Σ(a : A) (b = f(a)). `}
def SectionsOf (A B : Type) (f : A → B) : Type ≔ Σ (B → A) (s ↦ Id (B → B) (b ↦ f (s b)) (b ↦ b))

def sections_dependent_equiv (A B : Type) (f : A → B)
  : Equiv (SectionsOf A B f) ((b : B) → Σ A (a ↦ Id B b (f a)))
  ≔ compose_equiv (SectionsOf A B f) (Σ (B → A) (s ↦ (b : B) → Id B b (f (s b)))) ((b : B) → Σ A (a ↦ Id B b (f a)))
      (family_equiv (B → A) (s ↦ Id (B → B) (b ↦ f (s b)) (b ↦ b)) (s ↦ (b : B) → Id B b (f (s b)))
        (s ↦ compose_equiv (Id (B → B) (b ↦ f (s b)) (b ↦ b)) (Homotopy B (_ ↦ B) (b ↦ f (s b)) (b ↦ b))
          ((b : B) → Id B b (f (s b)))
          (function_extensionality B (_ ↦ B) (b ↦ f (s b)) (b ↦ b))
          (pi_family_equiv B (b ↦ Id B (f (s b)) b) (b ↦ Id B b (f (s b))) (b ↦ inverse_path_equiv B (f (s b)) b))))
      (canonical_inverse_equiv ((b : B) → Σ A (a ↦ Id B b (f a))) (Σ (B → A) (s ↦ (b : B) → Id B b (f (s b))))
        (choice_equiv B (_ ↦ A) (b a ↦ Id B b (f a))))

{` ev_{X÷,Y} : (X÷ = Y) → Y, transport of the point (refl ↦ pt_X up to the
   lifting path). `}
def type_evaluation (X : Pointed) (Y : Type) (r : Id Type (X .carrier) Y) : Y ≔ r .trr (X .point)

def pointed_equiv_evaluation_fiber_equiv (X : Pointed) (Y : Type) (y : Y)
  : Equiv (BookPointedEquiv (Y, y) X) (Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))
  ≔ let Pp ≔ Σ (Id Type (X .carrier) Y) (r ↦ Id ((Z ↦ Z) : Type → Type) r (X .point) y) in
    compose_equiv (BookPointedEquiv (Y, y) X) (Id Pointed (Y, y) X)
      (Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))
      (canonical_inverse_equiv (Id Pointed (Y, y) X) (BookPointedEquiv (Y, y) X) (pointed_path_equiv (Y, y) X))
      (compose_equiv (Id Pointed (Y, y) X) (Id Pointed X (Y, y))
        (Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))
        (inverse_path_equiv Pointed (Y, y) X)
        (compose_equiv (Id Pointed X (Y, y)) Pp (Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))
          (quasi_inverse_equiv (Id Pointed X (Y, y)) Pp (q ↦ (q .carrier, q .point)) (w ↦ (w .fst, w .snd))
            (q ↦ refl q) (w ↦ refl w))
          (family_equiv (Id Type (X .carrier) Y) (r ↦ Id ((Z ↦ Z) : Type → Type) r (X .point) y)
            (r ↦ Id Y y (type_evaluation X Y r))
            (r ↦ compose_equiv (Id ((Z ↦ Z) : Type → Type) r (X .point) y) (Id Y (r .trr (X .point)) y)
              (Id Y y (r .trr (X .point)))
              (pathover_transport_equiv Type (Z ↦ Z) (X .carrier) Y r (X .point) y)
              (inverse_path_equiv Y (r .trr (X .point)) y)))))

{` The displayed equivalence TX ≃ Σ(Y : U) ‖Y‖ × sec(ev_{X÷,Y}). `}
def warn_torsor_fibers_equiv (X : Pointed)
  : Equiv (WarnTorsor X)
      (Σ Type (Y ↦ Product (Mere Y) ((y : Y) → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))))
  ≔ family_equiv Type (Y ↦ Product (Mere Y) ((y : Y) → BookPointedEquiv (Y, y) X))
      (Y ↦ Product (Mere Y) ((y : Y) → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r))))
      (Y ↦ product_equiv (Mere Y) ((y : Y) → BookPointedEquiv (Y, y) X)
        (Mere Y) ((y : Y) → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))
        (identity_equiv (Mere Y))
        (pi_family_equiv Y (y ↦ BookPointedEquiv (Y, y) X)
          (y ↦ Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))
          (pointed_equiv_evaluation_fiber_equiv X Y)))

def warn_torsor_sections_equiv (X : Pointed)
  : Equiv (WarnTorsor X)
      (Σ Type (Y ↦ Product (Mere Y) (SectionsOf (Id Type (X .carrier) Y) Y (type_evaluation X Y))))
  ≔ compose_equiv (WarnTorsor X)
      (Σ Type (Y ↦ Product (Mere Y) ((y : Y) → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))))
      (Σ Type (Y ↦ Product (Mere Y) (SectionsOf (Id Type (X .carrier) Y) Y (type_evaluation X Y))))
      (warn_torsor_fibers_equiv X)
      (family_equiv Type
        (Y ↦ Product (Mere Y) ((y : Y) → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r))))
        (Y ↦ Product (Mere Y) (SectionsOf (Id Type (X .carrier) Y) Y (type_evaluation X Y)))
        (Y ↦ product_equiv (Mere Y) ((y : Y) → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))
          (Mere Y) (SectionsOf (Id Type (X .carrier) Y) Y (type_evaluation X Y))
          (identity_equiv (Mere Y))
          (canonical_inverse_equiv (SectionsOf (Id Type (X .carrier) Y) Y (type_evaluation X Y))
            ((y : Y) → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r)))
            (sections_dependent_equiv (Id Type (X .carrier) Y) Y (type_evaluation X Y)))))

{` Central pointed types (footnote to lem:warn-abelian-group, after BCFR):
   ev restricted to the component of refl in X÷ = X÷ is an equivalence. For
   X = BG this is the statement that z_G is an isomorphism, i.e. that G is
   abelian (def:abelian-groups). `}
def IsCentral (X : Pointed) : Type
  ≔ BookIsEquiv (NativeComponent (Id Type (X .carrier) (X .carrier)) (refl (X .carrier))) (X .carrier)
      (u ↦ u .fst .trr (X .point))

def abelian_bg_central (G : Group) (h : IsAbelian G) : IsCentral (BG G) ≔ abelian_center_inclusion_iso G h

{` For central X, ev restricted to the component of any p : X÷ = Y is an
   equivalence (by induction on p). `}
def central_component_evaluation_equiv (X : Pointed) (c : IsCentral X) (Y : Type) (p : Id Type (X .carrier) Y)
  : BookIsEquiv (NativeComponent (Id Type (X .carrier) Y) p) Y (u ↦ type_evaluation X Y (u .fst))
  ≔ J Type (X .carrier)
      (Y p ↦ BookIsEquiv (NativeComponent (Id Type (X .carrier) Y) p) Y (u ↦ type_evaluation X Y (u .fst)))
      c Y p

{` The map f_Y : ‖Y‖ × Π(y : Y) ev⁻¹(y) → ‖X÷ = Y‖₀, sending (!, s) to the
   component containing all s(y) (Y is connected, being merely X÷). `}
def EvaluationFibers (X : Pointed) (Y : Type) : Type
  ≔ (y : Y) → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r))

def evaluation_sections_connected (X : Pointed) (hX : Connected (X .carrier)) (Y : Type) (s : EvaluationFibers X Y) (y : Y)
  : Connected Y
  ≔ transport Type Connected (X .carrier) Y (s y .fst) hX

def evaluation_sections_component_constant (X : Pointed) (hX : Connected (X .carrier)) (Y : Type)
  (s : EvaluationFibers X Y)
  : WeaklyConstant Y (SetTrunc (Id Type (X .carrier) Y)) (y ↦ set_trunc (Id Type (X .carrier) Y) (s y .fst))
  ≔ y y' ↦ equiv_inverse_map
      (Id (SetTrunc (Id Type (X .carrier) Y)) (set_trunc (Id Type (X .carrier) Y) (s y .fst))
        (set_trunc (Id Type (X .carrier) Y) (s y' .fst)))
      (Mere (Id (Id Type (X .carrier) Y) (s y .fst) (s y' .fst)))
      (set_trunc_paths (Id Type (X .carrier) Y) (s y .fst) (s y' .fst))
      (trunc_map native_truncation (Id Y y y') (Id (Id Type (X .carrier) Y) (s y .fst) (s y' .fst))
        (q ↦ refl ((z ↦ s z .fst) : Y → Id Type (X .carrier) Y) q)
        (evaluation_sections_connected X hX Y s y .snd y y'))

def evaluation_sections_component (X : Pointed) (hX : Connected (X .carrier)) (Y : Type)
  (w : Product (Mere Y) (EvaluationFibers X Y)) : SetTrunc (Id Type (X .carrier) Y)
  ≔ weakly_constant_rec Y (SetTrunc (Id Type (X .carrier) Y)) (y ↦ set_trunc (Id Type (X .carrier) Y) (w .snd y .fst))
      (set_trunc_set (Id Type (X .carrier) Y)) (evaluation_sections_component_constant X hX Y (w .snd)) (w .fst)

{` The section attached to a component |p|₀: the inverse of ev on the
   component of p. `}
def component_section (X : Pointed) (c : IsCentral X) (Y : Type) (p : Id Type (X .carrier) Y) (y : Y)
  : BookFiber (NativeComponent (Id Type (X .carrier) Y) p) Y (u ↦ type_evaluation X Y (u .fst)) y
  ≔ central_component_evaluation_equiv X c Y p y .center

def component_evaluation_fibers (X : Pointed) (c : IsCentral X) (Y : Type) (p : Id Type (X .carrier) Y)
  : EvaluationFibers X Y
  ≔ y ↦ (component_section X c Y p y .fst .fst, component_section X c Y p y .snd)

{` Each fiber of f_Y over |p|₀ is contractible. `}
def evaluation_sections_fiber_contractible (X : Pointed) (hX : Connected (X .carrier)) (c : IsCentral X)
  (Y : Type) (p : Id Type (X .carrier) Y)
  : BookIsContr (BookFiber (Product (Mere Y) (EvaluationFibers X Y)) (SetTrunc (Id Type (X .carrier) Y))
      (evaluation_sections_component X hX Y) (set_trunc (Id Type (X .carrier) Y) p))
  ≔ let T ≔ SetTrunc (Id Type (X .carrier) Y) in
    let tp ≔ set_trunc (Id Type (X .carrier) Y) p in
    let D ≔ Product (Mere Y) (EvaluationFibers X Y) in
    let fY ≔ evaluation_sections_component X hX Y in
    let ev ≔ (u ↦ type_evaluation X Y (u .fst)) : NativeComponent (Id Type (X .carrier) Y) p → Y in
    let sp ≔ component_evaluation_fibers X c Y p in
    let in_component : (s : EvaluationFibers X Y) → (y : Y) → Id T tp (set_trunc (Id Type (X .carrier) Y) (s y .fst))
          → Mere (Id (Id Type (X .carrier) Y) p (s y .fst))
      ≔ s y e ↦ set_trunc_paths (Id Type (X .carrier) Y) p (s y .fst) .map e in
    let sp_comp : (y : Y) → Id T tp (set_trunc (Id Type (X .carrier) Y) (sp y .fst))
      ≔ y ↦ equiv_inverse_map (Id T tp (set_trunc (Id Type (X .carrier) Y) (sp y .fst)))
          (Mere (Id (Id Type (X .carrier) Y) p (sp y .fst)))
          (set_trunc_paths (Id Type (X .carrier) Y) p (sp y .fst)) (component_section X c Y p y .fst .snd) in
    let center_m ≔ mere Y (type_evaluation X Y p) in
    let center_e : Id T tp (fY (center_m, sp))
      ≔ concat T tp (set_trunc (Id Type (X .carrier) Y) (sp (type_evaluation X Y p) .fst)) (fY (center_m, sp))
          (sp_comp (type_evaluation X Y p))
          (inverse T (fY (center_m, sp)) (set_trunc (Id Type (X .carrier) Y) (sp (type_evaluation X Y p) .fst))
            (weakly_constant_rec_beta Y T (y ↦ set_trunc (Id Type (X .carrier) Y) (sp y .fst)) (set_trunc_set (Id Type (X .carrier) Y))
              (evaluation_sections_component_constant X hX Y sp) (type_evaluation X Y p))) in
    (((center_m, sp), center_e), t ↦
      let w ≔ t .fst in
      let s ≔ w .snd in
      let comp_y : (y : Y) → Id T tp (set_trunc (Id Type (X .carrier) Y) (s y .fst))
        ≔ y ↦ concat T tp (fY w) (set_trunc (Id Type (X .carrier) Y) (s y .fst)) (t .snd)
            (weakly_constant_rec_value Y T (z ↦ set_trunc (Id Type (X .carrier) Y) (s z .fst)) (set_trunc_set (Id Type (X .carrier) Y))
              (evaluation_sections_component_constant X hX Y s) (w .fst) y) in
      let sec_path : (y : Y) → Id (Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r))) (sp y) (s y)
        ≔ y ↦
          let F ≔ BookFiber (NativeComponent (Id Type (X .carrier) Y) p) Y ev y in
          let u1 : F ≔ component_section X c Y p y in
          let u2 : F ≔ ((s y .fst, in_component s y (comp_y y)), s y .snd) in
          let q : Id F u1 u2 ≔ contractible_prop F (native_contraction F (central_component_evaluation_equiv X c Y p y)) u1 u2 in
          refl ((v ↦ (v .fst .fst, v .snd)) : F → Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r))) q in
      subtype_equal D (v ↦ Id T tp (fY v)) (v ↦ set_trunc_set (Id Type (X .carrier) Y) tp (fY v))
        ((center_m, sp), center_e) t
        (mere_isprop Y center_m (w .fst),
         funext Y (y ↦ Σ (Id Type (X .carrier) Y) (r ↦ Id Y y (type_evaluation X Y r))) sp s sec_path))

def evaluation_sections_component_equiv (X : Pointed) (hX : Connected (X .carrier)) (c : IsCentral X) (Y : Type)
  : BookEquiv (Product (Mere Y) (EvaluationFibers X Y)) (SetTrunc (Id Type (X .carrier) Y))
  ≔ (evaluation_sections_component X hX Y, z ↦
      set_trunc_induction (Id Type (X .carrier) Y)
        (z ↦ BookIsContr (BookFiber (Product (Mere Y) (EvaluationFibers X Y)) (SetTrunc (Id Type (X .carrier) Y))
          (evaluation_sections_component X hX Y) z))
        (z ↦ prop_is_set (BookIsContr (BookFiber (Product (Mere Y) (EvaluationFibers X Y)) (SetTrunc (Id Type (X .carrier) Y))
            (evaluation_sections_component X hX Y) z))
          (book_iscontr_isprop (BookFiber (Product (Mere Y) (EvaluationFibers X Y)) (SetTrunc (Id Type (X .carrier) Y))
            (evaluation_sections_component X hX Y) z)))
        (evaluation_sections_fiber_contractible X hX c Y) z)

{` For connected central X: TX ≃ Σ(Y : U) ‖X÷ = Y‖₀ = Ũ_{X÷} U. `}
def central_warn_torsor_equiv (X : Pointed) (hX : Connected (X .carrier)) (c : IsCentral X)
  : Equiv (WarnTorsor X) (UnivCover Type (X .carrier))
  ≔ compose_equiv (WarnTorsor X) (Σ Type (Y ↦ Product (Mere Y) (EvaluationFibers X Y))) (UnivCover Type (X .carrier))
      (warn_torsor_fibers_equiv X)
      (family_equiv Type (Y ↦ Product (Mere Y) (EvaluationFibers X Y)) (Y ↦ SetTrunc (Id Type (X .carrier) Y))
        (Y ↦ native_equivalence (Product (Mere Y) (EvaluationFibers X Y)) (SetTrunc (Id Type (X .carrier) Y))
          (evaluation_sections_component_equiv X hX c Y)))

{` lem:warn-abelian-group: for abelian G, T(BG) can be identified with BB G. `}
def warn_abelian_torsor_equiv (G : Group) (h : IsAbelian G) : Equiv (WarnTorsor (BG G)) (BB G .carrier)
  ≔ central_warn_torsor_equiv (BG G) (bg_connected G) (abelian_bg_central G h)

def warn_abelian_torsor_path (G : Group) (h : IsAbelian G) : Id Type (WarnTorsor (BG G)) (BB G .carrier)
  ≔ ua (WarnTorsor (BG G)) (BB G .carrier) (warn_abelian_torsor_equiv G h)
