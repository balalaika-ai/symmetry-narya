export "04-ev-sections"

{` Blind statements, chapter 13 (fields.tex): def:O-functor, xca:O-functor,
   rem:pointing-ev, con:Omega-O. The circle S¹ is any CircleSignature C
   (circle_pointed C = (S¹, base)). `}

{` def:O-functor: O A ≔ (S¹ →* A), pointed at (cst_{pt_A}, refl). `}
def blind_O (C : CircleSignature) (A : Pointed) : Pointed
  ≔ blind_ptd_maps (circle_pointed C) A

{` The comparison path ρ_{f_pt} used to point O(f). In the book
   O(pt_{OA}) ≡ (cst_{f(pt_A)}, f_pt); in Narya the pointing path of the
   composite f ∘ (cst, refl) is concat f_pt refl, so the second component
   of the Σ-path ends at concat f_pt refl and the book's ρ_{f_pt} :
   f_pt·refl = f_pt (concat refl f_pt = f_pt) is followed by the inverse
   right unit law. `}
def blind_O_rho (B : Type) (b x : B) (q : Id B b x)
  : Id (Id B b x) (concat B b b x (refl b) q) (concat B b x x q (refl x))
  ≔ concat (Id B b x) (concat B b b x (refl b) q) q (concat B b x x q (refl x))
      (concat_1p B b x q) (inverse (Id B b x) (concat B b x x q (refl x)) q (concat_p1 B b x q))

{` The path (f_pt, ρ_{f_pt}) : (pt_B, refl) = (f(pt_A), f_pt·refl) in Σ_{x:B} (pt_B = x). `}
def blind_O_sigma_path (B : Type) (b x : B) (q : Id B b x)
  : Id (Σ B (z ↦ Id B b z)) (b, refl b) (x, concat B b x x q (refl x))
  ≔ (q, pathover_of_eq B (z ↦ Id B b z) b x q (refl b) (concat B b x x q (refl x)) (blind_O_rho B b x q))

{` O(f)_pt ≔ ap_{cst_*}(f_pt, ρ_{f_pt}). `}
def blind_O_map_pt (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap (circle_pointed C) B) (book_pointed_constant (circle_pointed C) B)
      (book_pointed_compose (circle_pointed C) A B (book_pointed_constant (circle_pointed C) A) f)
  ≔ refl (blind_cst_ptd (circle_pointed C) B)
      (blind_O_sigma_path (B .carrier) (B .point) (f .fst (A .point)) (f .snd))

{` def:O-functor: O(f)(g) ≔ f ∘ g (pointed composite), pointed by O(f)_pt. `}
def blind_O_map (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
  : BookPointedMap (blind_O C A) (blind_O C B)
  ≔ (g ↦ book_pointed_compose (circle_pointed C) A B g f, blind_O_map_pt C A B f)

{` xca:O-functor, part 1: O is a wild functor (U_* → U_*): the identity and
   composition laws (the fields map_id, map_comp of WildFunctor for
   PointedWild, with obj ≔ O and mor ≔ O(-)). `}
def blind_xca_O_functor_wild : Type
  ≔ (C : CircleSignature)
    → Product
        ((A : Pointed) → Id (BookPointedMap (blind_O C A) (blind_O C A))
          (blind_O_map C A A (book_pointed_identity A)) (book_pointed_identity (blind_O C A)))
        ((A B D : Pointed) (f : BookPointedMap A B) (g : BookPointedMap B D)
          → Id (BookPointedMap (blind_O C A) (blind_O C D))
              (blind_O_map C A D (book_pointed_compose A B D f g))
              (book_pointed_compose (blind_O C A) (blind_O C B) (blind_O C D)
                (blind_O_map C A B f) (blind_O_map C B D g)))

{` xca:O-functor, part 2: O(f)_pt = ptw_*^{-1}(cst_{f_pt}, ρ_{f_pt}). `}
def blind_xca_O_functor_pt : Type
  ≔ (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
    → let S ≔ circle_pointed C in
      let c ≔ book_pointed_constant S B in
      let Ofc ≔ book_pointed_compose S A B (book_pointed_constant S A) f in
      Id (Id (BookPointedMap S B) c Ofc)
        (blind_O_map_pt C A B f)
        (equiv_inverse_map (Id (BookPointedMap S B) c Ofc) (PointedHomotopy S B c Ofc)
          (pointed_map_path_equiv S B c Ofc)
          ((_ ↦ f .snd), blind_O_rho (B .carrier) (B .point) (f .fst (A .point)) (f .snd)))

{` rem:pointing-ev: ε_A(p) : refl = cst_{pt_A}(p)·refl for p : base = z, by
   path induction. The book's base case is refl (the endpoints agree
   judgmentally there); in Narya the base case is the path-algebra
   identification refl = refl·refl·refl⁻¹ of the conjugation formula of ev. `}
def blind_eps_base (A : Pointed)
  : Id (Loop A) (refl (A .point))
      (concat (A .carrier) (A .point) (A .point) (A .point) (refl (A .point))
        (concat (A .carrier) (A .point) (A .point) (A .point) (refl (A .point))
          (inverse (A .carrier) (A .point) (A .point) (refl (A .point)))))
  ≔ let a ≔ A .point in let T ≔ A .carrier in
    inverse (Loop A)
      (concat T a a a (refl a) (concat T a a a (refl a) (inverse T a a (refl a)))) (refl a)
      (concat (Loop A)
        (concat T a a a (refl a) (concat T a a a (refl a) (inverse T a a (refl a))))
        (concat T a a a (refl a) (inverse T a a (refl a))) (refl a)
        (concat_1p T a a (concat T a a a (refl a) (inverse T a a (refl a))))
        (concat (Loop A) (concat T a a a (refl a) (inverse T a a (refl a))) (inverse T a a (refl a)) (refl a)
          (concat_1p T a a (inverse T a a (refl a))) (inverse_refl T a)))

def blind_eps (C : CircleSignature) (A : Pointed) (z : C .carrier) (p : Id (C .carrier) (C .base) z)
  : Id (Loop A) (refl (A .point))
      (concat (A .carrier) (A .point) (A .point) (A .point) (refl (A .point))
        (concat (A .carrier) (A .point) (A .point) (A .point)
          (refl (constant (C .carrier) (A .carrier) (A .point)) p)
          (inverse (A .carrier) (A .point) (A .point) (refl (A .point)))))
  ≔ J (C .carrier) (C .base)
      (z p ↦ Id (Loop A) (refl (A .point))
        (concat (A .carrier) (A .point) (A .point) (A .point) (refl (A .point))
          (concat (A .carrier) (A .point) (A .point) (A .point)
            (refl (constant (C .carrier) (A .carrier) (A .point)) p)
            (inverse (A .carrier) (A .point) (A .point) (refl (A .point))))))
      (blind_eps_base A) z p

{` rem:pointing-ev: ev_A : (S¹ →* A) → ΩA, f ↦ Ω(f)(loop) = f_pt⁻¹·f(loop)·f_pt
   (cor:circle-loopspace, pointed_circle_loop_eval), pointed by
   (ev_A)_pt ≔ ε_A(loop). `}
def blind_ev (C : CircleSignature) (A : Pointed) : BookPointedMap (blind_O C A) (Omega A)
  ≔ (pointed_circle_loop_eval C (A .carrier) (A .point), blind_eps C A (C .base) (C .loop))

{` rem:pointing-ev, the recalled claims: ev_A is an equivalence, and its
   inverse sends p to the map with base ↦ pt_A, loop ↦ p, pointed by the
   (here propositional) base computation (pointed_circle_loop_rec). `}
def blind_rem_pointing_ev : Type
  ≔ (C : CircleSignature) (A : Pointed)
    → Product (BookIsEquiv (blind_O C A .carrier) (Loop A) (blind_ev C A .fst))
        ((p : Loop A) → Id (Loop A) (blind_ev C A .fst (pointed_circle_loop_rec C (A .carrier) (A .point) p)) p)

{` con:Omega-O: Ω(f) ∘ ev_A = ev_B ∘ O(f) as pointed maps OA →* ΩB. `}
def blind_con_Omega_O_square : Type
  ≔ (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
    → Id (BookPointedMap (blind_O C A) (Omega B))
        (book_pointed_compose (blind_O C A) (Omega A) (Omega B) (blind_ev C A) (loops_pointed_map A B f))
        (book_pointed_compose (blind_O C A) (blind_O C B) (Omega B) (blind_O_map C A B f) (blind_ev C B))

{` con:Omega-O, consequences: e ≔ ev_B^{-1} ∘ - ∘ ev_A is an equivalence
   (ΩA →* ΩB) ≃ (OA →* OB), and O = e ∘ Ω on A →* B. Since the book gives
   no pointing of ev_B^{-1}, e is characterised by ev_B ∘ e(φ) = φ ∘ ev_A
   (which determines e(φ) because ev_B is an equivalence). `}
def blind_con_Omega_O_equiv : Type
  ≔ (C : CircleSignature) (A B : Pointed)
    → Σ (BookEquiv (BookPointedMap (Omega A) (Omega B)) (BookPointedMap (blind_O C A) (blind_O C B)))
        (e ↦ Product
          ((φ : BookPointedMap (Omega A) (Omega B))
            → Id (BookPointedMap (blind_O C A) (Omega B))
                (book_pointed_compose (blind_O C A) (blind_O C B) (Omega B) (e .map φ) (blind_ev C B))
                (book_pointed_compose (blind_O C A) (Omega A) (Omega B) (blind_ev C A) φ))
          (Id (BookPointedMap A B → BookPointedMap (blind_O C A) (blind_O C B))
            (blind_O_map C A B) (f ↦ e .map (loops_pointed_map A B f))))
