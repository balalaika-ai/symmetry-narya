export "1332-circle-pointed-maps-functor"
export "401-group-homomorphisms"

{` Chapter 13 (fields.tex 426-602): the pointed evaluation equivalence
   ev_A : O A ≃* Ω A (rem:pointing-ev) and the comparison of Ω and O
   (con:Omega-O). The circle is an arbitrary CircleSignature C. `}

{` rem:pointing-ev. ev_A(f) = Ω(f)(loop) = f_pt⁻¹·f(loop)·f_pt (module 129;
   concatenation order f_pt, ap_f loop, f_pt⁻¹). `}
def pointed_circle_ev (C : CircleSignature) (A : Pointed) (f : BookPointedMap (circle_pointed C) A) : Loop A
  ≔ pointed_circle_loop_eval C (A .carrier) (A .point) f

def pointed_circle_ev_loops_map (C : CircleSignature) (A : Pointed) (f : BookPointedMap (circle_pointed C) A)
  : Id (Loop A) (pointed_circle_ev C A f) (loops_map (circle_pointed C) A f (C .loop))
  ≔ refl (pointed_circle_ev C A f)

{` ev_A is an equivalence (cor:circle-loopspace). Its inverse sends p to the
   map defined by circle recursion with f(base) = pt_A and f(loop) = p;
   since CircleSignature has propositional computation rules this map is
   pointed by the inverse of the base computation rule rather than by refl. `}
def pointed_circle_ev_book_equiv (C : CircleSignature) (A : Pointed)
  : BookIsEquiv (BookPointedMap (circle_pointed C) A) (Loop A) (pointed_circle_ev C A)
  ≔ pointed_circle_universal_property_book_map C (A .carrier) (A .point)

def pointed_circle_ev_inverse (C : CircleSignature) (A : Pointed) (p : Loop A) : BookPointedMap (circle_pointed C) A
  ≔ pointed_circle_loop_rec C (A .carrier) (A .point) p

def pointed_circle_ev_inverse_beta (C : CircleSignature) (A : Pointed) (p : Loop A)
  : Id (Loop A) (pointed_circle_ev C A (pointed_circle_ev_inverse C A p)) p
  ≔ pointed_circle_loop_rec_beta C (A .carrier) (A .point) p

{` ε_A(p) : refl = cst(p)·refl for p : base = z, by path induction. In
   Narya the value of ev_A at the constant map is the conjugate
   refl⁻¹·ap_cst(p)·refl (no judgmental unit laws), so the base case is the
   unit law of conjugation (loop_conjugate_unit) instead of refl_refl. `}
def pointed_circle_ev_pointing (C : CircleSignature) (A : Pointed) (z : C .carrier) (p : Id (C .carrier) (C .base) z)
  : Id (Loop A) (refl (A .point))
      (pointed_loop_conjugate (A .carrier) (A .point) (A .point) (refl (A .point))
        (refl (constant (C .carrier) (A .carrier) (A .point)) p))
  ≔ let X ≔ A .carrier in let a ≔ A .point in
    J (C .carrier) (C .base)
      (z p ↦ Id (Loop A) (refl a) (pointed_loop_conjugate X a a (refl a) (refl (constant (C .carrier) X a) p)))
      (inverse (Loop A) (pointed_loop_conjugate X a a (refl a) (refl a)) (refl a) (loop_conjugate_unit X a a (refl a)))
      z p

{` (ev_A)_pt ≔ ε_A(loop); ev_A as a pointed equivalence O A ≃* Ω A. `}
def pointed_circle_ev_pointed (C : CircleSignature) (A : Pointed)
  : BookPointedMap (circle_pointed_maps C A) (Omega A)
  ≔ (pointed_circle_ev C A, pointed_circle_ev_pointing C A (C .base) (C .loop))

def pointed_circle_ev_pointed_equiv (C : CircleSignature) (A : Pointed)
  : BookPointedEquiv (circle_pointed_maps C A) (Omega A)
  ≔ (pointed_circle_ev_pointed C A, pointed_circle_ev_book_equiv C A)

{` Induction on pointed equivalences out of X (their total type is
   contractible, module 162). `}
def pointed_equiv_induction (X : Pointed) (P : (Y : Pointed) → BookPointedEquiv X Y → Type)
  (d : P X (book_pointed_identity X, identity_book_equiv (X .carrier) .equiv))
  (Y : Pointed) (w : BookPointedEquiv X Y) : P Y w
  ≔ let T ≔ Σ Pointed (Y ↦ BookPointedEquiv X Y) in
    let h ≔ pointed_equivalences_total_contractible X in
    let i ≔ (X, (book_pointed_identity X, identity_book_equiv (X .carrier) .equiv)) : T in
    transport T (t ↦ P (t .fst) (t .snd)) i (Y, w)
      (concat T i (h .center) (Y, w) (inverse T (h .center) i (h .contract i)) (h .contract (Y, w))) d

{` Pre- and postcomposition with a pointed equivalence are equivalences. `}
def pointed_precompose_is_equiv (X Z : Pointed) (Y : Pointed) (w : BookPointedEquiv X Y)
  : isEquiv (BookPointedMap Y Z) (BookPointedMap X Z) (k ↦ book_pointed_compose X Y Z (w .fst) k)
  ≔ pointed_equiv_induction X
      (Y w ↦ isEquiv (BookPointedMap Y Z) (BookPointedMap X Z) (k ↦ book_pointed_compose X Y Z (w .fst) k))
      (quasi_inverse_equiv (BookPointedMap X Z) (BookPointedMap X Z)
        (k ↦ book_pointed_compose X X Z (book_pointed_identity X) k) (identity (BookPointedMap X Z))
        (k ↦ pointed_wild_ru X Z k) (k ↦ pointed_wild_ru X Z k) .equiv)
      Y w

def pointed_postcompose_is_equiv (X Y : Pointed) (Z : Pointed) (w : BookPointedEquiv Y Z)
  : isEquiv (BookPointedMap X Y) (BookPointedMap X Z) (k ↦ book_pointed_compose X Y Z k (w .fst))
  ≔ pointed_equiv_induction Y
      (Z w ↦ isEquiv (BookPointedMap X Y) (BookPointedMap X Z) (k ↦ book_pointed_compose X Y Z k (w .fst)))
      (quasi_inverse_equiv (BookPointedMap X Y) (BookPointedMap X Y)
        (k ↦ book_pointed_compose X Y Y k (book_pointed_identity Y)) (identity (BookPointedMap X Y))
        (k ↦ pointed_wild_lu X Y k) (k ↦ pointed_wild_lu X Y k) .equiv)
      Z w

{` con:Omega-O: Ω(f) ∘ ev_A = ev_B ∘ O(f) as pointed maps O A →* Ω B.
   Pointwise this is the functoriality of Ω (loops_map_compose_pointwise,
   the book's i(f, f_pt)(p, p_pt)). Instead of filling the pointing
   triangle by hand, the identification of pointed maps into the loop
   space Ω B is obtained from the pointwise one by cor:Id-(B->*loopsA)
   (module 1331), as the book itself does for con:ptw-swap-ptd-doms. `}
def omega_o_square (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap (circle_pointed_maps C A) (Omega B))
      (book_pointed_compose (circle_pointed_maps C A) (Omega A) (Omega B) (pointed_circle_ev_pointed C A) (loops_pointed_map A B f))
      (book_pointed_compose (circle_pointed_maps C A) (circle_pointed_maps C B) (Omega B)
        (o_functor_map C A B f) (pointed_circle_ev_pointed C B))
  ≔ let S ≔ circle_pointed C in
    loops_pointed_map_path_from_underlying B (circle_pointed_maps C A)
      (book_pointed_compose (circle_pointed_maps C A) (Omega A) (Omega B) (pointed_circle_ev_pointed C A) (loops_pointed_map A B f))
      (book_pointed_compose (circle_pointed_maps C A) (circle_pointed_maps C B) (Omega B)
        (o_functor_map C A B f) (pointed_circle_ev_pointed C B))
      (funext (BookPointedMap S A) (_ ↦ Loop B)
        (p ↦ loops_map A B f (loops_map S A p (C .loop)))
        (p ↦ loops_map S B (book_pointed_compose S A B p f) (C .loop))
        (p ↦ inverse (Loop B) (loops_map S B (book_pointed_compose S A B p f) (C .loop))
          (loops_map A B f (loops_map S A p (C .loop)))
          (loops_map_compose_pointwise S A B p f (C .loop))))

{` con:Omega-O, consequence: e ≔ ev_B⁻¹ ∘ - ∘ ev_A is an equivalence
   (Ω A →* Ω B) ≃ (O A →* O B). It is the composite of precomposition with
   ev_A and the inverse of postcomposition with ev_B (the book's ev_B⁻¹ ∘ -). `}
def omega_o_precompose_equiv (C : CircleSignature) (A B : Pointed)
  : Equiv (BookPointedMap (Omega A) (Omega B)) (BookPointedMap (circle_pointed_maps C A) (Omega B))
  ≔ ((k ↦ book_pointed_compose (circle_pointed_maps C A) (Omega A) (Omega B) (pointed_circle_ev_pointed C A) k),
     pointed_precompose_is_equiv (circle_pointed_maps C A) (Omega B) (Omega A) (pointed_circle_ev_pointed_equiv C A))

def omega_o_postcompose_equiv (C : CircleSignature) (A B : Pointed)
  : Equiv (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B)) (BookPointedMap (circle_pointed_maps C A) (Omega B))
  ≔ ((k ↦ book_pointed_compose (circle_pointed_maps C A) (circle_pointed_maps C B) (Omega B) k (pointed_circle_ev_pointed C B)),
     pointed_postcompose_is_equiv (circle_pointed_maps C A) (circle_pointed_maps C B) (Omega B) (pointed_circle_ev_pointed_equiv C B))

def omega_o_equiv (C : CircleSignature) (A B : Pointed)
  : Equiv (BookPointedMap (Omega A) (Omega B)) (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B))
  ≔ compose_equiv (BookPointedMap (Omega A) (Omega B)) (BookPointedMap (circle_pointed_maps C A) (Omega B))
      (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B))
      (omega_o_precompose_equiv C A B)
      (canonical_inverse_equiv (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B))
        (BookPointedMap (circle_pointed_maps C A) (Omega B)) (omega_o_postcompose_equiv C A B))

{` con:Omega-O, last claim: O = e ∘ Ω on A →* B. `}
def o_functor_omega (C : CircleSignature) (A B : Pointed)
  : Id (BookPointedMap A B → BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B))
      (o_functor_map C A B) (f ↦ omega_o_equiv C A B .map (loops_pointed_map A B f))
  ≔ let OAB ≔ BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B) in
    let OAΩ ≔ BookPointedMap (circle_pointed_maps C A) (Omega B) in
    let K ≔ omega_o_postcompose_equiv C A B in
    funext (BookPointedMap A B) (_ ↦ OAB) (o_functor_map C A B)
      (f ↦ omega_o_equiv C A B .map (loops_pointed_map A B f))
      (f ↦ concat OAB (o_functor_map C A B f) (equiv_inverse_map OAB OAΩ K (K .map (o_functor_map C A B f)))
        (omega_o_equiv C A B .map (loops_pointed_map A B f))
        (equiv_unit OAB OAΩ K (o_functor_map C A B f))
        (refl (equiv_inverse_map OAB OAΩ K)
          (inverse OAΩ (omega_o_precompose_equiv C A B .map (loops_pointed_map A B f)) (K .map (o_functor_map C A B f))
            (omega_o_square C A B f))))
