export "604-wild-pointed-types"
export "401-group-homomorphisms"

{` Chapter 6 (cats.tex), ex:loop-functor: taking loop types is a wild
   functor Ω : U_* → U_*. On a pointed map k : X →* Y (pointing path
   k_pt : pt_Y = k(pt_X)) the action is the map of def:loops-map,
   Ω k(p) = k_pt⁻¹ · ap_k(p) · k_pt, which in concatenation order is
   pointed_loop_conjugate (module 129): first k_pt, then ap_k(p), then
   k_pt⁻¹. Its pointing path refl = Ω k(refl) is an instance of the inverse
   law, obtained by path induction on k_pt; at k_pt = refl it is the unit
   law (typal β-rule of J). The pointed type ΩX = (pt_X = pt_X, refl) is
   chapter 4's Omega and the action on maps is chapter 4's loops_map
   (modules 400/401). The pointing path is constructed here by path
   induction (loop_conj_unit) rather than reusing loops_map_point, because
   the functor-law proofs below use its β-rule at k_pt = refl. `}

{` The unit law for conjugation by refl, and the inverse law for
   conjugating refl. `}
def loop_conj_refl (A : Type) (a : A) (l : Id A a a)
  : Id (Id A a a) (pointed_loop_conjugate A a a (refl a) l) l
  ≔ concat (Id A a a) (pointed_loop_conjugate A a a (refl a) l) (concat A a a a l (inverse A a a (refl a))) l
      (concat_1p A a a (concat A a a a l (inverse A a a (refl a))))
      (concat (Id A a a) (concat A a a a l (inverse A a a (refl a))) (concat A a a a l (refl a)) l
        (refl (concat A a a a l) (inverse_refl A a))
        (concat_p1 A a a l))

def loop_conj_unit (A : Type) (a x : A) (p : Id A a x)
  : Id (Id A a a) (pointed_loop_conjugate A a x p (refl x)) (refl a)
  ≔ J A a (x p ↦ Id (Id A a a) (pointed_loop_conjugate A a x p (refl x)) (refl a))
      (loop_conj_refl A a (refl a)) x p

def loop_conj_unit_refl (A : Type) (a : A)
  : Id (Id (Id A a a) (pointed_loop_conjugate A a a (refl a) (refl a)) (refl a))
      (loop_conj_refl A a (refl a)) (loop_conj_unit A a a (refl a))
  ≔ Jβ A a (x p ↦ Id (Id A a a) (pointed_loop_conjugate A a x p (refl x)) (refl a)) (loop_conj_refl A a (refl a))

{` ex:loop-functor: Ω k with its pointing path
   pt_{ΩY} = refl ⟶ k_pt⁻¹ · refl · k_pt = Ω k(pt_{ΩX}). `}
def loop_functor_map (X Y : Pointed) (k : BookPointedMap X Y) : BookPointedMap (Omega X) (Omega Y)
  ≔ (loops_map X Y k,
     inverse (Loop Y) (pointed_loop_conjugate (Y .carrier) (Y .point) (k .fst (X .point)) (k .snd) (refl (k .fst (X .point))))
       (refl (Y .point))
       (loop_conj_unit (Y .carrier) (Y .point) (k .fst (X .point)) (k .snd)))

{` For a strictly pointed map (pointing path refl), Ω k is ap_k with the
   pointing path refl (cf. rem:loops-map), as pointed maps. `}
def loop_functor_strict (A B : Type) (a : A) (f : A → B)
  : Id (BookPointedMap (Omega (A, a)) (Omega (B, f a)))
      (loop_functor_map (A, a) (B, f a) (f, refl (f a)))
      (l ↦ refl f l, refl (refl (f a)))
  ≔ let b ≔ f a in
    let L ≔ Id B b b in
    let x0 ≔ pointed_loop_conjugate B b b (refl b) (refl b) in
    let U0 ≔ loop_conj_unit B b b (refl b) in
    let K0 ≔ loop_conj_refl B b (refl b) in
    let F ≔ loop_functor_map (A, a) (B, b) (f, refl b) in
    let G : BookPointedMap (Omega (A, a)) (Omega (B, b)) ≔ (l ↦ refl f l, refl (refl b)) in
    equiv_inverse_map (Id (BookPointedMap (Omega (A, a)) (Omega (B, b))) F G)
      (PointedHomotopy (Omega (A, a)) (Omega (B, b)) F G)
      (pointed_map_path_equiv (Omega (A, a)) (Omega (B, b)) F G)
      (l ↦ loop_conj_refl B b (refl f l),
       concat (Id L (refl b) (refl b))
         (concat L (refl b) x0 (refl b) (inverse L x0 (refl b) U0) K0)
         (concat L (refl b) x0 (refl b) (inverse L x0 (refl b) U0) U0)
         (refl (refl b))
         (refl (concat L (refl b) x0 (refl b) (inverse L x0 (refl b) U0)) (loop_conj_unit_refl B b))
         (concat_inverse_left L x0 (refl b) U0))

{` Functoriality: Ω id = id. `}
def loop_functor_map_id (X : Pointed)
  : Id (BookPointedMap (Omega X) (Omega X)) (loop_functor_map X X (book_pointed_identity X))
      (book_pointed_identity (Omega X))
  ≔ loop_functor_strict (X .carrier) (X .carrier) (X .point) (identity (X .carrier))

{` Functoriality: Ω(g ∘ f) = Ω g ∘ Ω f, first for strictly pointed maps,
   then in general by path induction on the pointing paths (with fixed
   endpoints f(a) and g(b)). `}
def loop_functor_end_induction (A : Type) (y : A) (P : (x : A) → Id A x y → Type) (base : P y (refl y))
  (x : A) (p : Id A x y) : P x p
  ≔ transport (Id A x y) (P x) (inverse A y x (inverse A x y p)) p (inverse_inverse A x y p)
      (J A y (x' r ↦ P x' (inverse A y x' r))
        (transport (Id A y y) (P y) (refl y) (inverse A y y (refl y))
          (inverse (Id A y y) (inverse A y y (refl y)) (refl y) (inverse_refl A y)) base)
        x (inverse A x y p))

def LoopFunctorCompStatement (A B C : Type) (a : A) (f : A → B) (g : B → C) (b : B) (p : Id B b (f a))
  (c : C) (q : Id C c (g b)) : Type
  ≔ Id (BookPointedMap (Omega (A, a)) (Omega (C, c)))
      (loop_functor_map (A, a) (C, c) (book_pointed_compose (A, a) (B, b) (C, c) (f, p) (g, q)))
      (book_pointed_compose (Omega (A, a)) (Omega (B, b)) (Omega (C, c))
        (loop_functor_map (A, a) (B, b) (f, p)) (loop_functor_map (B, b) (C, c) (g, q)))

def loop_functor_comp_strict (A B C : Type) (a : A) (f : A → B) (g : B → C)
  : LoopFunctorCompStatement A B C a f g (f a) (refl (f a)) (g (f a)) (refl (g (f a)))
  ≔ let b ≔ f a in
    let c ≔ g b in
    let OA ≔ Omega (A, a) in
    let OB ≔ Omega (B, b) in
    let OC ≔ Omega (C, c) in
    let M ≔ BookPointedMap OA OC in
    let gf : A → C ≔ x ↦ g (f x) in
    let m0 ≔ loop_functor_map (A, a) (C, c) (gf, concat C c c c (refl c) (refl c)) in
    let m1 ≔ loop_functor_map (A, a) (C, c) (gf, refl c) in
    let m2 : M ≔ (l ↦ refl gf l, refl (refl c)) in
    let m3 ≔ book_pointed_compose OA OB OC (l ↦ refl f l, refl (refl b)) (l ↦ refl g l, refl (refl c)) in
    let m4 ≔ book_pointed_compose OA OB OC (loop_functor_map (A, a) (B, b) (f, refl b))
      (loop_functor_map (B, b) (C, c) (g, refl c)) in
    let e1 : Id M m0 m1
      ≔ refl ((r ↦ loop_functor_map (A, a) (C, c) (gf, r)) : Id C c c → M) (concat_p1 C c c (refl c)) in
    let e2 : Id M m1 m2 ≔ loop_functor_strict A C a gf in
    let e3 : Id M m2 m3
      ≔ (refl ((l ↦ refl g (refl f l)) : Id A a a → Id C c c),
         inverse (Id (Id C c c) (refl c) (refl c))
           (concat (Id C c c) (refl c) (refl c) (refl c) (refl (refl c)) (refl (refl c))) (refl (refl c))
           (concat_p1 (Id C c c) (refl c) (refl c) (refl (refl c)))) in
    let e4 : Id M m3 m4
      ≔ refl ((u v ↦ book_pointed_compose OA OB OC u v) : BookPointedMap OA OB → BookPointedMap OB OC → M)
          (inverse (BookPointedMap OA OB) (loop_functor_map (A, a) (B, b) (f, refl b)) (l ↦ refl f l, refl (refl b))
            (loop_functor_strict A B a f))
          (inverse (BookPointedMap OB OC) (loop_functor_map (B, b) (C, c) (g, refl c)) (l ↦ refl g l, refl (refl c))
            (loop_functor_strict B C b g)) in
    concat M m0 m1 m4 e1 (concat M m1 m2 m4 e2 (concat M m2 m3 m4 e3 e4))

def loop_functor_comp_general (A B C : Type) (a : A) (f : A → B) (g : B → C) (b : B) (p : Id B b (f a))
  (c : C) (q : Id C c (g b)) : LoopFunctorCompStatement A B C a f g b p c q
  ≔ loop_functor_end_induction C (g b) (c q ↦ LoopFunctorCompStatement A B C a f g b p c q)
      (loop_functor_end_induction B (f a) (b p ↦ LoopFunctorCompStatement A B C a f g b p (g b) (refl (g b)))
        (loop_functor_comp_strict A B C a f g) b p)
      c q

def LoopFunctor : WildFunctor PointedWild PointedWild
  ≔ (obj ≔ Omega,
     mor ≔ X Y k ↦ loop_functor_map X Y k,
     map_id ≔ X ↦ loop_functor_map_id X,
     map_comp ≔ X Y Z f g ↦ loop_functor_comp_general (X .carrier) (Y .carrier) (Z .carrier) (X .point)
       (f .fst) (g .fst) (Y .point) (f .snd) (Z .point) (g .snd))

{` Litmus checks: the action on maps is the book's formula of
   def:loops-map, and the pointing path has the displayed type
   refl = Ω k(refl). `}
def loop_functor_formula (X Y : Pointed) (k : BookPointedMap X Y) (l : Loop X)
  : Id (Loop Y) (LoopFunctor .mor X Y k .fst l)
      (concat (Y .carrier) (Y .point) (k .fst (X .point)) (Y .point) (k .snd)
        (concat (Y .carrier) (k .fst (X .point)) (k .fst (X .point)) (Y .point) (refl (k .fst) l)
          (inverse (Y .carrier) (Y .point) (k .fst (X .point)) (k .snd))))
  ≔ refl (LoopFunctor .mor X Y k .fst l)

def loop_functor_pointing (X Y : Pointed) (k : BookPointedMap X Y)
  : Id (Loop Y) (refl (Y .point)) (LoopFunctor .mor X Y k .fst (refl (X .point)))
  ≔ LoopFunctor .mor X Y k .snd

def loop_functor_bool_object : Id Type (LoopFunctor .obj pointed_bool_true .carrier) (Id Bool true. true.)
  ≔ refl (Id Bool true. true.)
