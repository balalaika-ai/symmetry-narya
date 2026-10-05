export "07-rezk"

{` Blind statements, chapter 6, section "Limits and colimits". `}

{` def:prod-in-a-cat. A cone (P, p1, p2) over A, B and its universal property:
   for every cone (X, x1, x2) a unique f : X → P with x_i = p_i ∘ f. `}
def BlindCone (C : BlindWildPrecat) (A B : C .ob) : Type
  ≔ Σ (C .ob) (P ↦ Product (C .hom P A) (C .hom P B))

def BlindConeHom (C : BlindWildPrecat) (A B : C .ob) (x p : BlindCone C A B) : Type
  ≔ Σ (C .hom (x .fst) (p .fst)) (f ↦
      Product (Id (C .hom (x .fst) A) (x .snd .fst) (C .comp (x .fst) (p .fst) A (p .snd .fst) f))
        (Id (C .hom (x .fst) B) (x .snd .snd) (C .comp (x .fst) (p .fst) B (p .snd .snd) f)))

def BlindIsProductCone (C : BlindWildPrecat) (A B : C .ob) (p : BlindCone C A B) : Type
  ≔ (X : C .ob) (x1 : C .hom X A) (x2 : C .hom X B) → BookIsContr (BlindConeHom C A B (X, (x1, x2)) p)

def BlindProductCone (C : BlindWildPrecat) (A B : C .ob) : Type
  ≔ Σ (BlindCone C A B) (BlindIsProductCone C A B)

{` xca:product-cone-prop. `}
def blind_xca_product_cone_prop : Type
  ≔ (C : BlindWildPrecat) → BlindIsUnivalent C → (A B : C .ob) → isProp (BlindProductCone C A B)

{` def:product-cones-as-terminal. The (pre)category of cones over A, B in a
   precategory C (for a wild C the associativity of filled triangles would
   need coherences, as for slices). `}
def blind_cone_hom_path (C : BlindPrecat) (A B : C .fst .ob) (x p : BlindCone (C .fst) A B)
  (m n : BlindConeHom (C .fst) A B x p) (q : Id (C .fst .hom (x .fst) (p .fst)) (m .fst) (n .fst))
  : Id (BlindConeHom (C .fst) A B x p) m n
  ≔ let W ≔ C .fst in
    equiv_inverse_map (Id (BlindConeHom W A B x p) m n) (Id (W .hom (x .fst) (p .fst)) (m .fst) (n .fst))
      (subtype_path_equiv (W .hom (x .fst) (p .fst))
        (f ↦ Product (Id (W .hom (x .fst) A) (x .snd .fst) (W .comp (x .fst) (p .fst) A (p .snd .fst) f))
          (Id (W .hom (x .fst) B) (x .snd .snd) (W .comp (x .fst) (p .fst) B (p .snd .snd) f)))
        (f ↦ sigma_prop (Id (W .hom (x .fst) A) (x .snd .fst) (W .comp (x .fst) (p .fst) A (p .snd .fst) f))
          (_ ↦ Id (W .hom (x .fst) B) (x .snd .snd) (W .comp (x .fst) (p .fst) B (p .snd .snd) f))
          (C .snd (x .fst) A (x .snd .fst) (W .comp (x .fst) (p .fst) A (p .snd .fst) f))
          (_ ↦ C .snd (x .fst) B (x .snd .snd) (W .comp (x .fst) (p .fst) B (p .snd .snd) f)))
        m n) q

def blind_cone_leg (C : BlindWildPrecat) (Z : C .ob) (X Y P : C .ob) (x : C .hom X Z) (y : C .hom Y Z)
  (p : C .hom P Z) (f : C .hom X Y) (g : C .hom Y P)
  (e1 : Id (C .hom X Z) x (C .comp X Y Z y f)) (e2 : Id (C .hom Y Z) y (C .comp Y P Z p g))
  : Id (C .hom X Z) x (C .comp X P Z p (C .comp X Y P g f))
  ≔ concat (C .hom X Z) x (C .comp X Y Z y f) (C .comp X P Z p (C .comp X Y P g f)) e1
      (concat (C .hom X Z) (C .comp X Y Z y f) (C .comp X Y Z (C .comp Y P Z p g) f) (C .comp X P Z p (C .comp X Y P g f))
        (refl (k ↦ C .comp X Y Z k f) e2)
        (inverse (C .hom X Z) (C .comp X P Z p (C .comp X Y P g f)) (C .comp X Y Z (C .comp Y P Z p g) f)
           (C .assoc X Y P Z f g p)))

def blind_cone_comp (C : BlindWildPrecat) (A B : C .ob) (x y p : BlindCone C A B)
  (g : BlindConeHom C A B y p) (f : BlindConeHom C A B x y) : BlindConeHom C A B x p
  ≔ (C .comp (x .fst) (y .fst) (p .fst) (g .fst) (f .fst),
     (blind_cone_leg C A (x .fst) (y .fst) (p .fst) (x .snd .fst) (y .snd .fst) (p .snd .fst) (f .fst) (g .fst)
        (f .snd .fst) (g .snd .fst),
      blind_cone_leg C B (x .fst) (y .fst) (p .fst) (x .snd .snd) (y .snd .snd) (p .snd .snd) (f .fst) (g .fst)
        (f .snd .snd) (g .snd .snd)))

def blind_cone_id (C : BlindWildPrecat) (A B : C .ob) (x : BlindCone C A B) : BlindConeHom C A B x x
  ≔ (C .idn (x .fst),
     (inverse (C .hom (x .fst) A) (C .comp (x .fst) (x .fst) A (x .snd .fst) (C .idn (x .fst))) (x .snd .fst)
        (C .runit (x .fst) A (x .snd .fst)),
      inverse (C .hom (x .fst) B) (C .comp (x .fst) (x .fst) B (x .snd .snd) (C .idn (x .fst))) (x .snd .snd)
        (C .runit (x .fst) B (x .snd .snd))))

def blind_cone_precat (C : BlindPrecat) (A B : C .fst .ob) : BlindPrecat
  ≔ let W ≔ C .fst in
    ((BlindCone W A B, BlindConeHom W A B, blind_cone_id W A B, blind_cone_comp W A B,
      (x y f ↦ blind_cone_hom_path C A B x y (blind_cone_comp W A B x y y (blind_cone_id W A B y) f) f
         (W .lunit (x .fst) (y .fst) (f .fst))),
      (x y f ↦ blind_cone_hom_path C A B x y (blind_cone_comp W A B x x y f (blind_cone_id W A B x)) f
         (W .runit (x .fst) (y .fst) (f .fst))),
      (x y z w f g h ↦ blind_cone_hom_path C A B x w
         (blind_cone_comp W A B x z w h (blind_cone_comp W A B x y z g f))
         (blind_cone_comp W A B x y w (blind_cone_comp W A B y z w h g) f)
         (W .assoc (x .fst) (y .fst) (z .fst) (w .fst) (f .fst) (g .fst) (h .fst)))),
     (x p ↦ sigma_set (W .hom (x .fst) (p .fst))
        (f ↦ Product (Id (W .hom (x .fst) A) (x .snd .fst) (W .comp (x .fst) (p .fst) A (p .snd .fst) f))
          (Id (W .hom (x .fst) B) (x .snd .snd) (W .comp (x .fst) (p .fst) B (p .snd .snd) f)))
        (C .snd (x .fst) (p .fst))
        (f ↦ prop_is_set (Product (Id (W .hom (x .fst) A) (x .snd .fst) (W .comp (x .fst) (p .fst) A (p .snd .fst) f))
                (Id (W .hom (x .fst) B) (x .snd .snd) (W .comp (x .fst) (p .fst) B (p .snd .snd) f)))
           (sigma_prop (Id (W .hom (x .fst) A) (x .snd .fst) (W .comp (x .fst) (p .fst) A (p .snd .fst) f))
              (_ ↦ Id (W .hom (x .fst) B) (x .snd .snd) (W .comp (x .fst) (p .fst) B (p .snd .snd) f))
              (C .snd (x .fst) A (x .snd .fst) (W .comp (x .fst) (p .fst) A (p .snd .fst) f))
              (_ ↦ C .snd (x .fst) B (x .snd .snd) (W .comp (x .fst) (p .fst) B (p .snd .snd) f))))))

def blind_rem_product_cones_as_terminal : Type
  ≔ (C : BlindPrecat) (A B : C .fst .ob) (p : BlindCone (C .fst) A B)
    → Product (BlindIsProductCone (C .fst) A B p → BlindIsTerminal (blind_cone_precat C A B .fst) p)
        (BlindIsTerminal (blind_cone_precat C A B .fst) p → BlindIsProductCone (C .fst) A B p)

{` def:coprod-in-a-cat: unique f : C → X with x_j = f ∘ i_j. (The book refers
   to fig:product-cone(2); fig:coproduct-cone(2) is meant.) `}
def BlindCocone (C : BlindWildPrecat) (A B : C .ob) : Type
  ≔ Σ (C .ob) (Q ↦ Product (C .hom A Q) (C .hom B Q))

def BlindIsCoproductCocone (C : BlindWildPrecat) (A B : C .ob) (q : BlindCocone C A B) : Type
  ≔ (X : C .ob) (x1 : C .hom A X) (x2 : C .hom B X)
    → BookIsContr (Σ (C .hom (q .fst) X) (f ↦
        Product (Id (C .hom A X) x1 (C .comp A (q .fst) X f (q .snd .fst)))
          (Id (C .hom B X) x2 (C .comp B (q .fst) X f (q .snd .snd)))))

def BlindCoproductCocone (C : BlindWildPrecat) (A B : C .ob) : Type
  ≔ Σ (BlindCocone C A B) (BlindIsCoproductCocone C A B)

{` def:pullback. `}
def BlindPullback (B C D : Type) (f : B → D) (g : C → D) : Type
  ≔ Σ (Product B C) (bc ↦ Id D (f (bc .fst)) (g (bc .snd)))

def blind_pullback_pr1 (B C D : Type) (f : B → D) (g : C → D) (u : BlindPullback B C D f g) : B ≔ u .fst .fst
def blind_pullback_pr2 (B C D : Type) (f : B → D) (g : C → D) (u : BlindPullback B C D f g) : C ≔ u .fst .snd

{` xca:univpropofpullback. WRONG AS PRINTED: the image of (β, γ, p) is
   written a ↦ (f(a), g(a), p(a)), which is ill-typed (a : A, f : B → D); it
   must be a ↦ (β(a), γ(a), p(a)) with p(a) = happly p a. Only the corrected
   statement is given. `}
def blind_xca_univpropofpullback_corrected : Type
  ≔ (A B C D : Type) (f : B → D) (g : C → D)
    → BookIsEquiv
        (BlindPullback (A → B) (A → C) (A → D) (be ↦ a ↦ f (be a)) (ga ↦ a ↦ g (ga a)))
        (A → BlindPullback B C D f g)
        (u ↦ a ↦ ((u .fst .fst a, u .fst .snd a),
                  happly A (_ ↦ D) (a' ↦ f (u .fst .fst a')) (a' ↦ g (u .fst .snd a')) (u .snd) a))

{` Example after xca:univpropofpullback. TYPO AS PRINTED: the preimage is
   written Σ_{b:B} d = g(b) but g : C → D, so b : C is meant. `}
def blind_ex_preimage_pullback : Type
  ≔ (C D : Type) (d : D) (g : C → D)
    → BookEquiv (BlindPullback Unit C D (_ ↦ d) g) (BookFiber C D g d)
