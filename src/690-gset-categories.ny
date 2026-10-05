export "664-set-sigma-pi-adjunctions"
export "500-gsets"

{` Chapter 6 examples involving G-sets (chapter 5 core): the category of
   G-sets (bullet after def:category), the functors f_!, f^*, f_* of
   ex:action-functors, and the adjunctions f_! ⊣ f^* ⊣ f_* of the prose
   before def:adjunction. G-sets are the families of sets over BG, so all
   of this is the instance A = BG, B = BH, f = Bf of the families of sets
   of modules 662-664; the identifications with the chapter-5 definitions
   (GSet, GSetHom, gset_hom_compose, gset_restrict, gset_induce,
   gset_coinduce) hold by refl. `}

{` Families of sets over A form a category: (P = Q) ≃ ∏_a (P a ≃ Q a) ≃
   (P ≅ Q), the isomorphisms being the fiberwise equivalences (as for
   FamilyWild in module 604). `}
def family_set_iso_path_equiv (A : Type) (P Q : A → SetTypes)
  : Equiv (Id (A → SetTypes) P Q) (CatIso (FamilySetWild A) P Q)
  ≔ let Pf : A → Type ≔ a ↦ P a .fst in
    let Qf : A → Type ≔ a ↦ Q a .fst in
    let Fib ≔ (a : A) → Σ (Pf a → Qf a) (isEquiv (Pf a) (Qf a)) in
    let Tot ≔ Σ ((a : A) → Pf a → Qf a) (f ↦ (a : A) → isEquiv (Pf a) (Qf a) (f a)) in
    compose_equiv (Id (A → SetTypes) P Q) (Homotopy A (_ ↦ SetTypes) P Q) (CatIso (FamilySetWild A) P Q)
      (function_extensionality A (_ ↦ SetTypes) P Q)
      (compose_equiv (Homotopy A (_ ↦ SetTypes) P Q) ((a : A) → Equiv (Pf a) (Qf a)) (CatIso (FamilySetWild A) P Q)
        (pi_family_equiv A (a ↦ Id SetTypes (P a) (Q a)) (a ↦ Equiv (Pf a) (Qf a)) (a ↦ set_paths_equiv (P a) (Q a)))
        (compose_equiv ((a : A) → Equiv (Pf a) (Qf a)) Fib (CatIso (FamilySetWild A) P Q)
          (pi_family_equiv A (a ↦ Equiv (Pf a) (Qf a)) (a ↦ Σ (Pf a → Qf a) (isEquiv (Pf a) (Qf a)))
            (a ↦ equiv_sigma_equiv (Pf a) (Qf a)))
          (compose_equiv Fib Tot (CatIso (FamilySetWild A) P Q)
            (choice_equiv A (a ↦ Pf a → Qf a) (a f ↦ isEquiv (Pf a) (Qf a) f))
            (family_equiv ((a : A) → Pf a → Qf a) (f ↦ (a : A) → isEquiv (Pf a) (Qf a) (f a))
              (f ↦ CatIsIso (FamilySetWild A) P Q f)
              (f ↦ iff_equiv ((a : A) → isEquiv (Pf a) (Qf a) (f a)) (CatIsIso (FamilySetWild A) P Q f)
                (pi_prop A (a ↦ isEquiv (Pf a) (Qf a) (f a)) (a ↦ isequiv_isprop (Pf a) (Qf a) (f a)))
                (cat_is_iso_prop (FamilySetWild A) P Q f)
                (family_fiberwise_equiv_iso A Pf Qf f)
                (i ↦ family_iso_fiberwise_equiv A Pf Qf f i))))))

def family_set_univalent (A : Type) : IsUnivalentCat (FamilySetWild A)
  ≔ cat_univalent_from_equivalences (FamilySetWild A) (family_set_iso_path_equiv A)

def FamilySetCategory (A : Type) : Category ≔ (FamilySetWild A, family_set_homset A, family_set_univalent A)

{` The category of G-sets: objects GSet G, arrows GSetHom G X Y (maps of
   G-sets, def:map-of-Gsets), composition gset_hom_compose. `}
def GSetWild (G : Group) : WildPrecat ≔ FamilySetWild (BG G .carrier)

def GSetCat (G : Group) : Category ≔ FamilySetCategory (BG G .carrier)

def gset_cat_objects (G : Group) : Id Type (GSetCat G .wild .ob) (GSet G) ≔ refl (GSet G)

def gset_cat_homs (G : Group) (X Y : GSet G) : Id Type (GSetCat G .wild .hom X Y) (GSetHom G X Y)
  ≔ refl (GSetHom G X Y)

def gset_cat_identity (G : Group) (X : GSet G) : Id (GSetHom G X X) (GSetCat G .wild .idn X) (gset_hom_id G X)
  ≔ refl (gset_hom_id G X)

def gset_cat_compose (G : Group) (X Y Z : GSet G) (f : GSetHom G X Y) (g : GSetHom G Y Z)
  : Id (GSetHom G X Z) (GSetCat G .wild .comp X Y Z g f) (gset_hom_compose G X Y Z f g)
  ≔ refl (gset_hom_compose G X Y Z f g)

{` ex:action-functors. For a homomorphism f : G → H, restriction
   f^* : GSet[H] → GSet[G], induction f_! and coinduction f_* :
   GSet[G] → GSet[H]. On objects they are the chapter-5 constructions
   (def:restrictandinduce, rem:coinduced-Hset). On arrows, f^*(g) maps
   z : BG to g_{Bf(z)}, and f_!(g) is the functorial action of set
   truncation on ‖Σ_{z} (Bf z = w) × X(z)‖₀ (the book's text breaks off
   here); f_*(g) is postcomposition with g. `}
def gset_restrict_functor (G H : Group) (f : GroupHom G H) : WildFunctor (GSetWild H) (GSetWild G)
  ≔ set_family_reindex_functor (BG G .carrier) (BG H .carrier) (hom_function G H f)

def gset_induce_functor (G H : Group) (f : GroupHom G H) : WildFunctor (GSetWild G) (GSetWild H)
  ≔ set_family_sum_functor (BG G .carrier) (BG H .carrier) (hom_function G H f)

def gset_coinduce_functor (G H : Group) (f : GroupHom G H) : WildFunctor (GSetWild G) (GSetWild H)
  ≔ set_family_product_functor (BG G .carrier) (BG H .carrier) (hom_function G H f)

def gset_restrict_functor_obj (G H : Group) (f : GroupHom G H) (Y : GSet H)
  : Id (GSet G) (gset_restrict_functor G H f .obj Y) (gset_restrict G H f Y)
  ≔ refl (gset_restrict G H f Y)

def gset_restrict_functor_mor (G H : Group) (f : GroupHom G H) (X Y : GSet H) (g : GSetHom H X Y)
  : Id (GSetHom G (gset_restrict G H f X) (gset_restrict G H f Y)) (gset_restrict_functor G H f .mor X Y g)
      (z ↦ g (hom_function G H f z))
  ≔ refl ((z ↦ g (hom_function G H f z)) : GSetHom G (gset_restrict G H f X) (gset_restrict G H f Y))

def gset_induce_functor_obj (G H : Group) (f : GroupHom G H) (X : GSet G)
  : Id (GSet H) (gset_induce_functor G H f .obj X) (gset_induce G H f X)
  ≔ refl (gset_induce G H f X)

{` On a representative (z, p, x) of f_!X(w), f_!(g) acts by g_z on x. `}
def gset_induce_functor_mor_class (G H : Group) (f : GroupHom G H) (X Y : GSet G) (g : GSetHom G X Y)
  (w : BG H .carrier) (t : GSetInducedSum G H f X w)
  : Id (SetTrunc (GSetInducedSum G H f Y w))
      (gset_induce_functor G H f .mor X Y g w (set_trunc (GSetInducedSum G H f X w) t))
      (set_trunc (GSetInducedSum G H f Y w) (t .fst, (t .snd .fst, g (t .fst) (t .snd .snd))))
  ≔ set_trunc_rec_beta (GSetInducedSum G H f X w) (SetTrunc (GSetInducedSum G H f Y w))
      (set_trunc_set (GSetInducedSum G H f Y w))
      (s ↦ set_trunc (GSetInducedSum G H f Y w) (s .fst, (s .snd .fst, g (s .fst) (s .snd .snd)))) t

def gset_coinduce_functor_obj (G H : Group) (f : GroupHom G H) (X : GSet G)
  : Id (GSet H) (gset_coinduce_functor G H f .obj X) (gset_coinduce G H f X)
  ≔ refl (gset_coinduce G H f X)

{` The prose before def:adjunction: natural bijections
   α : Hom_H(f_! X, Y) ≅ Hom_G(X, f^* Y) and β : Hom_G(f^* Y, X) ≅ Hom_H(Y, f_* X),
   i.e. adjunctions f_! ⊣ f^* ⊣ f_* (xca:adjunction-_!-^*, xca:adjunction-^*-_*). `}
def gset_induce_restrict_adjunction (G H : Group) (f : GroupHom G H) : WildAdjunction (GSetWild G) (GSetWild H)
  ≔ set_family_sum_adjunction (BG G .carrier) (BG H .carrier) (hom_function G H f)

def gset_restrict_coinduce_adjunction (G H : Group) (f : GroupHom G H) : WildAdjunction (GSetWild H) (GSetWild G)
  ≔ set_family_product_adjunction (BG G .carrier) (BG H .carrier) (hom_function G H f)

def gset_induce_restrict_transpose_equiv (G H : Group) (f : GroupHom G H) (X : GSet G) (Y : GSet H)
  : Equiv (GSetHom H (gset_induce G H f X) Y) (GSetHom G X (gset_restrict G H f Y))
  ≔ adjunction_transpose_equiv (GSetWild G) (GSetWild H) (gset_induce_functor G H f)
      (gset_induce_restrict_adjunction G H f .right_adjoint) X Y

def gset_restrict_coinduce_transpose_equiv (G H : Group) (f : GroupHom G H) (Y : GSet H) (X : GSet G)
  : Equiv (GSetHom G (gset_restrict G H f Y) X) (GSetHom H Y (gset_coinduce G H f X))
  ≔ adjunction_transpose_equiv (GSetWild H) (GSetWild G) (gset_restrict_functor G H f)
      (gset_restrict_coinduce_adjunction G H f .right_adjoint) Y X

{` Litmus: restriction along the identity homomorphism is the identity on
   objects, and the identity isomorphism of a G-set is the identity map. `}
def gset_restrict_identity_check (G : Group) (Y : GSet G)
  : Id (GSet G) (gset_restrict_functor G G (group_hom_id G) .obj Y) Y
  ≔ refl Y

def gset_cat_identity_iso_check (G : Group) (X : GSet G)
  : Id (GSetHom G X X) (cat_identity_iso (GSetCat G .wild) X .fst) (gset_hom_id G X)
  ≔ refl (gset_hom_id G X)
