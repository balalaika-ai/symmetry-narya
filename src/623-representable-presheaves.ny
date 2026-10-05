export "622-yoneda-lemma"

{` Chapter 6 (cats.tex), section 6.6: the Yoneda embedding is an
   injection on objects for a category (cor:yo-emb-obj), representable
   presheaves (def:repr) and uniqueness of representing objects
   (cor:repr-prop). `}

{` A fully faithful functor reflects isomorphisms and induces equivalences
   a ≅ b ≃ F(a) ≅ F(b) (in any wild precategories). `}
def ff_hom_equiv (C D : WildPrecat) (F : WildFunctor C D) (ff : IsFullyFaithful C D F) (a b : C .ob)
  : Equiv (C .hom a b) (D .hom (F .obj a) (F .obj b))
  ≔ native_equivalence (C .hom a b) (D .hom (F .obj a) (F .obj b)) (fully_faithful_equiv C D F ff a b)

def ff_hom_inverse (C D : WildPrecat) (F : WildFunctor C D) (ff : IsFullyFaithful C D F) (a b : C .ob)
  : D .hom (F .obj a) (F .obj b) → C .hom a b
  ≔ equiv_inverse_map (C .hom a b) (D .hom (F .obj a) (F .obj b)) (ff_hom_equiv C D F ff a b)

def ff_hom_injective (C D : WildPrecat) (F : WildFunctor C D) (ff : IsFullyFaithful C D F) (a b : C .ob)
  (u v : C .hom a b) (q : Id (D .hom (F .obj a) (F .obj b)) (F .mor a b u) (F .mor a b v))
  : Id (C .hom a b) u v
  ≔ let e ≔ ff_hom_equiv C D F ff a b in
    concat (C .hom a b) u (ff_hom_inverse C D F ff a b (F .mor a b u)) v
      (inverse (C .hom a b) (ff_hom_inverse C D F ff a b (F .mor a b u)) u
        (equiv_retraction (C .hom a b) (D .hom (F .obj a) (F .obj b)) e u))
      (concat (C .hom a b) (ff_hom_inverse C D F ff a b (F .mor a b u)) (ff_hom_inverse C D F ff a b (F .mor a b v)) v
        (refl (ff_hom_inverse C D F ff a b) q)
        (equiv_retraction (C .hom a b) (D .hom (F .obj a) (F .obj b)) e v))

{` If F(u) ∘ m = id with m = F(g) up to the counit, then u ∘ g = id. `}
def ff_inverse_law (C D : WildPrecat) (F : WildFunctor C D) (ff : IsFullyFaithful C D F) (a b : C .ob)
  (u : C .hom a b) (m : D .hom (F .obj b) (F .obj a))
  (p : Id (D .hom (F .obj b) (F .obj b)) (D .comp (F .obj b) (F .obj a) (F .obj b) (F .mor a b u) m) (D .idn (F .obj b)))
  : Id (C .hom b b) (C .comp b a b u (ff_hom_inverse C D F ff b a m)) (C .idn b)
  ≔ let g ≔ ff_hom_inverse C D F ff b a m in
    ff_hom_injective C D F ff b b (C .comp b a b u g) (C .idn b)
      (calc
        F .mor b b (C .comp b a b u g)
        = D .comp (F .obj b) (F .obj a) (F .obj b) (F .mor a b u) (F .mor b a g)
          by F .map_comp b a b g u
        = D .comp (F .obj b) (F .obj a) (F .obj b) (F .mor a b u) m
          by cat_whisker_left D (F .obj b) (F .obj a) (F .obj b) (F .mor a b u) (F .mor b a g) m
               (equiv_counit (C .hom b a) (D .hom (F .obj b) (F .obj a)) (ff_hom_equiv C D F ff b a) m)
        = D .idn (F .obj b) by p
        = F .mor b b (C .idn b)
          by inverse (D .hom (F .obj b) (F .obj b)) (F .mor b b (C .idn b)) (D .idn (F .obj b)) (F .map_id b) ∎)

def ff_reflects_iso (C D : WildPrecat) (F : WildFunctor C D) (ff : IsFullyFaithful C D F) (a b : C .ob)
  (f : C .hom a b) (j : CatIsIso D (F .obj a) (F .obj b) (F .mor a b f)) : CatIsIso C a b f
  ≔ ((ff_hom_inverse C D F ff b a (j .fst .fst), ff_inverse_law C D F ff a b f (j .fst .fst) (j .fst .snd)),
     (ff_hom_inverse C D F ff b a (j .snd .fst),
      ff_hom_injective C D F ff a a (C .comp a b a (ff_hom_inverse C D F ff b a (j .snd .fst)) f) (C .idn a)
        (calc
          F .mor a a (C .comp a b a (ff_hom_inverse C D F ff b a (j .snd .fst)) f)
          = D .comp (F .obj a) (F .obj b) (F .obj a) (F .mor b a (ff_hom_inverse C D F ff b a (j .snd .fst)))
              (F .mor a b f)
            by F .map_comp a b a f (ff_hom_inverse C D F ff b a (j .snd .fst))
          = D .comp (F .obj a) (F .obj b) (F .obj a) (j .snd .fst) (F .mor a b f)
            by cat_whisker_right D (F .obj a) (F .obj b) (F .obj a)
                 (F .mor b a (ff_hom_inverse C D F ff b a (j .snd .fst))) (j .snd .fst) (F .mor a b f)
                 (equiv_counit (C .hom b a) (D .hom (F .obj b) (F .obj a)) (ff_hom_equiv C D F ff b a) (j .snd .fst))
          = D .idn (F .obj a) by j .snd .snd
          = F .mor a a (C .idn a)
            by inverse (D .hom (F .obj a) (F .obj a)) (F .mor a a (C .idn a)) (D .idn (F .obj a)) (F .map_id a) ∎)))

def ff_iso_inverse (C D : WildPrecat) (F : WildFunctor C D) (ff : IsFullyFaithful C D F) (a b : C .ob)
  (e : CatIso D (F .obj a) (F .obj b)) : CatIso C a b
  ≔ let m ≔ ff_hom_inverse C D F ff a b (e .fst) in
    (m, ff_reflects_iso C D F ff a b m
          (transport (D .hom (F .obj a) (F .obj b)) (CatIsIso D (F .obj a) (F .obj b)) (e .fst) (F .mor a b m)
            (inverse (D .hom (F .obj a) (F .obj b)) (F .mor a b m) (e .fst)
              (equiv_counit (C .hom a b) (D .hom (F .obj a) (F .obj b)) (ff_hom_equiv C D F ff a b) (e .fst)))
            (e .snd)))

def ff_functor_iso_equiv (C D : WildPrecat) (F : WildFunctor C D) (ff : IsFullyFaithful C D F) (a b : C .ob)
  : Equiv (CatIso C a b) (CatIso D (F .obj a) (F .obj b))
  ≔ quasi_inverse_equiv (CatIso C a b) (CatIso D (F .obj a) (F .obj b)) (functor_iso C D F a b)
      (ff_iso_inverse C D F ff a b)
      (e ↦ cat_iso_path C a b (ff_iso_inverse C D F ff a b (functor_iso C D F a b e)) e
         (equiv_retraction (C .hom a b) (D .hom (F .obj a) (F .obj b)) (ff_hom_equiv C D F ff a b) (e .fst)))
      (e ↦ cat_iso_path D (F .obj a) (F .obj b) (functor_iso C D F a b (ff_iso_inverse C D F ff a b e)) e
         (equiv_counit (C .hom a b) (D .hom (F .obj a) (F .obj b)) (ff_hom_equiv C D F ff a b) (e .fst)))

{` Every functor commutes with idtoiso: idtoiso(ap F p) = F(idtoiso p). `}
def functor_idtoiso_base (C D : WildPrecat) (F : WildFunctor C D) (x : C .ob)
  : Id (CatIso D (F .obj x) (F .obj x))
      (cat_idtoiso D (F .obj x) (F .obj x) (refl (F .obj x)))
      (functor_iso C D F x x (cat_idtoiso C x x (refl x)))
  ≔ cat_iso_path D (F .obj x) (F .obj x) (cat_idtoiso D (F .obj x) (F .obj x) (refl (F .obj x)))
      (functor_iso C D F x x (cat_idtoiso C x x (refl x)))
      (calc
        cat_idtoiso D (F .obj x) (F .obj x) (refl (F .obj x)) .fst
        = D .idn (F .obj x)
          by inverse (D .hom (F .obj x) (F .obj x)) (D .idn (F .obj x))
               (cat_idtoiso D (F .obj x) (F .obj x) (refl (F .obj x)) .fst)
               (refl ((e ↦ e .fst) : CatIso D (F .obj x) (F .obj x) → D .hom (F .obj x) (F .obj x))
                 (cat_idtoiso_refl D (F .obj x)))
        = F .mor x x (C .idn x)
          by inverse (D .hom (F .obj x) (F .obj x)) (F .mor x x (C .idn x)) (D .idn (F .obj x)) (F .map_id x)
        = F .mor x x (cat_idtoiso C x x (refl x) .fst)
          by refl (F .mor x x)
               (refl ((e ↦ e .fst) : CatIso C x x → C .hom x x) (cat_idtoiso_refl C x)) ∎)

def functor_idtoiso (C D : WildPrecat) (F : WildFunctor C D) (x y : C .ob) (p : Id (C .ob) x y)
  : Id (CatIso D (F .obj x) (F .obj y))
      (cat_idtoiso D (F .obj x) (F .obj y) (map_path (C .ob) (D .ob) (F .obj) x y p))
      (functor_iso C D F x y (cat_idtoiso C x y p))
  ≔ J (C .ob) x (y p ↦ Id (CatIso D (F .obj x) (F .obj y))
        (cat_idtoiso D (F .obj x) (F .obj y) (map_path (C .ob) (D .ob) (F .obj) x y p))
        (functor_iso C D F x y (cat_idtoiso C x y p)))
      (functor_idtoiso_base C D F x) y p

{` A fully faithful functor between univalent wild precategories is an
   injection (embedding) on objects: ap F is the composite of the
   equivalences idtoiso, F on isomorphisms and isotoid. `}
def ff_ap_equiv (C D : WildPrecat) (uC : IsUnivalentCat C) (uD : IsUnivalentCat D) (F : WildFunctor C D)
  (ff : IsFullyFaithful C D F) (x y : C .ob)
  : Equiv (Id (C .ob) x y) (Id (D .ob) (F .obj x) (F .obj y))
  ≔ let phi ≔ cat_idtoiso_equiv D uD (F .obj x) (F .obj y) in
    let psi ≔ compose_equiv (Id (C .ob) x y) (CatIso C x y) (CatIso D (F .obj x) (F .obj y))
        (cat_idtoiso_equiv C uC x y) (ff_functor_iso_equiv C D F ff x y) in
    equiv_change_map (Id (C .ob) x y) (Id (D .ob) (F .obj x) (F .obj y))
      (compose_equiv (Id (C .ob) x y) (CatIso D (F .obj x) (F .obj y)) (Id (D .ob) (F .obj x) (F .obj y))
        psi (canonical_inverse_equiv (Id (D .ob) (F .obj x) (F .obj y)) (CatIso D (F .obj x) (F .obj y)) phi))
      (map_path (C .ob) (D .ob) (F .obj) x y)
      (p ↦ concat (Id (D .ob) (F .obj x) (F .obj y))
         (equiv_inverse_map (Id (D .ob) (F .obj x) (F .obj y)) (CatIso D (F .obj x) (F .obj y)) phi
           (functor_iso C D F x y (cat_idtoiso C x y p)))
         (equiv_inverse_map (Id (D .ob) (F .obj x) (F .obj y)) (CatIso D (F .obj x) (F .obj y)) phi
           (phi .map (map_path (C .ob) (D .ob) (F .obj) x y p)))
         (map_path (C .ob) (D .ob) (F .obj) x y p)
         (refl (equiv_inverse_map (Id (D .ob) (F .obj x) (F .obj y)) (CatIso D (F .obj x) (F .obj y)) phi)
           (inverse (CatIso D (F .obj x) (F .obj y))
             (cat_idtoiso D (F .obj x) (F .obj y) (map_path (C .ob) (D .ob) (F .obj) x y p))
             (functor_iso C D F x y (cat_idtoiso C x y p))
             (functor_idtoiso C D F x y p)))
         (equiv_retraction (Id (D .ob) (F .obj x) (F .obj y)) (CatIso D (F .obj x) (F .obj y)) phi
           (map_path (C .ob) (D .ob) (F .obj) x y p)))

def ff_object_embedding (C D : WildPrecat) (uC : IsUnivalentCat C) (uD : IsUnivalentCat D) (F : WildFunctor C D)
  (ff : IsFullyFaithful C D F) : IsEmbedding (C .ob) (D .ob) (F .obj)
  ≔ path_equivalences_embedding (C .ob) (D .ob) (F .obj)
      (x y ↦ book_equivalence (Id (C .ob) x y) (Id (D .ob) (F .obj x) (F .obj y)) (ff_ap_equiv C D uC uD F ff x y)
        .equiv)

{` cor:yo-emb-obj. `}
def yoneda_object_embedding (C : Category)
  : IsEmbedding (C .wild .ob) (PresheafCategory (category_precat C) .wild .ob)
      (yoneda_functor (category_precat C) .obj)
  ≔ ff_object_embedding (C .wild) (PresheafCategory (category_precat C) .wild) (C .univalent)
      (PresheafCategory (category_precat C) .univalent) (yoneda_functor (category_precat C))
      (yoneda_fully_faithful (category_precat C))

{` def:repr: the type of pairs (c, α) with α : yo(c) ≅ F. `}
def IsRepresentable (C : Precat) (F : PresheafCategory C .wild .ob) : Type
  ≔ Σ (C .wild .ob) (c ↦ CatIso (PresheafCategory C .wild) (yoneda_functor C .obj c) F)

{` A type equivalent to a proposition is a proposition. `}
def prop_from_equiv (A B : Type) (e : Equiv A B) (hB : isProp B) : isProp A
  ≔ retract_prop B A hB (equiv_inverse_map A B e) (e .map) (equiv_retraction A B e)

{` cor:repr-prop: IsRepresentable is the fiber of yo over F (up to
   univalence of Set^{C^op}), hence a proposition by cor:yo-emb-obj. `}
def representability_fiber_equiv (C : Category) (F : PresheafCategory (category_precat C) .wild .ob)
  : Equiv (IsRepresentable (category_precat C) F)
      (BookFiber (C .wild .ob) (PresheafCategory (category_precat C) .wild .ob) (yoneda_functor (category_precat C) .obj) F)
  ≔ let P ≔ PresheafCategory (category_precat C) in
    let yo ≔ yoneda_functor (category_precat C) in
    family_equiv (C .wild .ob) (c ↦ CatIso (P .wild) (yo .obj c) F) (c ↦ Id (P .wild .ob) F (yo .obj c))
      (c ↦ compose_equiv (CatIso (P .wild) (yo .obj c) F) (Id (P .wild .ob) (yo .obj c) F) (Id (P .wild .ob) F (yo .obj c))
        (canonical_inverse_equiv (Id (P .wild .ob) (yo .obj c) F) (CatIso (P .wild) (yo .obj c) F)
          (cat_idtoiso_equiv (P .wild) (P .univalent) (yo .obj c) F))
        (inverse_path_equiv (P .wild .ob) (yo .obj c) F))

def representability_prop (C : Category) (F : PresheafCategory (category_precat C) .wild .ob)
  : isProp (IsRepresentable (category_precat C) F)
  ≔ prop_from_equiv (IsRepresentable (category_precat C) F)
      (BookFiber (C .wild .ob) (PresheafCategory (category_precat C) .wild .ob) (yoneda_functor (category_precat C) .obj) F)
      (representability_fiber_equiv C F)
      (yoneda_object_embedding C F)

{` Litmus: yo(c) is represented by (c, id); the presheaf constant at the
   empty set is not representable (evaluate the iso at id_c). `}
def representable_presheaf_is_representable (C : Precat) (c : C .wild .ob)
  : IsRepresentable C (yoneda_functor C .obj c)
  ≔ (c, cat_identity_iso (PresheafCategory C .wild) (yoneda_functor C .obj c))

def empty_presheaf (C : Precat) : PresheafCategory C .wild .ob
  ≔ constant_functor (OppositeWild (C .wild)) SetWild (Empty, empty_set)

def empty_presheaf_not_representable (C : Precat) (r : IsRepresentable C (empty_presheaf C)) : Empty
  ≔ r .snd .fst .component (r .fst) (C .wild .idn (r .fst))

def set_cat_bool_representable_center
  : Id (Bool → Bool)
      (representable_presheaf_is_representable set_precat set_cat_bool .snd .fst .component set_cat_bool bool_not)
      bool_not
  ≔ refl bool_not
