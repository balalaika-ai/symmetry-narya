export "643-ff-eso-equivalences"

{` Chapter 6, section 6.7: the footnote to cor:Cat-ua. For precategories,
   identifications C = D correspond to isomorphisms of precategories:
   fully faithful functors that induce an equivalence on the types of
   objects. The map sends refl C to the identity functor (path induction);
   it is an equivalence because the total space of isomorphisms out of C is
   contractible (structure identity principle: the object type, the hom
   family, identities and composition are contracted one after another by
   univalence and function extensionality; the laws are propositions). `}

{` Generic contractibility tools. `}
def ch6c_contr_transfer (A B : Type) (e : Equiv A B) (h : isContr A) : isContr B
  ≔ hlevel_equiv zero. A B e h

{` If A is contractible and a0 : A, then Σ A B ≃ B a0. `}
def ch6c_sigma_contract_base (A : Type) (B : A → Type) (hA : isContr A) (a0 : A) : Equiv (Σ A B) (B a0)
  ≔ let hp : (x : A) → isContr (Id A a0 x) ≔ x ↦ prop_paths_contractible A (contractible_prop A hA) a0 x in
    compose_equiv (Σ A B) (Σ A (x ↦ Product (Id A a0 x) (B x))) (B a0)
      (family_equiv A B (x ↦ Product (Id A a0 x) (B x)) (x ↦
        quasi_inverse_equiv (B x) (Product (Id A a0 x) (B x))
          (b ↦ (hp x .center, b)) (u ↦ u .snd) (b ↦ refl b)
          (u ↦ (contractible_prop (Id A a0 x) (hp x) (hp x .center) (u .fst), refl (u .snd)))))
      (contract_away_simple A a0 B)

{` Singletons of (dependent, curried) functions with pointwise
   identifications. `}
def ch6c_fun_singleton1 (A : Type) (B : A → Type) (k0 : (a : A) → B a)
  : isContr (Σ ((a : A) → B a) (k ↦ (a : A) → Id (B a) (k0 a) (k a)))
  ≔ ch6c_contr_transfer ((a : A) → Σ (B a) (b ↦ Id (B a) (k0 a) b))
      (Σ ((a : A) → B a) (k ↦ (a : A) → Id (B a) (k0 a) (k a)))
      (choice_equiv A B (a b ↦ Id (B a) (k0 a) b))
      (pi_contractible A (a ↦ Σ (B a) (b ↦ Id (B a) (k0 a) b)) (a ↦ iscontr_idfrom (B a) (k0 a)))

def ch6c_fun_singleton2 (A : Type) (B : A → Type) (X : (a : A) → B a → Type) (k0 : (a : A) (b : B a) → X a b)
  : isContr (Σ ((a : A) (b : B a) → X a b) (k ↦ (a : A) (b : B a) → Id (X a b) (k0 a b) (k a b)))
  ≔ ch6c_contr_transfer
      ((a : A) → Σ ((b : B a) → X a b) (ka ↦ (b : B a) → Id (X a b) (k0 a b) (ka b)))
      (Σ ((a : A) (b : B a) → X a b) (k ↦ (a : A) (b : B a) → Id (X a b) (k0 a b) (k a b)))
      (choice_equiv A (a ↦ (b : B a) → X a b) (a ka ↦ (b : B a) → Id (X a b) (k0 a b) (ka b)))
      (pi_contractible A (a ↦ Σ ((b : B a) → X a b) (ka ↦ (b : B a) → Id (X a b) (k0 a b) (ka b)))
        (a ↦ ch6c_fun_singleton1 (B a) (X a) (k0 a)))

def ch6c_fun_singleton3 (A : Type) (B : A → Type) (X : (a : A) → B a → Type)
  (Y : (a : A) (b : B a) → X a b → Type) (k0 : (a : A) (b : B a) (x : X a b) → Y a b x)
  : isContr (Σ ((a : A) (b : B a) (x : X a b) → Y a b x)
      (k ↦ (a : A) (b : B a) (x : X a b) → Id (Y a b x) (k0 a b x) (k a b x)))
  ≔ ch6c_contr_transfer
      ((a : A) → Σ ((b : B a) (x : X a b) → Y a b x) (ka ↦ (b : B a) (x : X a b) → Id (Y a b x) (k0 a b x) (ka b x)))
      (Σ ((a : A) (b : B a) (x : X a b) → Y a b x)
        (k ↦ (a : A) (b : B a) (x : X a b) → Id (Y a b x) (k0 a b x) (k a b x)))
      (choice_equiv A (a ↦ (b : B a) (x : X a b) → Y a b x)
        (a ka ↦ (b : B a) (x : X a b) → Id (Y a b x) (k0 a b x) (ka b x)))
      (pi_contractible A
        (a ↦ Σ ((b : B a) (x : X a b) → Y a b x) (ka ↦ (b : B a) (x : X a b) → Id (Y a b x) (k0 a b x) (ka b x)))
        (a ↦ ch6c_fun_singleton2 (B a) (X a) (Y a) (k0 a)))

def ch6c_fun_singleton4 (A : Type) (B : A → Type) (X : (a : A) → B a → Type)
  (Y : (a : A) (b : B a) → X a b → Type) (Z : (a : A) (b : B a) (x : X a b) → Y a b x → Type)
  (k0 : (a : A) (b : B a) (x : X a b) (y : Y a b x) → Z a b x y)
  : isContr (Σ ((a : A) (b : B a) (x : X a b) (y : Y a b x) → Z a b x y)
      (k ↦ (a : A) (b : B a) (x : X a b) (y : Y a b x) → Id (Z a b x y) (k0 a b x y) (k a b x y)))
  ≔ ch6c_contr_transfer
      ((a : A) → Σ ((b : B a) (x : X a b) (y : Y a b x) → Z a b x y)
        (ka ↦ (b : B a) (x : X a b) (y : Y a b x) → Id (Z a b x y) (k0 a b x y) (ka b x y)))
      (Σ ((a : A) (b : B a) (x : X a b) (y : Y a b x) → Z a b x y)
        (k ↦ (a : A) (b : B a) (x : X a b) (y : Y a b x) → Id (Z a b x y) (k0 a b x y) (k a b x y)))
      (choice_equiv A (a ↦ (b : B a) (x : X a b) (y : Y a b x) → Z a b x y)
        (a ka ↦ (b : B a) (x : X a b) (y : Y a b x) → Id (Z a b x y) (k0 a b x y) (ka b x y)))
      (pi_contractible A
        (a ↦ Σ ((b : B a) (x : X a b) (y : Y a b x) → Z a b x y)
          (ka ↦ (b : B a) (x : X a b) (y : Y a b x) → Id (Z a b x y) (k0 a b x y) (ka b x y)))
        (a ↦ ch6c_fun_singleton3 (B a) (X a) (Y a) (Z a) (k0 a)))

def ch6c_fun_singleton5 (A : Type) (B : A → Type) (X : (a : A) → B a → Type)
  (Y : (a : A) (b : B a) → X a b → Type) (Z : (a : A) (b : B a) (x : X a b) → Y a b x → Type)
  (W : (a : A) (b : B a) (x : X a b) (y : Y a b x) → Z a b x y → Type)
  (k0 : (a : A) (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → W a b x y z)
  : isContr (Σ ((a : A) (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → W a b x y z)
      (k ↦ (a : A) (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → Id (W a b x y z) (k0 a b x y z) (k a b x y z)))
  ≔ ch6c_contr_transfer
      ((a : A) → Σ ((b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → W a b x y z)
        (ka ↦ (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → Id (W a b x y z) (k0 a b x y z) (ka b x y z)))
      (Σ ((a : A) (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → W a b x y z)
        (k ↦ (a : A) (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → Id (W a b x y z) (k0 a b x y z) (k a b x y z)))
      (choice_equiv A (a ↦ (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → W a b x y z)
        (a ka ↦ (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → Id (W a b x y z) (k0 a b x y z) (ka b x y z)))
      (pi_contractible A
        (a ↦ Σ ((b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → W a b x y z)
          (ka ↦ (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → Id (W a b x y z) (k0 a b x y z) (ka b x y z)))
        (a ↦ ch6c_fun_singleton4 (B a) (X a) (Y a) (Z a) (W a) (k0 a)))

{` Σ (B : Type) (A ≃ B) is contractible (univalence). `}
def ch6c_equiv_singleton (A : Type) : isContr (Σ Type (B ↦ Equiv A B))
  ≔ ch6c_contr_transfer (Σ Type (B ↦ Id Type A B)) (Σ Type (B ↦ Equiv A B))
      (family_equiv Type (B ↦ Id Type A B) (B ↦ Equiv A B) (B ↦ univalence_equiv A B))
      (iscontr_idfrom Type A)

{` Families of types with fiberwise equivalences from a fixed family. `}
def ch6c_family2_equiv_singleton (X : Type) (H : X → X → Type)
  : isContr (Σ (X → X → Type) (h ↦ (a b : X) → Equiv (H a b) (h a b)))
  ≔ ch6c_contr_transfer ((a : X) → Σ (X → Type) (ha ↦ (b : X) → Equiv (H a b) (ha b)))
      (Σ (X → X → Type) (h ↦ (a b : X) → Equiv (H a b) (h a b)))
      (choice_equiv X (_ ↦ X → Type) (a ha ↦ (b : X) → Equiv (H a b) (ha b)))
      (pi_contractible X (a ↦ Σ (X → Type) (ha ↦ (b : X) → Equiv (H a b) (ha b)))
        (a ↦ ch6c_contr_transfer ((b : X) → Σ Type (T ↦ Equiv (H a b) T))
          (Σ (X → Type) (ha ↦ (b : X) → Equiv (H a b) (ha b)))
          (choice_equiv X (_ ↦ Type) (b T ↦ Equiv (H a b) T))
          (pi_contractible X (b ↦ Σ Type (T ↦ Equiv (H a b) T)) (b ↦ ch6c_equiv_singleton (H a b)))))

{` Isomorphisms of precategories (footnote to cor:Cat-ua). `}
def PrecatIsomorphism (C D : Precat) : Type
  ≔ Σ (WildFunctor (C .wild) (D .wild)) (F ↦
      Product (IsFullyFaithful (C .wild) (D .wild) F) (BookIsEquiv (C .wild .ob) (D .wild .ob) (F .obj)))

def precat_identity_isomorphism (C : Precat) : PrecatIsomorphism C C
  ≔ (functor_identity (C .wild),
     (identity_cat_equivalence_ff (C .wild),
      book_equivalence (C .wild .ob) (C .wild .ob) (identity_equiv (C .wild .ob)) .equiv))

{` The map (C = D) → (C ≅ D), by path induction. `}
def precategory_path_to_isomorphism (C D : Precat) (p : Id Precat C D) : PrecatIsomorphism C D
  ≔ J Precat C (D _ ↦ PrecatIsomorphism C D) (precat_identity_isomorphism C) D p

def precategory_path_to_isomorphism_refl (C : Precat)
  : Id (PrecatIsomorphism C C) (precat_identity_isomorphism C) (precategory_path_to_isomorphism C C (refl C))
  ≔ Jβ Precat C (D _ ↦ PrecatIsomorphism C D) (precat_identity_isomorphism C)

{` The native form of isomorphisms of precategories. `}
def PrecatIsoNative (C D : Precat) : Type
  ≔ Σ (WildFunctor (C .wild) (D .wild)) (F ↦
      Product ((a b : C .wild .ob) → isEquiv (C .wild .hom a b) (D .wild .hom (F .obj a) (F .obj b)) (F .mor a b))
        (isEquiv (C .wild .ob) (D .wild .ob) (F .obj)))

def precat_iso_native_equiv (C D : Precat) : Equiv (PrecatIsomorphism C D) (PrecatIsoNative C D)
  ≔ let W ≔ C .wild in
    let V ≔ D .wild in
    family_equiv (WildFunctor W V)
      (F ↦ Product (IsFullyFaithful W V F) (BookIsEquiv (W .ob) (V .ob) (F .obj)))
      (F ↦ Product ((a b : W .ob) → isEquiv (W .hom a b) (V .hom (F .obj a) (F .obj b)) (F .mor a b))
        (isEquiv (W .ob) (V .ob) (F .obj)))
      (F ↦ product_equiv (IsFullyFaithful W V F) (BookIsEquiv (W .ob) (V .ob) (F .obj))
        ((a b : W .ob) → isEquiv (W .hom a b) (V .hom (F .obj a) (F .obj b)) (F .mor a b))
        (isEquiv (W .ob) (V .ob) (F .obj))
        (iff_equiv (IsFullyFaithful W V F)
          ((a b : W .ob) → isEquiv (W .hom a b) (V .hom (F .obj a) (F .obj b)) (F .mor a b))
          (is_fully_faithful_prop W V F)
          (ch6c_pi_prop2 (W .ob) (_ ↦ W .ob) (a b ↦ isEquiv (W .hom a b) (V .hom (F .obj a) (F .obj b)) (F .mor a b))
            (a b ↦ isequiv_isprop (W .hom a b) (V .hom (F .obj a) (F .obj b)) (F .mor a b)))
          (ff_mor_is_equiv W V F) (ff_from_mor_equivs W V F))
        (iff_equiv (BookIsEquiv (W .ob) (V .ob) (F .obj)) (isEquiv (W .ob) (V .ob) (F .obj))
          (book_isequiv_isprop (W .ob) (V .ob) (F .obj)) (isequiv_isprop (W .ob) (V .ob) (F .obj))
          (b ↦ native_equivalence (W .ob) (V .ob) (F .obj, b) .equiv)
          (n ↦ book_equivalence (W .ob) (V .ob) (F .obj, n) .equiv)))

{` The layered form of the total space Σ_D (C ≅ D). `}
def SipLaws (ob : Type) (hom : ob → ob → Type) (idn : (a : ob) → hom a a)
  (comp : (a b c : ob) → hom b c → hom a b → hom a c) : Type
  ≔ Σ ((a b : ob) → isSet (hom a b)) (_ ↦
      Product ((a b : ob) (f : hom a b) → Id (hom a b) (comp a b b (idn b) f) f)
        (Product ((a b : ob) (f : hom a b) → Id (hom a b) (comp a a b f (idn a)) f)
          ((a b c d : ob) (f : hom a b) (g : hom b c) (h : hom c d)
            → Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f))))

def SipCompLayer (C : Precat) (ob : Type) (eo : Equiv (C .wild .ob) ob) (hom : ob → ob → Type)
  (eh : (a b : C .wild .ob) → Equiv (C .wild .hom a b) (hom (eo .map a) (eo .map b))) (idn : (x : ob) → hom x x)
  : Type
  ≔ Σ (Σ ((x y z : ob) → hom y z → hom x y → hom x z) (comp ↦
        (a b c : C .wild .ob) (g : C .wild .hom b c) (f : C .wild .hom a b)
        → Id (hom (eo .map a) (eo .map c)) (eh a c .map (C .wild .comp a b c g f))
            (comp (eo .map a) (eo .map b) (eo .map c) (eh b c .map g) (eh a b .map f))))
      (W ↦ SipLaws ob hom idn (W .fst))

def SipIdnLayer (C : Precat) (ob : Type) (eo : Equiv (C .wild .ob) ob) (hom : ob → ob → Type)
  (eh : (a b : C .wild .ob) → Equiv (C .wild .hom a b) (hom (eo .map a) (eo .map b))) : Type
  ≔ Σ (Σ ((x : ob) → hom x x) (idn ↦ (a : C .wild .ob)
          → Id (hom (eo .map a) (eo .map a)) (eh a a .map (C .wild .idn a)) (idn (eo .map a))))
      (Z ↦ SipCompLayer C ob eo hom eh (Z .fst))

def SipHomLayer (C : Precat) (ob : Type) (eo : Equiv (C .wild .ob) ob) : Type
  ≔ Σ (Σ (ob → ob → Type) (hom ↦ (a b : C .wild .ob) → Equiv (C .wild .hom a b) (hom (eo .map a) (eo .map b))))
      (Y ↦ SipIdnLayer C ob eo (Y .fst) (Y .snd))

def SipTotal (C : Precat) : Type
  ≔ Σ (Σ Type (ob ↦ Equiv (C .wild .ob) ob)) (X ↦ SipHomLayer C (X .fst) (X .snd))

def sip_reorganize (C : Precat) : Equiv (Σ Precat (D ↦ PrecatIsoNative C D)) (SipTotal C)
  ≔ quasi_inverse_equiv (Σ Precat (D ↦ PrecatIsoNative C D)) (SipTotal C)
      (u ↦ ((u .fst .wild .ob, (u .snd .fst .obj, u .snd .snd .snd)),
            ((u .fst .wild .hom, a b ↦ (u .snd .fst .mor a b, u .snd .snd .fst a b)),
             ((u .fst .wild .idn, u .snd .fst .map_id),
              ((u .fst .wild .comp, a b c g f ↦ u .snd .fst .map_comp a b c f g),
               (u .fst .homset, (u .fst .wild .lu, (u .fst .wild .ru, u .fst .wild .assoc))))))))
      (s ↦ ((wild ≔ (ob ≔ s .fst .fst,
                     hom ≔ s .snd .fst .fst,
                     idn ≔ s .snd .snd .fst .fst,
                     comp ≔ s .snd .snd .snd .fst .fst,
                     lu ≔ s .snd .snd .snd .snd .snd .fst,
                     ru ≔ s .snd .snd .snd .snd .snd .snd .fst,
                     assoc ≔ s .snd .snd .snd .snd .snd .snd .snd),
             homset ≔ s .snd .snd .snd .snd .fst),
            ((obj ≔ s .fst .snd .map,
              mor ≔ a b ↦ s .snd .fst .snd a b .map,
              map_id ≔ s .snd .snd .fst .snd,
              map_comp ≔ a b c f g ↦ s .snd .snd .snd .fst .snd a b c g f),
             (a b ↦ s .snd .fst .snd a b .equiv, s .fst .snd .equiv))))
      (u ↦ refl u) (s ↦ refl s)

{` The laws of a precategory are propositions once its hom types are sets. `}
def sip_laws_prop (ob : Type) (hom : ob → ob → Type) (idn : (a : ob) → hom a a)
  (comp : (a b c : ob) → hom b c → hom a b → hom a c) : isProp (SipLaws ob hom idn comp)
  ≔ sigma_prop ((a b : ob) → isSet (hom a b)) (_ ↦
        Product ((a b : ob) (f : hom a b) → Id (hom a b) (comp a b b (idn b) f) f)
          (Product ((a b : ob) (f : hom a b) → Id (hom a b) (comp a a b f (idn a)) f)
            ((a b c d : ob) (f : hom a b) (g : hom b c) (h : hom c d)
              → Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f))))
      (ch6c_pi_prop2 ob (_ ↦ ob) (a b ↦ isSet (hom a b)) (a b ↦ isset_isprop (hom a b)))
      (hs ↦ product_prop ((a b : ob) (f : hom a b) → Id (hom a b) (comp a b b (idn b) f) f)
        (Product ((a b : ob) (f : hom a b) → Id (hom a b) (comp a a b f (idn a)) f)
          ((a b c d : ob) (f : hom a b) (g : hom b c) (h : hom c d)
            → Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f)))
        (ch6c_pi_prop3 ob (_ ↦ ob) (a b ↦ hom a b) (a b f ↦ Id (hom a b) (comp a b b (idn b) f) f)
          (a b f ↦ hs a b (comp a b b (idn b) f) f))
        (product_prop ((a b : ob) (f : hom a b) → Id (hom a b) (comp a a b f (idn a)) f)
          ((a b c d : ob) (f : hom a b) (g : hom b c) (h : hom c d)
            → Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f))
          (ch6c_pi_prop3 ob (_ ↦ ob) (a b ↦ hom a b) (a b f ↦ Id (hom a b) (comp a a b f (idn a)) f)
            (a b f ↦ hs a b (comp a a b f (idn a)) f))
          (ch6c_pi_prop4 ob (_ ↦ ob) (_ _ ↦ ob) (_ _ _ ↦ ob)
            (a b c d ↦ (f : hom a b) (g : hom b c) (h : hom c d)
              → Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f))
            (a b c d ↦ ch6c_pi_prop3 (hom a b) (_ ↦ hom b c) (_ _ ↦ hom c d)
              (f g h ↦ Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f))
              (f g h ↦ hs a d (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f))))))

{` Contracting the layers one after another. `}
def sip_total_contractible (C : Precat) : isContr (SipTotal C)
  ≔ let W ≔ C .wild in
    let ob ≔ W .ob in
    let idE ≔ identity_equiv ob in
    let ids : (a b : ob) → Equiv (W .hom a b) (W .hom a b) ≔ a b ↦ identity_equiv (W .hom a b) in
    let e1 ≔ ch6c_sigma_contract_base (Σ Type (o ↦ Equiv ob o)) (X ↦ SipHomLayer C (X .fst) (X .snd))
      (ch6c_equiv_singleton ob) (ob, idE) in
    let e2 ≔ ch6c_sigma_contract_base
      (Σ (ob → ob → Type) (hom ↦ (a b : ob) → Equiv (W .hom a b) (hom a b)))
      (Y ↦ SipIdnLayer C ob idE (Y .fst) (Y .snd))
      (ch6c_family2_equiv_singleton ob (W .hom)) (W .hom, ids) in
    let e3 ≔ ch6c_sigma_contract_base
      (Σ ((x : ob) → W .hom x x) (idn ↦ (a : ob) → Id (W .hom a a) (W .idn a) (idn a)))
      (Z ↦ SipCompLayer C ob idE (W .hom) ids (Z .fst))
      (ch6c_fun_singleton1 ob (a ↦ W .hom a a) (W .idn)) (W .idn, a ↦ refl (W .idn a)) in
    let e4 ≔ ch6c_sigma_contract_base
      (Σ ((x y z : ob) → W .hom y z → W .hom x y → W .hom x z) (comp ↦
        (a b c : ob) (g : W .hom b c) (f : W .hom a b) → Id (W .hom a c) (W .comp a b c g f) (comp a b c g f)))
      (V ↦ SipLaws ob (W .hom) (W .idn) (V .fst))
      (ch6c_fun_singleton5 ob (_ ↦ ob) (_ _ ↦ ob) (_ b c ↦ W .hom b c) (a b _ _ ↦ W .hom a b)
        (a _ c _ _ ↦ W .hom a c) (W .comp))
      (W .comp, a b c g f ↦ refl (W .comp a b c g f)) in
    let laws : SipLaws ob (W .hom) (W .idn) (W .comp) ≔ (C .homset, (W .lu, (W .ru, W .assoc))) in
    let hl : isContr (SipLaws ob (W .hom) (W .idn) (W .comp))
      ≔ (laws, x ↦ sip_laws_prop ob (W .hom) (W .idn) (W .comp) x laws) in
    ch6c_contr_transfer (SipLaws ob (W .hom) (W .idn) (W .comp)) (SipTotal C)
      (canonical_inverse_equiv (SipTotal C) (SipLaws ob (W .hom) (W .idn) (W .comp))
        (compose_equiv (SipTotal C) (SipHomLayer C ob idE) (SipLaws ob (W .hom) (W .idn) (W .comp)) e1
          (compose_equiv (SipHomLayer C ob idE) (SipIdnLayer C ob idE (W .hom) ids)
            (SipLaws ob (W .hom) (W .idn) (W .comp)) e2
            (compose_equiv (SipIdnLayer C ob idE (W .hom) ids) (SipCompLayer C ob idE (W .hom) ids (W .idn))
              (SipLaws ob (W .hom) (W .idn) (W .comp)) e3 e4))))
      hl

def precat_iso_total_contractible (C : Precat) : isContr (Σ Precat (D ↦ PrecatIsomorphism C D))
  ≔ ch6c_contr_transfer (Σ Precat (D ↦ PrecatIsoNative C D)) (Σ Precat (D ↦ PrecatIsomorphism C D))
      (canonical_inverse_equiv (Σ Precat (D ↦ PrecatIsomorphism C D)) (Σ Precat (D ↦ PrecatIsoNative C D))
        (family_equiv Precat (D ↦ PrecatIsomorphism C D) (D ↦ PrecatIsoNative C D) (precat_iso_native_equiv C)))
      (ch6c_contr_transfer (SipTotal C) (Σ Precat (D ↦ PrecatIsoNative C D))
        (canonical_inverse_equiv (Σ Precat (D ↦ PrecatIsoNative C D)) (SipTotal C) (sip_reorganize C))
        (sip_total_contractible C))

{` The footnote to cor:Cat-ua: identifications of precategories are
   equivalent to isomorphisms of precategories, via the map defined by
   path induction. `}
def precategory_path_to_isomorphism_is_equiv (C D : Precat)
  : isEquiv (Id Precat C D) (PrecatIsomorphism C D) (precategory_path_to_isomorphism C D)
  ≔ fiberwise_from_total Precat (D ↦ Id Precat C D) (D ↦ PrecatIsomorphism C D) (precategory_path_to_isomorphism C)
      (cat_contractible_map_is_equiv (Σ Precat (D ↦ Id Precat C D)) (Σ Precat (D ↦ PrecatIsomorphism C D))
        (totalize Precat (D ↦ Id Precat C D) (D ↦ PrecatIsomorphism C D) (precategory_path_to_isomorphism C))
        (iscontr_idfrom Precat C) (precat_iso_total_contractible C)) D

def precategory_path_equiv (C D : Precat) : BookEquiv (Id Precat C D) (PrecatIsomorphism C D)
  ≔ book_equivalence (Id Precat C D) (PrecatIsomorphism C D)
      (precategory_path_to_isomorphism C D, precategory_path_to_isomorphism_is_equiv C D)

{` Litmus: the map sends refl to the identity isomorphism, whose functor
   is the identity on objects. `}
def precategory_path_equiv_refl_obj (C : Precat) (c : C .wild .ob)
  : Id (C .wild .ob) (precat_identity_isomorphism C .fst .obj c) c
  ≔ refl c
