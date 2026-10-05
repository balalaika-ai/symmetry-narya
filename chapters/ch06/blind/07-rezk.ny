export "06-equivalences"

{` Blind statements, chapter 6, section "Equivalences of categories" from
   def:Rezk-completion on. `}

{` def:Rezk-completion. L(C) = full subcategory of Set^{C^op} on the
   (merely) representable presheaves; η factors yo. `}
def blind_rezk (C : BlindPrecat) : BlindPrecat ≔ blind_full_subprecat (blind_psh C) (BlindIsRepr C)

def blind_rezk_eta (C : BlindPrecat) : BlindWildFunctor (C .fst) (blind_rezk C .fst)
  ≔ ((c ↦ (blind_yo_ob C c,
           (P _ k ↦ k (c, blind_id_iso (blind_psh C .fst) (blind_yo_ob C c))))),
     blind_yoneda C .fhom, blind_yoneda C .fid, blind_yoneda C .fcomp)

{` Prose around the definition: L(C) is a category. `}
def blind_def_rezk_is_category : Type ≔ (C : BlindPrecat) → BlindIsUnivalent (blind_rezk C .fst)

{` thm:Rezk-completion. Essential U-smallness of a precategory: objects and
   all hom-sets essentially U-small (as in the proof). The book's
   Replacement principle (used in the proof) is an explicit hypothesis. `}
def BlindIsEssUSmall (U : Universe) (C : BlindWildPrecat) : Type
  ≔ Product (EssentiallySmall U (C .ob)) ((a b : C .ob) → EssentiallySmall U (C .hom a b))

def blind_thm_rezk_completion : Type
  ≔ (C : BlindPrecat)
    → Product (BlindIsWeakEquiv (C .fst) (blind_rezk C .fst) (blind_rezk_eta C))
        ((U : Universe) → Replacement U → BlindIsEssUSmall U (C .fst) → BlindIsEssUSmall U (blind_rezk C .fst))

{` xca:Rezk-completion-locally-small. The hom-types of L(C) are types of
   natural transformations, so only essential local smallness can hold;
   the hypothesis is local smallness of C as in rem:cat-sizes. `}
def blind_xca_rezk_locally_small : Type
  ≔ (U : Universe) (C : BlindPrecat) → BlindIsLocallyUSmall U (C .fst)
    → (a b : blind_rezk C .fst .ob) → EssentiallySmall U (blind_rezk C .fst .hom a b)

{` thm:1types-are-groupoids. Gpd = groupoids among categories; the path
   groupoid of a 1-type needs the category and pregroupoid proofs, which are
   included in the statement (they are propositions). `}
def BlindOneTypes : Type ≔ Σ Type isGroupoid
def BlindGpd : Type ≔ Σ BlindCat (C ↦ BlindIsPregroupoid (C .fst .fst))

def BlindPathGpdProofs (X : Type) : Type
  ≔ Product ((x y : X) → isSet (Id X x y))
      (Product (BlindIsUnivalent (blind_path_wild_precat X)) (BlindIsPregroupoid (blind_path_wild_precat X)))

def blind_thm_1types_are_groupoids : Type
  ≔ Product
      ((A B : Type) → isGroupoid A → isGroupoid B
        → BookIsEquiv (BlindWildFunctor (blind_path_wild_precat A) (blind_path_wild_precat B)) (A → B) (F ↦ F .fob))
      (Σ ((X : BlindOneTypes) → BlindPathGpdProofs (X .fst)) (pf ↦
         BookIsEquiv BlindOneTypes BlindGpd
           (X ↦ (((blind_path_wild_precat (X .fst), pf X .fst), pf X .snd .fst), pf X .snd .snd))))

{` xca:Rezk-completion-1trunc. The path pregroupoid with ‖x = y‖₀, with
   identity |refl| and composition |q| ∘ |p| = |p · q|; its Rezk completion
   is equivalent to the path groupoid of ‖A‖₁ (= Trunc 2 A). `}
def blind_wild_of_str (Ob : Type) (hom : Ob → Ob → Type) (s : BlindWildPrecatStr Ob hom) : BlindWildPrecat
  ≔ (Ob, hom, s .idn, s .comp, s .lunit, s .runit, s .assoc)

def blind_xca_rezk_1trunc : Type
  ≔ (A : Type)
    → Σ (BlindWildPrecatStr A (x y ↦ SetTrunc (Id A x y))) (s ↦
        let P : BlindPrecat ≔ (blind_wild_of_str A (x y ↦ SetTrunc (Id A x y)) s, (x y ↦ set_trunc_set (Id A x y))) in
        Product ((x : A) → Id (SetTrunc (Id A x x)) (s .idn x) (set_trunc (Id A x x) (refl x)))
          (Product ((x y z : A) (p : Id A x y) (q : Id A y z)
                      → Id (SetTrunc (Id A x z)) (s .comp x y z (set_trunc (Id A y z) q) (set_trunc (Id A x y) p))
                          (set_trunc (Id A x z) (concat A x y z p q)))
             (Product (BlindIsPregroupoid (P .fst))
                (BlindCatEquiv (blind_rezk P .fst) (blind_path_wild_precat (Trunc (suc. (suc. zero.)) A))))))

{` def:flagged-cat. `}
def BlindFlCat : Type
  ≔ Σ BlindCat (C ↦ Σ Type (A ↦ Σ (A → C .fst .fst .ob) (f ↦ Surjective A (C .fst .fst .ob) f)))

{` thm:flagged-cat-equiv. The book says "sending a category C" but the domain
   is PreCat (typo for precategory). L(C) as a category and the
   surjectivity of Ob(η) are proofs supplied in the statement (propositions). `}
def blind_thm_flagged_cat_equiv : Type
  ≔ Σ ((C : BlindPrecat) → BlindIsUnivalent (blind_rezk C .fst)) (lu ↦
      Σ ((C : BlindPrecat) → Surjective (C .fst .ob) (blind_rezk C .fst .ob) (blind_rezk_eta C .fob)) (sj ↦
        BookIsEquiv BlindPrecat BlindFlCat
          (C ↦ ((blind_rezk C, lu C), (C .fst .ob, (blind_rezk_eta C .fob, sj C))))))

{` rem:chicken-or-egg: Cat → PreCat is an injection and L is a retraction of it. `}
def blind_rem_chicken_or_egg : Type
  ≔ Product (IsEmbedding BlindCat BlindPrecat (C ↦ C .fst))
      (Σ ((C : BlindPrecat) → BlindIsUnivalent (blind_rezk C .fst)) (lu ↦
         (C : BlindCat) → Id BlindCat (blind_rezk (C .fst), lu (C .fst)) C))
