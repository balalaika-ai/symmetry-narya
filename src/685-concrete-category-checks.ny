export "603-adjunctions-and-equivalences"

{` Litmus checks for the chapter-6 core: a small concrete category (the
   walking arrow 0 → 1) whose composition computes by refl and which is
   univalent, and a non-trivial use of the univalence of the category of
   sets. `}

def ArrowHom (a b : Bool) : Type ≔ match a, b [
  | false., false. ↦ Unit
  | false., true. ↦ Unit
  | true., false. ↦ Empty
  | true., true. ↦ Unit ]

def arrow_hom_prop (a b : Bool) : isProp (ArrowHom a b) ≔ match a, b [
  | false., false. ↦ unit_prop
  | false., true. ↦ unit_prop
  | true., false. ↦ empty_prop
  | true., true. ↦ unit_prop ]

def arrow_idn (a : Bool) : ArrowHom a a ≔ match a [ false. ↦ star. | true. ↦ star. ]

def arrow_comp (a b c : Bool) : ArrowHom b c → ArrowHom a b → ArrowHom a c ≔ match a, b, c [
  | false., false., false. ↦ g f ↦ star.
  | false., false., true. ↦ g f ↦ star.
  | false., true., false. ↦ g f ↦ match g []
  | false., true., true. ↦ g f ↦ star.
  | true., false., false. ↦ g f ↦ match f []
  | true., false., true. ↦ g f ↦ match f []
  | true., true., false. ↦ g f ↦ match g []
  | true., true., true. ↦ g f ↦ star. ]

def WalkingArrowWild : WildPrecat
  ≔ (ob ≔ Bool,
     hom ≔ ArrowHom,
     idn ≔ arrow_idn,
     comp ≔ arrow_comp,
     lu ≔ a b f ↦ arrow_hom_prop a b (arrow_comp a b b (arrow_idn b) f) f,
     ru ≔ a b f ↦ arrow_hom_prop a b (arrow_comp a a b f (arrow_idn a)) f,
     assoc ≔ a b c d f g h ↦ arrow_hom_prop a d (arrow_comp a c d h (arrow_comp a b c g f))
       (arrow_comp a b d (arrow_comp b c d h g) f))

def walking_arrow_homset : HasHomSets WalkingArrowWild
  ≔ a b ↦ prop_is_set (ArrowHom a b) (arrow_hom_prop a b)

{` Composition computes: the composite 0 → 0 → 1 is the arrow 0 → 1. `}
def walking_arrow_compose_check
  : Id (ArrowHom false. true.) (WalkingArrowWild .comp false. false. true. star. star.) star.
  ≔ refl (star. : Unit)

def walking_arrow_iso_prop (a b : Bool) : isProp (CatIso WalkingArrowWild a b)
  ≔ sigma_prop (ArrowHom a b) (f ↦ CatIsIso WalkingArrowWild a b f) (arrow_hom_prop a b)
      (f ↦ cat_is_iso_prop WalkingArrowWild a b f)

{` The arrow 0 → 1 is not an isomorphism (an inverse would be an arrow
   1 → 0). `}
def walking_arrow_not_iso (i : CatIsIso WalkingArrowWild false. true. star.) : Empty ≔ i .fst .fst

def walking_arrow_paths_iso (a b : Bool) : Equiv (Id Bool a b) (CatIso WalkingArrowWild a b)
  ≔ match a, b [
  | false., false. ↦ iff_equiv (Id Bool false. false.) (CatIso WalkingArrowWild false. false.)
      (bool_set false. false.) (walking_arrow_iso_prop false. false.)
      (_ ↦ cat_identity_iso WalkingArrowWild false.) (_ ↦ refl (false. : Bool))
  | false., true. ↦ iff_equiv (Id Bool false. true.) (CatIso WalkingArrowWild false. true.)
      (bool_set false. true.) (walking_arrow_iso_prop false. true.)
      (p ↦ absurd (CatIso WalkingArrowWild false. true.) (bool_encode false. true. p))
      (e ↦ absurd (Id Bool false. true.) (e .snd .fst .fst))
  | true., false. ↦ iff_equiv (Id Bool true. false.) (CatIso WalkingArrowWild true. false.)
      (bool_set true. false.) (walking_arrow_iso_prop true. false.)
      (p ↦ absurd (CatIso WalkingArrowWild true. false.) (bool_encode true. false. p))
      (e ↦ absurd (Id Bool true. false.) (e .fst))
  | true., true. ↦ iff_equiv (Id Bool true. true.) (CatIso WalkingArrowWild true. true.)
      (bool_set true. true.) (walking_arrow_iso_prop true. true.)
      (_ ↦ cat_identity_iso WalkingArrowWild true.) (_ ↦ refl (true. : Bool)) ]

def walking_arrow_univalent : IsUnivalentCat WalkingArrowWild
  ≔ cat_univalent_from_equivalences WalkingArrowWild walking_arrow_paths_iso

def WalkingArrowCat : Category ≔ (WalkingArrowWild, walking_arrow_homset, walking_arrow_univalent)

{` Univalence of the category of sets is not vacuous: the loop at Bool
   corresponding to negation is not reflexivity, since applying idtoiso
   would identify negation with the identity. `}
def set_cat_negation_loop : Id (SetCat .wild .ob) set_cat_bool set_cat_bool
  ≔ cat_isotoid (SetCat .wild) (SetCat .univalent) set_cat_bool set_cat_bool set_cat_negation_iso

{` Projections are taken in separate definitions, abstracting over the
   path, to avoid the E0500 projection bug (docs/narya-notes.md). `}
def cat_iso_arrow_path (C : WildPrecat) (a b : C .ob) (e d : CatIso C a b) (r : Id (CatIso C a b) e d)
  : Id (C .hom a b) (e .fst) (d .fst)
  ≔ refl ((u ↦ u .fst) : CatIso C a b → C .hom a b) r

def set_cat_negation_not_identity (q : Id (Bool → Bool) bool_not (x ↦ x)) : Empty
  ≔ bool_encode false. true. (q (refl (true. : Bool)))

def set_cat_negation_loop_nontrivial
  (r : Id (Id (SetCat .wild .ob) set_cat_bool set_cat_bool) set_cat_negation_loop (refl set_cat_bool))
  : Empty
  ≔ let W ≔ SetCat .wild in
    let e : Id (CatIso W set_cat_bool set_cat_bool) set_cat_negation_iso (cat_identity_iso W set_cat_bool)
      ≔ concat (CatIso W set_cat_bool set_cat_bool) set_cat_negation_iso
          (cat_idtoiso W set_cat_bool set_cat_bool (refl set_cat_bool)) (cat_identity_iso W set_cat_bool)
          (concat (CatIso W set_cat_bool set_cat_bool) set_cat_negation_iso
            (cat_idtoiso W set_cat_bool set_cat_bool set_cat_negation_loop)
            (cat_idtoiso W set_cat_bool set_cat_bool (refl set_cat_bool))
            (inverse (CatIso W set_cat_bool set_cat_bool)
              (cat_idtoiso W set_cat_bool set_cat_bool set_cat_negation_loop) set_cat_negation_iso
              (cat_idtoiso_isotoid W (SetCat .univalent) set_cat_bool set_cat_bool set_cat_negation_iso))
            (refl (cat_idtoiso W set_cat_bool set_cat_bool) r))
          (inverse (CatIso W set_cat_bool set_cat_bool) (cat_identity_iso W set_cat_bool)
            (cat_idtoiso W set_cat_bool set_cat_bool (refl set_cat_bool)) (cat_idtoiso_refl W set_cat_bool)) in
    set_cat_negation_not_identity (cat_iso_arrow_path W set_cat_bool set_cat_bool set_cat_negation_iso
      (cat_identity_iso W set_cat_bool) e)
