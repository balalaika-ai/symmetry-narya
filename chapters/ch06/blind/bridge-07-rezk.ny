import "bridge-00-core"
import "bridge-03-functors"
import "bridge-05-yoneda"
import "bridge-06-equivalences"
import "../../../src/675-flagged-category-equivalence"
import "../../../src/676-rezk-completion-smallness"
import "../../../src/677-one-types-are-groupoids"
import "../../../src/678-rezk-completion-one-truncation"
import "../../../src/679-chicken-or-egg"

{` Bridges for cats.tex, section "Equivalences of categories" from
   def:Rezk-completion on (blind file 07).

   def:Rezk-completion. Blind L(C) is the full subcategory of the blind
   presheaf precategory on the merely representable presheaves; ours is the
   full subcategory of PresheafCategory on MerelyRepresentable. The record
   translation of presheaves gives a functor T : L_blind(C) → L(C) that is
   the identity on arrows up to the translation of natural transformations,
   fully faithful and (split) essentially surjective; with univalence of
   L_blind(C) (from ours, below) it is an equivalence, hence an
   identification of categories (cor:Cat-ua, module 674). `}

def BridgeBR (C : BlindPrecat) : WildPrecat ≔ bridge_w (blind_rezk C .fst)

def BridgeOR (C : BlindPrecat) : WildPrecat ≔ RezkCompletion (bridge_p C) .wild

{` Prose around def:Rezk-completion: L(C) is a category (univalence of the
   functor category of module 621, transferred, and def:full-subcat). `}
def bridge_rezk_univalent (C : BlindPrecat) : BlindIsUnivalent (blind_rezk C .fst)
  ≔ full_subcat_univalent (BridgeFP (blind_op (C .fst)) blind_set_precat) (BlindIsRepr C)
      (bridge_fp_univalent (blind_op (C .fst)) blind_set_precat
        (functor_wild_univalent (OppositeWild (bridge_w (C .fst))) SetCat))

def bridge_def_rezk_is_category : blind_def_rezk_is_category ≔ bridge_rezk_univalent

def BridgeBRC (C : BlindPrecat) : Category ≔ bridge_c (blind_rezk C, bridge_rezk_univalent C)

def bridge_repr_to (C : BlindPrecat) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst))
  (r : BlindIsRepr C F .fst) : MerelyRepresentable (bridge_p C) (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) F) .fst
  ≔ bridge_mere_map (BlindRepresentation C F)
      (IsRepresentable (bridge_p C) (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) F))
      (bridge_def_representation C F .map) r

def bridge_repr_from (C : BlindPrecat) (G : WildFunctor (OppositeWild (bridge_w (C .fst))) SetWild)
  (r : MerelyRepresentable (bridge_p C) G .fst)
  : BlindIsRepr C (bridge_f_inv (blind_op (C .fst)) (blind_set_precat .fst) G) .fst
  ≔ bridge_mere_map (IsRepresentable (bridge_p C) G)
      (BlindRepresentation C (bridge_f_inv (blind_op (C .fst)) (blind_set_precat .fst) G))
      (equiv_inverse_map (BlindRepresentation C (bridge_f_inv (blind_op (C .fst)) (blind_set_precat .fst) G))
         (IsRepresentable (bridge_p C) G)
         (bridge_def_representation C (bridge_f_inv (blind_op (C .fst)) (blind_set_precat .fst) G))) r

def bridge_rezk_functor (C : BlindPrecat) : WildFunctor (BridgeBR C) (BridgeOR C)
  ≔ (obj ≔ x ↦ (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (x .fst), bridge_repr_to C (x .fst) (x .snd)),
     mor ≔ x y ↦ bridge_nt (blind_op (C .fst)) (blind_set_precat .fst) (x .fst) (y .fst),
     map_id ≔ x ↦ refl (nat_trans_identity (OppositeWild (bridge_w (C .fst))) SetWild
       (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (x .fst))),
     map_comp ≔ x y z al be ↦ refl (bridge_nt (blind_op (C .fst)) (blind_set_precat .fst) (x .fst) (z .fst)
       (blind_nat_comp (blind_op (C .fst)) (blind_set_precat .fst) (x .fst) (y .fst) (z .fst) be al)))

def bridge_rezk_obj_inv (C : BlindPrecat) (x : BridgeOR C .ob) : BridgeBR C .ob
  ≔ (bridge_f_inv (blind_op (C .fst)) (blind_set_precat .fst) (x .fst), bridge_repr_from C (x .fst) (x .snd))

def bridge_rezk_obj_equiv (C : BlindPrecat) : Equiv (BridgeOR C .ob) (BridgeBR C .ob)
  ≔ quasi_inverse_equiv (BridgeOR C .ob) (BridgeBR C .ob) (bridge_rezk_obj_inv C) (bridge_rezk_functor C .obj)
      (x ↦ subtype_equal (WildFunctor (OppositeWild (bridge_w (C .fst))) SetWild)
         (G ↦ MerelyRepresentable (bridge_p C) G .fst) (G ↦ MerelyRepresentable (bridge_p C) G .snd)
         (bridge_rezk_functor C .obj (bridge_rezk_obj_inv C x)) x (refl (x .fst)))
      (y ↦ subtype_equal (BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst))
         (G ↦ BlindIsRepr C G .fst) (G ↦ BlindIsRepr C G .snd)
         (bridge_rezk_obj_inv C (bridge_rezk_functor C .obj y)) y (refl (y .fst)))

def bridge_rezk_functor_ff (C : BlindPrecat)
  : IsFullyFaithful (BridgeBR C) (BridgeOR C) (bridge_rezk_functor C)
  ≔ fully_faithful_from_equivs (BridgeBR C) (BridgeOR C) (bridge_rezk_functor C) (x y ↦
      book_equivalence (BlindNatTrans (blind_op (C .fst)) (blind_set_precat .fst) (x .fst) (y .fst))
        (WildNatTrans (OppositeWild (bridge_w (C .fst))) SetWild
          (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (x .fst)) (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (y .fst)))
        (bridge_def_nat_trans (blind_op (C .fst)) (blind_set_precat .fst) (x .fst) (y .fst)) .equiv)

def bridge_rezk_functor_eso (C : BlindPrecat) : IsEso (BridgeBR C) (BridgeOR C) (bridge_rezk_functor C)
  ≔ d ↦ mere (Σ (BridgeBR C .ob) (x ↦ CatIso (BridgeOR C) (bridge_rezk_functor C .obj x) d))
      (bridge_rezk_obj_inv C d, cat_identity_iso (PresheafCategory (bridge_p C) .wild) (d .fst))

def bridge_rezk_equivalence (C : BlindPrecat) : CatEquivalence (BridgeBR C) (BridgeOR C)
  ≔ (bridge_rezk_functor C,
     ff_eso_is_cat_equivalence (BridgeBRC C) (category_precat (RezkCompletion (bridge_p C))) (bridge_rezk_functor C)
       (bridge_rezk_functor_ff C) (bridge_rezk_functor_eso C))

def bridge_rezk_path (C : BlindPrecat) : Id Category (BridgeBRC C) (RezkCompletion (bridge_p C))
  ≔ category_path_from_equivalence (BridgeBRC C) (RezkCompletion (bridge_p C)) (bridge_rezk_equivalence C)

{` η: the blind unit followed by T is ours (rezk_unit) on objects up to the
   (propositional) representability proof, and on arrows on the nose. `}
def bridge_rezk_unit_obj (C : BlindPrecat) (c : C .fst .ob)
  : Id (BridgeOR C .ob) (bridge_rezk_functor C .obj (blind_rezk_eta C .fob c)) (rezk_unit (bridge_p C) .obj c)
  ≔ subtype_equal (WildFunctor (OppositeWild (bridge_w (C .fst))) SetWild)
      (G ↦ MerelyRepresentable (bridge_p C) G .fst) (G ↦ MerelyRepresentable (bridge_p C) G .snd)
      (bridge_rezk_functor C .obj (blind_rezk_eta C .fob c)) (rezk_unit (bridge_p C) .obj c)
      (refl (representable_presheaf (bridge_p C) c))

{` thm:Rezk-completion. (1) η is a weak equivalence: full faithfulness is
   ours for yo (cor:yo-ff bridge; the arrows of L are those of the
   presheaf category), essential surjectivity holds by definition on both
   sides (rezk_unit_eso is d ↦ d.snd). (2) smallness, from
   rezk_completion_essentially_small transported along T. `}
def bridge_rezk_eta_we (C : BlindPrecat) : BlindIsWeakEquiv (C .fst) (blind_rezk C .fst) (blind_rezk_eta C)
  ≔ (bridge_cor_yo_ff C, d ↦ d .snd)

def bridge_rezk_ess_small (C : BlindPrecat) (U : Universe) (h : IsEssentiallySmallPrecat U (category_precat (RezkCompletion (bridge_p C))))
  : BlindIsEssUSmall U (blind_rezk C .fst)
  ≔ (essentially_small_equiv U (BridgeOR C .ob) (BridgeBR C .ob) (bridge_rezk_obj_equiv C) (h .fst),
     a b ↦ essentially_small_equiv U
       (WildNatTrans (OppositeWild (bridge_w (C .fst))) SetWild
          (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (a .fst)) (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (b .fst)))
       (BlindNatTrans (blind_op (C .fst)) (blind_set_precat .fst) (a .fst) (b .fst))
       (canonical_inverse_equiv (BlindNatTrans (blind_op (C .fst)) (blind_set_precat .fst) (a .fst) (b .fst))
          (WildNatTrans (OppositeWild (bridge_w (C .fst))) SetWild
             (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (a .fst)) (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (b .fst)))
          (bridge_def_nat_trans (blind_op (C .fst)) (blind_set_precat .fst) (a .fst) (b .fst)))
       (h .snd (bridge_rezk_functor C .obj a) (bridge_rezk_functor C .obj b)))

def bridge_thm_rezk_completion : blind_thm_rezk_completion
  ≔ C ↦ (bridge_rezk_eta_we C,
         U rep h ↦ bridge_rezk_ess_small C U (rezk_completion_essentially_small U rep (bridge_p C) h))

{` xca:Rezk-completion-locally-small (ours also proves the strict version
   rezk_completion_locally_small). `}
def bridge_xca_rezk_locally_small : blind_xca_rezk_locally_small
  ≔ U C h a b ↦ essentially_small_equiv U
       (WildNatTrans (OppositeWild (bridge_w (C .fst))) SetWild
          (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (a .fst)) (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (b .fst)))
       (BlindNatTrans (blind_op (C .fst)) (blind_set_precat .fst) (a .fst) (b .fst))
       (canonical_inverse_equiv (BlindNatTrans (blind_op (C .fst)) (blind_set_precat .fst) (a .fst) (b .fst))
          (WildNatTrans (OppositeWild (bridge_w (C .fst))) SetWild
             (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (a .fst)) (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (b .fst)))
          (bridge_def_nat_trans (blind_op (C .fst)) (blind_set_precat .fst) (a .fst) (b .fst)))
       (rezk_completion_locally_essentially_small U (bridge_p C)
          (x y ↦ small_essentially_small U (C .fst .hom x y) (h x y))
          (bridge_rezk_functor C .obj a) (bridge_rezk_functor C .obj b))

{` thm:1types-are-groupoids. `}
def bridge_tgpd (G : Gpd) : BlindGpd ≔ (bridge_c_inv (G .fst), G .snd)

def bridge_def_gpd : Equiv Gpd BlindGpd
  ≔ quasi_inverse_equiv Gpd BlindGpd bridge_tgpd (G ↦ (bridge_c (G .fst), G .snd)) (G ↦ refl G) (G ↦ refl G)

def bridge_path_gpd_proofs (X : BlindOneTypes) : BlindPathGpdProofs (X .fst)
  ≔ (X .snd, (path_wild_univalent (X .fst), path_wild_invertible (X .fst)))

def bridge_thm_1types_are_groupoids : blind_thm_1types_are_groupoids
  ≔ ((A B hA hB ↦ book_two_out_of_three_composite
         (BlindWildFunctor (blind_path_wild_precat A) (blind_path_wild_precat B))
         (WildFunctor (PathWild A) (PathWild B)) (A → B)
         (bridge_f (blind_path_wild_precat A) (blind_path_wild_precat B)) (F ↦ F .fob) (F ↦ F .obj)
         (refl ((F ↦ F .fob) : BlindWildFunctor (blind_path_wild_precat A) (blind_path_wild_precat B) → A → B))
         (book_equivalence (BlindWildFunctor (blind_path_wild_precat A) (blind_path_wild_precat B))
            (WildFunctor (PathWild A) (PathWild B))
            (bridge_def_functor (blind_path_wild_precat A) (blind_path_wild_precat B)) .equiv)
         (one_types_functor_groupoid_projection A B hA hB)),
     (bridge_path_gpd_proofs,
      book_two_out_of_three_composite BlindOneTypes Gpd BlindGpd path_gpd
        (X ↦ (((blind_path_wild_precat (X .fst), bridge_path_gpd_proofs X .fst), bridge_path_gpd_proofs X .snd .fst),
              bridge_path_gpd_proofs X .snd .snd))
        bridge_tgpd
        (refl ((X ↦ bridge_tgpd (path_gpd X)) : BlindOneTypes → BlindGpd))
        one_types_groupoids_is_equiv
        (book_equivalence Gpd BlindGpd bridge_def_gpd .equiv)))

{` def:flagged-cat. `}
def bridge_tfl (X : FlCat) : BlindFlCat ≔ (bridge_c_inv (X .fst), X .snd)

def bridge_def_flagged_cat : Equiv FlCat BlindFlCat
  ≔ quasi_inverse_equiv FlCat BlindFlCat bridge_tfl (Y ↦ (bridge_c (Y .fst), Y .snd)) (X ↦ refl X) (Y ↦ refl Y)

{` thm:flagged-cat-equiv. Blind L(C) with its flag is identified with ours
   (rezk_flag) via the equivalence T and ours flagged_path_from_equivalence
   (module 675); the blind map is homotopic to ours conjugated by the
   record translations, and ours is an equivalence (precat_flagged_equiv). `}
def bridge_rezk_obj_surjective (C : BlindPrecat)
  : Surjective (C .fst .ob) (blind_rezk C .fst .ob) (blind_rezk_eta C .fob)
  ≔ eso_univalent_obj_surjective (bridge_w (C .fst)) (BridgeBR C) (bridge_rezk_univalent C)
      (bridge_f (C .fst) (blind_rezk C .fst) (blind_rezk_eta C)) (bridge_rezk_eta_we C .snd)

def bridge_blind_flag (C : BlindPrecat) : BlindFlCat
  ≔ ((blind_rezk C, bridge_rezk_univalent C), (C .fst .ob, (blind_rezk_eta C .fob, bridge_rezk_obj_surjective C)))

def bridge_flag_homotopy (C : BlindPrecat)
  : Id BlindFlCat (bridge_blind_flag C) (bridge_tfl (rezk_flag (bridge_p C)))
  ≔ refl bridge_tfl
      (flagged_path_from_equivalence (BridgeBRC C) (RezkCompletion (bridge_p C)) (bridge_rezk_equivalence C) (C .fst .ob)
        (blind_rezk_eta C .fob) (bridge_rezk_obj_surjective C)
        (rezk_unit (bridge_p C) .obj) (rezk_unit_obj_surjective (bridge_p C))
        (bridge_rezk_unit_obj C))

def bridge_thm_flagged_cat_equiv : blind_thm_flagged_cat_equiv
  ≔ (bridge_rezk_univalent,
     (bridge_rezk_obj_surjective,
      book_two_out_of_three_composite BlindPrecat BlindFlCat BlindFlCat
        (C ↦ bridge_tfl (rezk_flag (bridge_p C))) bridge_blind_flag (x ↦ x)
        (funext BlindPrecat (_ ↦ BlindFlCat) (C ↦ bridge_tfl (rezk_flag (bridge_p C))) bridge_blind_flag
           (C ↦ inverse BlindFlCat (bridge_blind_flag C) (bridge_tfl (rezk_flag (bridge_p C))) (bridge_flag_homotopy C)))
        (book_equivalence BlindPrecat BlindFlCat
           (compose_equiv BlindPrecat Precat BlindFlCat bridge_def_precat
              (compose_equiv Precat FlCat BlindFlCat precat_flagged_equiv bridge_def_flagged_cat)) .equiv)
        (book_equivalence BlindFlCat BlindFlCat (identity_equiv BlindFlCat) .equiv)))

{` rem:chicken-or-egg. Cat → PreCat is an embedding (ours,
   category_precat_embedding, on translated fibers); L retracts it: blind
   L(C) = ours L(C) (via T) = C (ours, rezk_completion_retraction). `}
def bridge_cat_fiber_equiv (P : BlindPrecat)
  : Equiv (BookFiber BlindCat BlindPrecat (C ↦ C .fst) P) (BookFiber Category Precat category_precat (bridge_p P))
  ≔ quasi_inverse_equiv (BookFiber BlindCat BlindPrecat (C ↦ C .fst) P) (BookFiber Category Precat category_precat (bridge_p P))
      (t ↦ (bridge_c (t .fst), refl bridge_p (t .snd)))
      (t ↦ (bridge_c_inv (t .fst), refl ((Q ↦ (bridge_w_inv (Q .wild), Q .homset)) : Precat → BlindPrecat) (t .snd)))
      (t ↦ refl t) (t ↦ refl t)

def bridge_rem_chicken_or_egg : blind_rem_chicken_or_egg
  ≔ (P ↦ prop_from_equiv (BookFiber BlindCat BlindPrecat (C ↦ C .fst) P)
           (BookFiber Category Precat category_precat (bridge_p P)) (bridge_cat_fiber_equiv P)
           (category_precat_embedding (bridge_p P)),
     (bridge_rezk_univalent,
      C ↦ refl bridge_c_inv
        (concat Category (BridgeBRC (C .fst)) (RezkCompletion (bridge_p (C .fst))) (bridge_c C)
           (bridge_rezk_path (C .fst)) (rezk_completion_retraction (bridge_c C)))))

{` xca:Rezk-completion-1trunc. Ours (modules 672, 678): the structure
   TruncPathWild with |refl| and |p · q| by refl, its invertibility, and
   L(TruncPath A) = path groupoid of ‖A‖₁; composed with blind L = ours L. `}
def bridge_trunc_path_precat (A : Type) : BlindPrecat
  ≔ (blind_wild_of_str A (x y ↦ SetTrunc (Id A x y)) (bridge_wstr_of (TruncPathWild A)), x y ↦ set_trunc_set (Id A x y))

def bridge_xca_rezk_1trunc : blind_xca_rezk_1trunc
  ≔ A ↦ (bridge_wstr_of (TruncPathWild A),
         ((x ↦ refl (set_trunc (Id A x x) (refl x))),
          ((x y z p q ↦ trunc_path_comp_compute A x y z p q),
           (trunc_path_invertible A,
            bridge_ce_inv_map (blind_rezk (bridge_trunc_path_precat A) .fst) (blind_path_wild_precat (OneTrunc A))
              (category_path_to_equivalence (BridgeBRC (bridge_trunc_path_precat A)) (one_trunc_category A)
                 (concat Category (BridgeBRC (bridge_trunc_path_precat A)) (RezkCompletion (trunc_path_precat A))
                    (one_trunc_category A)
                    (bridge_rezk_path (bridge_trunc_path_precat A))
                    (inverse Category (one_trunc_category A) (RezkCompletion (trunc_path_precat A))
                       (trunc_path_rezk_path A))))))))
