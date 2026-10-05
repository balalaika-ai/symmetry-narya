export "880-free-groups-iterated-wedges"

{` Further properties of the constructed free groups (module 877):
   the universal property Hom(F_S, G) ≃ (S → USym G) by evaluation at the
   generators, decidable equality of the symmetries (F_S is a decidable
   group), and the sum lemma F_{S+T} = F_S ∨ F_T for the constructed groups. `}

{` Hom(F_S, G) ≃ (S → USym G), f ↦ (s ↦ f(ι_s)) (congp.tex:719-721). `}
def constructed_free_group_hom_equiv (S : Type) (dec : DecidableEquality S) (G : Group)
  : Equiv (GroupHom (constructed_free_group S dec) G) (S → USym G)
  ≔ compose_equiv (GroupHom (constructed_free_group S dec) G)
      (BookPointedMap (BG (constructed_free_group S dec)) (BG G)) (S → USym G)
      (group_hom_classifying_equiv (constructed_free_group S dec) G)
      (free_pointed_universal_property S (constructed_free_group_signature S dec) (BG G .carrier) (shape G))

def constructed_free_group_hom_equiv_evaluation (S : Type) (dec : DecidableEquality S) (G : Group)
  (f : GroupHom (constructed_free_group S dec) G) (s : S)
  : Id (USym G) (constructed_free_group_hom_equiv S dec G .map f s)
      (usym_hom (constructed_free_group S dec) G f (constructed_free_group_generator S dec s))
  ≔ refl (usym_hom (constructed_free_group S dec) G f (constructed_free_group_generator S dec s))

{` F_S is a decidable group: its symmetries have decidable equality. `}
def fsc_equiv_decidable_equality (A B : Type) (e : Equiv A B) (d : DecidableEquality B) (x y : A)
  : Decidable (Id A x y)
  ≔ match d (e .map x) (e .map y) [
  | inl. p ↦ inl. (equivalence_injective A B e x y p)
  | inr. n ↦ inr. (q ↦ n (refl (e .map) q)) ]

def constructed_free_group_decidable_equality (S : Type) (dec : DecidableEquality S)
  : DecidableEquality (USym (constructed_free_group S dec))
  ≔ fsc_equiv_decidable_equality (USym (constructed_free_group S dec)) (ReducedWord S)
      (constructed_free_group_usym_equiv S dec) (reduced_word_decidable_equality S dec)

{` F_{S+T} = F_S ∨ F_T for the constructed groups: B F_{S+T} is a wedge of
   B F_S and B F_T, pointed at i1(base) = base. `}
def constructed_free_sum_wedge (S T : Type) (dS : DecidableEquality S) (dT : DecidableEquality T)
  : WedgeSignature (BG (constructed_free_group S dS)) (BG (constructed_free_group T dT))
  ≔ free_sum_wedge_signature S T (Sum S T) (identity_equiv (Sum S T))
      (constructed_free_group_signature (Sum S T) (sum_decidable_equality S T dS dT))
      (constructed_free_group_signature S dS) (constructed_free_group_signature T dT)

def constructed_free_sum_wedge_path (S T : Type) (dS : DecidableEquality S) (dT : DecidableEquality T)
  : Id Pointed (BG (constructed_free_group (Sum S T) (sum_decidable_equality S T dS dT)))
      (wedge_pointed (BG (constructed_free_group S dS)) (BG (constructed_free_group T dT))
        (constructed_free_sum_wedge S T dS dT))
  ≔ (refl (BG (constructed_free_group (Sum S T) (sum_decidable_equality S T dS dT)) .carrier),
     inverse (BG (constructed_free_group (Sum S T) (sum_decidable_equality S T dS dT)) .carrier)
       (free_sum_incl1 S T (Sum S T) (identity_equiv (Sum S T))
         (constructed_free_group_signature (Sum S T) (sum_decidable_equality S T dS dT))
         (constructed_free_group_signature S dS) (shape (constructed_free_group S dS)))
       (shape (constructed_free_group (Sum S T) (sum_decidable_equality S T dS dT)))
       (free_sum_base1 S T (Sum S T) (identity_equiv (Sum S T))
         (constructed_free_group_signature (Sum S T) (sum_decidable_equality S T dS dT))
         (constructed_free_group_signature S dS)))
