export "865-free-group"
export "881-constructed-free-group-properties"

{` Bridge between the two chapter-8 free groups: the constructed free group
   (module 877, no HITs) and def:bfree's F_S for an arbitrary signature
   (module 865), instantiated at the constructed signature.  Their
   classifying pointed types coincide judgmentally; only the proofs of
   connectedness and groupoidness differ.  thm:free-group-elements
   (module 864) applies to the constructed signature, giving the book's
   interpretation ⟦-⟧ : R_S ≃ USym F_S for the constructed free group. `}

def constructed_free_group_path (S : Type) (dec : DecidableEquality S)
  : Id Group (constructed_free_group S dec) (free_group S dec (constructed_free_group_signature S dec))
  ≔ group_path_from_pointed_equiv (constructed_free_group S dec) (free_group S dec (constructed_free_group_signature S dec))
      ((x ↦ x, refl (constructed_free_group_signature S dec .base)),
       identity_book_equiv (constructed_free_group_signature S dec .carrier) .equiv)

def constructed_free_group_usym_check (S : Type) (dec : DecidableEquality S)
  : Id Type (USym (constructed_free_group S dec)) (USym (free_group S dec (constructed_free_group_signature S dec)))
  ≔ refl (USym (constructed_free_group S dec))

{` thm:free-group-elements for the constructed free group: the book's
   interpretation r ↦ ⟦r⟧ is an equivalence R_S ≃ USym F_S. `}
def constructed_free_group_interpretation_equiv (S : Type) (dec : DecidableEquality S)
  : Equiv (ReducedWord S) (USym (constructed_free_group S dec))
  ≔ free_group_reduced_words_equiv S dec (constructed_free_group_signature S dec)

def constructed_free_group_interpretation_map (S : Type) (dec : DecidableEquality S) (r : ReducedWord S)
  : Id (USym (constructed_free_group S dec)) (constructed_free_group_interpretation_equiv S dec .map r)
      (free_word_interpretation S (constructed_free_group_signature S dec) (r .fst))
  ≔ refl (free_word_interpretation S (constructed_free_group_signature S dec) (r .fst))

{` Litmus: ⟦a b⟧ = ι_a · ι_b in the constructed free group on Bool. `}
def constructed_free_bool_word_check
  : Id (USym (constructed_free_group Bool fw_bool_decidable_equality))
      (free_word_interpretation Bool (constructed_free_group_signature Bool fw_bool_decidable_equality)
        (cons. fw_letter_a (cons. fw_letter_b nil.)))
      (usym_mul (constructed_free_group Bool fw_bool_decidable_equality)
        (constructed_free_group_generator Bool fw_bool_decidable_equality false.)
        (usym_mul (constructed_free_group Bool fw_bool_decidable_equality)
          (constructed_free_group_generator Bool fw_bool_decidable_equality true.)
          (usym_unit (constructed_free_group Bool fw_bool_decidable_equality))))
  ≔ refl (free_word_interpretation Bool (constructed_free_group_signature Bool fw_bool_decidable_equality)
        (cons. fw_letter_a (cons. fw_letter_b nil.)))
