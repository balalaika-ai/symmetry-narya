export "863-free-word-interpretation"

{` thm:free-group-elements (congp.tex:869), for every FreeGroupSignature
   S F with dec : DecidableEquality S: the restriction r |-> [r] of the
   interpretation to R_S (the image of rho_S) is an equivalence
   R_S = (base = base).

   The proof follows the book's encode-decode argument.  The family
   R_S(x) is defined by free_rec into Type with R_S(base) = R_S and
   R_S(loop_a) = ua(s_a).  Because the computation rule of the signature
   is only an identification, R_S(base) is identified with R_S by the
   enumeration of FreeWordMonodromy (transport of the standard datum
   along free_rec_beta, as for the circle in module 27); tau_x(p) is the
   transport of the enumerated eps.  [-]_x is defined by free_ind with
   [-]_base = [-] and the loop case is the book's square ([s_a w] =
   loop_a . [w], via [rho w] = [w]); [-]_x o tau_x = id holds by path
   induction.  For tau_base([w]) we prove the book's "tau([w]) ~ w for all
   words w" in the form tau([w]) = rho(w) by induction on w; at base this
   already gives the theorem, and the fiberwise statement for all x
   follows from free_ind_prop (connectedness). `}

def free_word_bouquet (S : Type) (dec : DecidableEquality S) : BouquetData S Type
  ≔ (ReducedWordImage S dec,
      a ↦ ua (ReducedWordImage S dec) (ReducedWordImage S dec) (image_letter_action_equiv S dec (inl. a)))

def free_word_family (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) : F .carrier → Type
  ≔ free_rec S F Type (free_word_bouquet S dec)

{` Data identifying the fiber over base with R_S, compatibly with the
   letter actions; not an assumption, constructed below. `}
def FreeWordMonodromy (S : Type) (dec : DecidableEquality S) (d : BouquetData S Type) : Type ≔ sig (
  enumeration : Equiv (ReducedWordImage S dec) (d .fst),
  step : (a : S) (r : ReducedWordImage S dec)
    → Id (d .fst) (d .snd a .trr (enumeration .map r)) (enumeration .map (image_letter_action S dec (inl. a) r)))

def standard_free_word_monodromy (S : Type) (dec : DecidableEquality S)
  : FreeWordMonodromy S dec (free_word_bouquet S dec)
  ≔ (identity_equiv (ReducedWordImage S dec), a r ↦ refl (image_letter_action S dec (inl. a) r))

def free_word_monodromy (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : FreeWordMonodromy S dec (free_bouquet S F Type (free_word_family S dec F))
  ≔ refl (FreeWordMonodromy S dec) (free_rec_beta S F Type (free_word_bouquet S dec)) .trl
      (standard_free_word_monodromy S dec)

def free_word_enumeration (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Equiv (ReducedWordImage S dec) (free_word_family S dec F (F .base))
  ≔ free_word_monodromy S dec F .enumeration

def free_word_step (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  (r : ReducedWordImage S dec)
  : Id (free_word_family S dec F (F .base))
      (transport (F .carrier) (free_word_family S dec F) (F .base) (F .base) (F .loop a)
        (free_word_enumeration S dec F .map r))
      (free_word_enumeration S dec F .map (image_letter_action S dec (inl. a) r))
  ≔ free_word_monodromy S dec F .step a r

def free_word_unenumerate (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (x : free_word_family S dec F (F .base)) : ReducedWordImage S dec
  ≔ equiv_inverse_map (ReducedWordImage S dec) (free_word_family S dec F (F .base)) (free_word_enumeration S dec F) x

{` The enumerated empty word, and tau_x(p) = trp_p(eps). `}
def free_word_root (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : free_word_family S dec F (F .base)
  ≔ free_word_enumeration S dec F .map (reduced_image_empty S dec)

def free_word_encode (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (z : F .carrier)
  (p : Id (F .carrier) (F .base) z) : free_word_family S dec F z
  ≔ transport (F .carrier) (free_word_family S dec F) (F .base) z p (free_word_root S dec F)

def free_word_decode_base (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (x : free_word_family S dec F (F .base)) : Id (F .carrier) (F .base) (F .base)
  ≔ free_word_interpretation S F (free_word_unenumerate S dec F x .fst)

{` Transport along loop_a acts by s_a on enumerated reduced words. `}
def free_word_step_index (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  (x0 x1 : free_word_family S dec F (F .base)) (q : Id (free_word_family S dec F) (F .loop a) x0 x1)
  : Id (ReducedWordImage S dec)
      (image_letter_action S dec (inl. a) (free_word_unenumerate S dec F x0)) (free_word_unenumerate S dec F x1)
  ≔ let e ≔ free_word_enumeration S dec F in
    let g ≔ free_word_unenumerate S dec F in
    equivalence_injective (ReducedWordImage S dec) (free_word_family S dec F (F .base)) e
      (image_letter_action S dec (inl. a) (g x0)) (g x1)
      (calc
        e .map (image_letter_action S dec (inl. a) (g x0))
        = transport (F .carrier) (free_word_family S dec F) (F .base) (F .base) (F .loop a) (e .map (g x0))
          by inverse (free_word_family S dec F (F .base))
            (transport (F .carrier) (free_word_family S dec F) (F .base) (F .base) (F .loop a) (e .map (g x0)))
            (e .map (image_letter_action S dec (inl. a) (g x0))) (free_word_step S dec F a (g x0))
        = transport (F .carrier) (free_word_family S dec F) (F .base) (F .base) (F .loop a) x0
          by refl (transport (F .carrier) (free_word_family S dec F) (F .base) (F .base) (F .loop a))
            (equiv_counit (ReducedWordImage S dec) (free_word_family S dec F (F .base)) e x0)
        = x1 by pathover_transport_equiv (F .carrier) (free_word_family S dec F) (F .base) (F .base) (F .loop a)
            x0 x1 .map q
        = e .map (g x1) by inverse (free_word_family S dec F (F .base)) (e .map (g x1)) x1
            (equiv_counit (ReducedWordImage S dec) (free_word_family S dec F (F .base)) e x1) ∎)

{` The book's square: [-] o s_a = (loop_a . -) o [-]. `}
def free_word_decode_triangle (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  (x0 x1 : free_word_family S dec F (F .base)) (q : Id (free_word_family S dec F) (F .loop a) x0 x1)
  : Id (Id (F .carrier) (F .base) (F .base))
      (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_decode_base S dec F x0) (F .loop a))
      (free_word_decode_base S dec F x1)
  ≔ concat (Id (F .carrier) (F .base) (F .base))
      (concat (F .carrier) (F .base) (F .base) (F .base) (free_word_decode_base S dec F x0) (F .loop a))
      (free_word_interpretation S F (word_reduction S dec (cons. (inl. a) (free_word_unenumerate S dec F x0 .fst))))
      (free_word_decode_base S dec F x1)
      (inverse (Id (F .carrier) (F .base) (F .base))
        (free_word_interpretation S F (word_reduction S dec (cons. (inl. a) (free_word_unenumerate S dec F x0 .fst))))
        (free_word_interpretation S F (cons. (inl. a) (free_word_unenumerate S dec F x0 .fst)))
        (free_word_interpretation_reduction S dec F (cons. (inl. a) (free_word_unenumerate S dec F x0 .fst))))
      (map_path (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base))
        (r ↦ free_word_interpretation S F (r .fst))
        (image_letter_action S dec (inl. a) (free_word_unenumerate S dec F x0)) (free_word_unenumerate S dec F x1)
        (free_word_step_index S dec F a x0 x1 q))

def free_word_decode_family (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (z : F .carrier)
  : Type
  ≔ free_word_family S dec F z → Id (F .carrier) (F .base) z

def free_word_decode_loop (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  : Id (free_word_decode_family S dec F) (F .loop a) (free_word_decode_base S dec F) (free_word_decode_base S dec F)
  ≔ x ⤇ pathover_from_triangle (F .carrier) (F .base) (F .base) (F .base) (F .loop a)
      (free_word_decode_base S dec F x.0) (free_word_decode_base S dec F x.1)
      (free_word_decode_triangle S dec F a x.0 x.1 x.2)

def free_word_decode_data (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : free_boundary S F (free_word_decode_family S dec F)
  ≔ (free_word_decode_base S dec F, a ↦ free_word_decode_loop S dec F a)

{` [-]_x : R_S(x) -> (base = x). `}
def free_word_decode (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : (z : F .carrier) → free_word_decode_family S dec F z
  ≔ free_ind S F (free_word_decode_family S dec F) (free_word_decode_data S dec F)

def free_word_decode_beta (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Id (free_word_decode_family S dec F (F .base)) (free_word_decode S dec F (F .base)) (free_word_decode_base S dec F)
  ≔ free_ind_base S F (free_word_decode_family S dec F) (free_word_decode_data S dec F)

def free_word_decode_root (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Id (Id (F .carrier) (F .base) (F .base)) (free_word_decode S dec F (F .base) (free_word_root S dec F))
      (refl (F .base))
  ≔ concat (Id (F .carrier) (F .base) (F .base))
      (free_word_decode S dec F (F .base) (free_word_root S dec F))
      (free_word_decode_base S dec F (free_word_root S dec F)) (refl (F .base))
      (free_word_decode_beta S dec F (refl (free_word_root S dec F)))
      (map_path (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base))
        (r ↦ free_word_interpretation S F (r .fst))
        (free_word_unenumerate S dec F (free_word_root S dec F)) (reduced_image_empty S dec)
        (equiv_retraction (ReducedWordImage S dec) (free_word_family S dec F (F .base))
          (free_word_enumeration S dec F) (reduced_image_empty S dec)))

{` [-]_x o tau_x = id, by path induction. `}
def free_word_decode_encode (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (z : F .carrier)
  (p : Id (F .carrier) (F .base) z)
  : Id (Id (F .carrier) (F .base) z) (free_word_decode S dec F z (free_word_encode S dec F z p)) p
  ≔ J (F .carrier) (F .base)
      (z p ↦ Id (Id (F .carrier) (F .base) z) (free_word_decode S dec F z (free_word_encode S dec F z p)) p)
      (concat (Id (F .carrier) (F .base) (F .base))
        (free_word_decode S dec F (F .base) (free_word_encode S dec F (F .base) (refl (F .base))))
        (free_word_decode S dec F (F .base) (free_word_root S dec F)) (refl (F .base))
        (refl (free_word_decode S dec F (F .base))
          (transport_refl (F .carrier) (free_word_family S dec F) (F .base) (free_word_root S dec F)))
        (free_word_decode_root S dec F)) z p

{` tau_base([w]) = rho(w) for every word w (the book: tau([w]) ~ w). `}
def fw_encode_inverse_letter (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  (v : SignedWord S)
  : Id (free_word_family S dec F (F .base))
      (transport (F .carrier) (free_word_family S dec F) (F .base) (F .base) (F .loop a)
        (free_word_enumeration S dec F .map (reduced_image_factor S dec (cons. (inr. a) v))))
      (free_word_enumeration S dec F .map (reduced_image_factor S dec v))
  ≔ let e ≔ free_word_enumeration S dec F in
    calc
      transport (F .carrier) (free_word_family S dec F) (F .base) (F .base) (F .loop a)
        (e .map (reduced_image_factor S dec (cons. (inr. a) v)))
      = e .map (image_letter_action S dec (inl. a) (reduced_image_factor S dec (cons. (inr. a) v)))
        by free_word_step S dec F a (reduced_image_factor S dec (cons. (inr. a) v))
      = e .map (reduced_image_factor S dec (cons. (inl. a) (cons. (inr. a) v)))
        by refl (e .map) (image_letter_action_factor S dec (inl. a) (cons. (inr. a) v))
      = e .map (reduced_image_factor S dec v)
        by refl (e .map) (reduced_image_factor_cancel_pair S dec (inl. a) v) ∎

def fw_encode_ih (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (v : SignedWord S) : Type
  ≔ Id (free_word_family S dec F (F .base))
      (free_word_encode S dec F (F .base) (free_word_interpretation S F v))
      (free_word_enumeration S dec F .map (reduced_image_factor S dec v))

def fw_encode_generator (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  (v : SignedWord S) (ih : fw_encode_ih S dec F v) : fw_encode_ih S dec F (cons. (inl. a) v)
  ≔ let R ≔ free_word_family S dec F in
    let X ≔ F .carrier in
    let b ≔ F .base in
    let e ≔ free_word_enumeration S dec F in
    let r ≔ free_word_root S dec F in
    calc
      transport X R b b (concat X b b b (free_word_interpretation S F v) (F .loop a)) r
      = transport X R b b (F .loop a) (transport X R b b (free_word_interpretation S F v) r)
        by transport_concat X R b b b (free_word_interpretation S F v) (F .loop a) r
      = transport X R b b (F .loop a) (e .map (reduced_image_factor S dec v))
        by refl (transport X R b b (F .loop a)) ih
      = e .map (image_letter_action S dec (inl. a) (reduced_image_factor S dec v))
        by free_word_step S dec F a (reduced_image_factor S dec v)
      = e .map (reduced_image_factor S dec (cons. (inl. a) v))
        by refl (e .map) (image_letter_action_factor S dec (inl. a) v) ∎

def fw_encode_inverse_generator (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  (v : SignedWord S) (ih : fw_encode_ih S dec F v) : fw_encode_ih S dec F (cons. (inr. a) v)
  ≔ let R ≔ free_word_family S dec F in
    let X ≔ F .carrier in
    let b ≔ F .base in
    let e ≔ free_word_enumeration S dec F in
    let r ≔ free_word_root S dec F in
    calc
      transport X R b b (concat X b b b (free_word_interpretation S F v) (inverse X b b (F .loop a))) r
      = transport X R b b (inverse X b b (F .loop a)) (transport X R b b (free_word_interpretation S F v) r)
        by transport_concat X R b b b (free_word_interpretation S F v) (inverse X b b (F .loop a)) r
      = transport X R b b (inverse X b b (F .loop a)) (e .map (reduced_image_factor S dec v))
        by refl (transport X R b b (inverse X b b (F .loop a))) ih
      = transport X R b b (inverse X b b (F .loop a))
          (transport X R b b (F .loop a) (e .map (reduced_image_factor S dec (cons. (inr. a) v))))
        by refl (transport X R b b (inverse X b b (F .loop a)))
          (inverse (R b) (transport X R b b (F .loop a) (e .map (reduced_image_factor S dec (cons. (inr. a) v))))
            (e .map (reduced_image_factor S dec v)) (fw_encode_inverse_letter S dec F a v))
      = e .map (reduced_image_factor S dec (cons. (inr. a) v))
        by transport_inverse_roundtrip X R b b (F .loop a) (e .map (reduced_image_factor S dec (cons. (inr. a) v))) ∎

def fw_encode_letter (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (x : SignedLetter S)
  (v : SignedWord S) (ih : fw_encode_ih S dec F v) : fw_encode_ih S dec F (cons. x v)
  ≔ match x [
  | inl. a ↦ fw_encode_generator S dec F a v ih
  | inr. a ↦ fw_encode_inverse_generator S dec F a v ih ]

def free_word_encode_interpretation (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (w : SignedWord S)
  : Id (free_word_family S dec F (F .base))
      (free_word_encode S dec F (F .base) (free_word_interpretation S F w))
      (free_word_enumeration S dec F .map (reduced_image_factor S dec w))
  ≔ match w [
  | nil. ↦ transport_refl (F .carrier) (free_word_family S dec F) (F .base) (free_word_root S dec F)
  | cons. x v ↦ fw_encode_letter S dec F x v (free_word_encode_interpretation S dec F v) ]

{` thm:free-group-elements. `}
def free_group_elements_inverse (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (p : Id (F .carrier) (F .base) (F .base)) : ReducedWordImage S dec
  ≔ free_word_unenumerate S dec F (free_word_encode S dec F (F .base) p)

def free_group_elements_retraction (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (r : ReducedWordImage S dec)
  : Id (ReducedWordImage S dec) (free_group_elements_inverse S dec F (free_reduced_interpretation S dec F r)) r
  ≔ let e ≔ free_word_enumeration S dec F in
    calc
      free_word_unenumerate S dec F (free_word_encode S dec F (F .base) (free_word_interpretation S F (r .fst)))
      = free_word_unenumerate S dec F (e .map (reduced_image_factor S dec (r .fst)))
        by refl (free_word_unenumerate S dec F) (free_word_encode_interpretation S dec F (r .fst))
      = reduced_image_factor S dec (r .fst)
        by equiv_retraction (ReducedWordImage S dec) (free_word_family S dec F (F .base)) e
          (reduced_image_factor S dec (r .fst))
      = r by reduced_image_factor_self S dec r ∎

def free_group_elements_section (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (p : Id (F .carrier) (F .base) (F .base))
  : Id (Id (F .carrier) (F .base) (F .base)) (free_reduced_interpretation S dec F (free_group_elements_inverse S dec F p)) p
  ≔ concat (Id (F .carrier) (F .base) (F .base))
      (free_word_decode_base S dec F (free_word_encode S dec F (F .base) p))
      (free_word_decode S dec F (F .base) (free_word_encode S dec F (F .base) p)) p
      (inverse (Id (F .carrier) (F .base) (F .base))
        (free_word_decode S dec F (F .base) (free_word_encode S dec F (F .base) p))
        (free_word_decode_base S dec F (free_word_encode S dec F (F .base) p))
        (free_word_decode_beta S dec F (refl (free_word_encode S dec F (F .base) p))))
      (free_word_decode_encode S dec F (F .base) p)

def free_group_elements_equiv (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Equiv (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base))
  ≔ quasi_inverse_equiv (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base))
      (free_reduced_interpretation S dec F) (free_group_elements_inverse S dec F)
      (free_group_elements_retraction S dec F) (free_group_elements_section S dec F)

{` The same in the book's equivalence convention, and with the hypothesis
   "S is a decidable set" in the form of module 161. `}
def free_group_elements_book_equiv (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : BookEquiv (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base))
  ≔ book_equivalence (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base)) (free_group_elements_equiv S dec F)

def free_group_elements_decidable_set (S : Type) (hS : DecidableSet S) (F : FreeGroupSignature S)
  : Equiv (ReducedWordImage S (decidable_set_equality S hS)) (Id (F .carrier) (F .base) (F .base))
  ≔ free_group_elements_equiv S (decidable_set_equality S hS) F

{` The same for the subtype of reduced words; the map is r |-> [r]. `}
def free_group_reduced_words_equiv (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Equiv (ReducedWord S) (Id (F .carrier) (F .base) (F .base))
  ≔ compose_equiv (ReducedWord S) (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base))
      (canonical_inverse_equiv (ReducedWordImage S dec) (ReducedWord S) (reduced_word_image_equiv S dec))
      (free_group_elements_equiv S dec F)

def free_group_reduced_words_equiv_map (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Id (ReducedWord S → Id (F .carrier) (F .base) (F .base)) (free_group_reduced_words_equiv S dec F .map)
      (r ↦ free_word_interpretation S F (r .fst))
  ≔ refl (free_group_reduced_words_equiv S dec F .map)

{` The fiberwise statement of the proof: tau_x and [-]_x are inverse
   equivalences (base = x) = R_S(x) for every x : B F_S. `}
def free_word_family_set (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : (z : F .carrier) → isSet (free_word_family S dec F z)
  ≔ free_ind_prop S F (z ↦ isSet (free_word_family S dec F z)) (z ↦ isset_isprop (free_word_family S dec F z))
      (hlevel_two_to_set (free_word_family S dec F (F .base))
        (hlevel_equiv (suc. (suc. zero.)) (ReducedWordImage S dec) (free_word_family S dec F (F .base))
          (free_word_enumeration S dec F) (set_to_hlevel_two (ReducedWordImage S dec) (reduced_image_set S dec))))

def free_word_encode_decode_base (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (x : free_word_family S dec F (F .base))
  : Id (free_word_family S dec F (F .base)) (free_word_encode S dec F (F .base) (free_word_decode S dec F (F .base) x)) x
  ≔ let e ≔ free_word_enumeration S dec F in
    calc
      free_word_encode S dec F (F .base) (free_word_decode S dec F (F .base) x)
      = free_word_encode S dec F (F .base) (free_word_decode_base S dec F x)
        by refl (free_word_encode S dec F (F .base)) (free_word_decode_beta S dec F (refl x))
      = e .map (reduced_image_factor S dec (free_word_unenumerate S dec F x .fst))
        by free_word_encode_interpretation S dec F (free_word_unenumerate S dec F x .fst)
      = e .map (free_word_unenumerate S dec F x)
        by refl (e .map) (reduced_image_factor_self S dec (free_word_unenumerate S dec F x))
      = x by equiv_counit (ReducedWordImage S dec) (free_word_family S dec F (F .base)) e x ∎

def free_word_encode_decode (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : (z : F .carrier) (x : free_word_family S dec F z)
    → Id (free_word_family S dec F z) (free_word_encode S dec F z (free_word_decode S dec F z x)) x
  ≔ free_ind_prop S F
      (z ↦ (x : free_word_family S dec F z)
        → Id (free_word_family S dec F z) (free_word_encode S dec F z (free_word_decode S dec F z x)) x)
      (z ↦ pi_prop (free_word_family S dec F z)
        (x ↦ Id (free_word_family S dec F z) (free_word_encode S dec F z (free_word_decode S dec F z x)) x)
        (x ↦ free_word_family_set S dec F z (free_word_encode S dec F z (free_word_decode S dec F z x)) x))
      (free_word_encode_decode_base S dec F)

def free_word_path_code_equiv (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (z : F .carrier)
  : Equiv (Id (F .carrier) (F .base) z) (free_word_family S dec F z)
  ≔ quasi_inverse_equiv (Id (F .carrier) (F .base) z) (free_word_family S dec F z)
      (free_word_encode S dec F z) (free_word_decode S dec F z)
      (free_word_decode_encode S dec F z) (free_word_encode_decode S dec F z)
