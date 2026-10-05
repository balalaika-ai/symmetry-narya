export "864-free-group-elements"

{` Consequences of thm:free-group-elements (congp.tex:738-780, 869): for a
   decidable set S (dec : DecidableEquality S) and every FreeGroupSignature
   S F, B F_S is a groupoid ("we need to know that B F_S is a groupoid"),
   so def:bfree's F_S = mkgroup(B F_S, base) is a group; USym F_S = R_S,
   USym F_S has decidable equality, Hom(F_S, G) = (S -> USym G) by
   evaluation at the generators, and F_S is a free group on S in the sense
   of the inline definition at congp.tex:716.  Litmus: the generators are
   nontrivial and F_Bool is not abelian. `}

def free_base_loops_set (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : isSet (Id (F .carrier) (F .base) (F .base))
  ≔ hlevel_two_to_set (Id (F .carrier) (F .base) (F .base))
      (hlevel_equiv (suc. (suc. zero.)) (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base))
        (free_group_elements_equiv S dec F) (set_to_hlevel_two (ReducedWordImage S dec) (reduced_image_set S dec)))

def free_based_paths_set (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : (z : F .carrier) → isSet (Id (F .carrier) (F .base) z)
  ≔ free_ind_prop S F (z ↦ isSet (Id (F .carrier) (F .base) z)) (z ↦ isset_isprop (Id (F .carrier) (F .base) z))
      (free_base_loops_set S dec F)

{` B F_S is a groupoid (congp.tex:767-772, for decidable S). `}
def free_signature_groupoid (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : isGroupoid (F .carrier)
  ≔ free_ind_prop S F (x ↦ (y : F .carrier) → isSet (Id (F .carrier) x y))
      (x ↦ pi_prop (F .carrier) (y ↦ isSet (Id (F .carrier) x y)) (y ↦ isset_isprop (Id (F .carrier) x y)))
      (free_based_paths_set S dec F)

def free_group_pcg (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) : PointedConnectedGroupoid
  ≔ (F .carrier, F .base, free_connected S F, free_signature_groupoid S dec F)

{` def:bfree, last sentence: F_S = mkgroup(B F_S, base). `}
def free_group (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) : Group
  ≔ mkgroup (free_group_pcg S dec F)

def free_group_decidable_set (S : Type) (hS : DecidableSet S) (F : FreeGroupSignature S) : Group
  ≔ free_group S (decidable_set_equality S hS) F

def free_group_classifying (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Id Pointed (BG (free_group S dec F)) (free_pointed S F)
  ≔ refl (free_pointed S F)

{` The generators iota_s = loop_s. `}
def free_group_generator (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (s : S)
  : USym (free_group S dec F)
  ≔ F .loop s

{` Words as elements of F_S, in the group operations of module 400:
   [a w] = iota_a . [w] and [A w] = iota_a^-1 . [w] (judgmental). `}
def free_group_word (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (w : SignedWord S)
  : USym (free_group S dec F)
  ≔ free_word_interpretation S F w

def free_group_word_generator (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  (w : SignedWord S)
  : Id (USym (free_group S dec F)) (free_group_word S dec F (cons. (inl. a) w))
      (usym_mul (free_group S dec F) (free_group_generator S dec F a) (free_group_word S dec F w))
  ≔ refl (free_group_word S dec F (cons. (inl. a) w))

def free_group_word_inverse_generator (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (a : S)
  (w : SignedWord S)
  : Id (USym (free_group S dec F)) (free_group_word S dec F (cons. (inr. a) w))
      (usym_mul (free_group S dec F) (usym_inv (free_group S dec F) (free_group_generator S dec F a))
        (free_group_word S dec F w))
  ≔ refl (free_group_word S dec F (cons. (inr. a) w))

{` thm:free-group-elements in group notation: R_S = USym F_S. `}
def free_group_usym_equiv (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Equiv (ReducedWordImage S dec) (USym (free_group S dec F))
  ≔ free_group_elements_equiv S dec F

def free_group_usym_reduced_words (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : Equiv (ReducedWord S) (USym (free_group S dec F))
  ≔ free_group_reduced_words_equiv S dec F

{` USym F_S has decidable equality. `}
def fw_transfer_decide (A B : Type) (e : Equiv A B) (x y : B)
  (c : Decidable (Id A (equiv_inverse_map A B e x) (equiv_inverse_map A B e y))) : Decidable (Id B x y)
  ≔ match c [
  | inl. p ↦ inl. (concat B x (e .map (equiv_inverse_map A B e x)) y
      (inverse B (e .map (equiv_inverse_map A B e x)) x (equiv_counit A B e x))
      (concat B (e .map (equiv_inverse_map A B e x)) (e .map (equiv_inverse_map A B e y)) y
        (refl (e .map) p) (equiv_counit A B e y)))
  | inr. n ↦ inr. (q ↦ n (refl (equiv_inverse_map A B e) q)) ]

def fw_transfer_decidable_equality (A B : Type) (e : Equiv A B) (d : DecidableEquality A) : DecidableEquality B
  ≔ x y ↦ fw_transfer_decide A B e x y (d (equiv_inverse_map A B e x) (equiv_inverse_map A B e y))

def free_group_usym_decidable_equality (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : DecidableEquality (USym (free_group S dec F))
  ≔ fw_transfer_decidable_equality (ReducedWordImage S dec) (USym (free_group S dec F))
      (free_group_usym_equiv S dec F) (reduced_image_decidable_equality S dec)

{` "evaluation gives an equivalence Hom(F_S, G) = (S -> USym G)": the
   group version of 860's free_pointed_universal_property. `}
def free_group_hom_equiv (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (G : Group)
  : Equiv (GroupHom (free_group S dec F) G) (S → USym G)
  ≔ compose_equiv (GroupHom (free_group S dec F) G) (BookPointedMap (BG (free_group S dec F)) (BG G)) (S → USym G)
      (group_hom_classifying_equiv (free_group S dec F) G)
      (free_pointed_universal_property S F (BG G .carrier) (shape G))

def free_group_hom_equiv_map (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (G : Group)
  (f : GroupHom (free_group S dec F) G)
  : Id (S → USym G) (free_group_hom_equiv S dec F G .map f)
      (s ↦ usym_hom (free_group S dec F) G f (free_group_generator S dec F s))
  ≔ refl (free_group_hom_equiv S dec F G .map f)

{` congp.tex:716 (inline definition): a free group on S is a group with
   elements iota_s : USym such that evaluation Hom(F, G) -> (S -> USym G),
   f |-> (s |-> USym f (iota_s)), is an equivalence for every group G. `}
def IsFreeGroupOn (S : Type) (Phi : Group) (iota : S → USym Phi) : Type
  ≔ (G : Group) → isEquiv (GroupHom Phi G) (S → USym G) (f ↦ s ↦ usym_hom Phi G f (iota s))

def free_group_is_free (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  : IsFreeGroupOn S (free_group S dec F) (free_group_generator S dec F)
  ≔ G ↦ free_group_hom_equiv S dec F G .equiv

{` Litmus: every generator is nontrivial. `}
def fw_singleton_not_empty (S : Type) (s : S)
  (p : Id (SignedWord S) (cons. (inl. s) nil.) nil.) : Empty
  ≔ list_encode (SignedLetter S) (cons. (inl. s) nil.) nil. p

def free_group_generator_nontrivial (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (s : S)
  : Not (Id (USym (free_group S dec F)) (free_group_generator S dec F s) (usym_unit (free_group S dec F)))
  ≔ q ↦ fw_singleton_not_empty S s
      (map_path (ReducedWordImage S dec) (SignedWord S) (r ↦ r .fst)
        (reduced_image_factor S dec (cons. (inl. s) nil.)) (reduced_image_empty S dec)
        (equivalence_injective (ReducedWordImage S dec) (Id (F .carrier) (F .base) (F .base))
          (free_group_elements_equiv S dec F)
          (reduced_image_factor S dec (cons. (inl. s) nil.)) (reduced_image_empty S dec)
          (concat (Id (F .carrier) (F .base) (F .base))
            (concat (F .carrier) (F .base) (F .base) (F .base) (refl (F .base)) (F .loop s))
            (F .loop s) (refl (F .base))
            (concat_1p (F .carrier) (F .base) (F .base) (F .loop s)) q)))

{` Litmus: F_Bool is not abelian (iota_a . iota_b differs from
   iota_b . iota_a, since ab and ba are distinct reduced words). `}
def fw_ab_ba_distinct
  (p : Id (SignedWord Bool) (cons. fw_letter_a (cons. fw_letter_b nil.)) (cons. fw_letter_b (cons. fw_letter_a nil.)))
  : Empty
  ≔ bool_encode false. true.
      (sum_encode Bool Bool (inl. false.) (inl. true.)
        (list_encode (SignedLetter Bool) (cons. fw_letter_a (cons. fw_letter_b nil.))
          (cons. fw_letter_b (cons. fw_letter_a nil.)) p .fst))

def free_group_bool_not_abelian (F : FreeGroupSignature Bool)
  : Not (IsAbelian (free_group Bool fw_bool_decidable_equality F))
  ≔ h ↦
    let X ≔ F .carrier in
    let b ≔ F .base in
    let la ≔ F .loop false. in
    let lb ≔ F .loop true. in
    fw_ab_ba_distinct
      (map_path (ReducedWordImage Bool fw_bool_decidable_equality) (SignedWord Bool) (r ↦ r .fst)
        (reduced_image_factor Bool fw_bool_decidable_equality (cons. fw_letter_a (cons. fw_letter_b nil.)))
        (reduced_image_factor Bool fw_bool_decidable_equality (cons. fw_letter_b (cons. fw_letter_a nil.)))
        (equivalence_injective (ReducedWordImage Bool fw_bool_decidable_equality) (Id X b b)
          (free_group_elements_equiv Bool fw_bool_decidable_equality F)
          (reduced_image_factor Bool fw_bool_decidable_equality (cons. fw_letter_a (cons. fw_letter_b nil.)))
          (reduced_image_factor Bool fw_bool_decidable_equality (cons. fw_letter_b (cons. fw_letter_a nil.)))
          (calc
            concat X b b b (concat X b b b (refl b) lb) la
            = concat X b b b lb la
              by refl ((q ↦ concat X b b b q la) : Id X b b → Id X b b) (concat_1p X b b lb)
            = concat X b b b la lb by h la lb
            = concat X b b b (concat X b b b (refl b) la) lb
              by refl ((q ↦ concat X b b b q lb) : Id X b b → Id X b b)
                (inverse (Id X b b) (concat X b b b (refl b) la) la (concat_1p X b b la)) ∎)))
