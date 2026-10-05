export "876-reduced-words-free"

{` The free group on a decidable set S, constructed without HITs or axioms
   (instance of def:bfree's FreeGroupSignature, module 860): the component
   of the S-set (R_S, s) of reduced words in the type of types with
   S-indexed endomaps, based at (R_S, s), with loop_a the S-automorphism of
   R_S sending ε to s_a(ε) = a.

   Orientation: evaluation ev(t) = transport of ε along t (an equivalence
   USym F_S ≃ R_S, constructed_free_group_usym_equiv) satisfies
   ev(concat loop_a t) = s_a(ev t), i.e. ev(t · loop_a) = ρ(a · ev(t)) in
   the book's notation g · h = concat h g. `}

def constructed_free_group_signature (S : Type) (dec : DecidableEquality S) : FreeGroupSignature S
  ≔ free_group_signature_from_free_sset S (reduced_word_free_sset S dec)

def constructed_free_group_signature_decidable_set (S : Type) (h : DecidableSet S) : FreeGroupSignature S
  ≔ constructed_free_group_signature S (x y ↦ h x y .snd)

def constructed_free_group (S : Type) (dec : DecidableEquality S) : Group
  ≔ free_sset_group S (reduced_word_free_sset S dec) (reduced_word_set S dec)

def constructed_free_group_classifying (S : Type) (dec : DecidableEquality S)
  : Id Pointed (BG (constructed_free_group S dec)) (free_pointed S (constructed_free_group_signature S dec))
  ≔ refl (free_pointed S (constructed_free_group_signature S dec))

def constructed_free_group_generator (S : Type) (dec : DecidableEquality S) (a : S)
  : USym (constructed_free_group S dec)
  ≔ constructed_free_group_signature S dec .loop a

{` Loops of the base are the reduced words. `}
def constructed_free_group_usym_equiv (S : Type) (dec : DecidableEquality S)
  : Equiv (USym (constructed_free_group S dec)) (ReducedWord S)
  ≔ fsc_loops_equiv S (reduced_word_free_sset S dec)

def constructed_free_group_generator_word (S : Type) (dec : DecidableEquality S) (a : S)
  : Id (ReducedWord S) (constructed_free_group_usym_equiv S dec .map (constructed_free_group_generator S dec a))
      (cons. (inl. a) nil., (star., star.))
  ≔ fsc_loop_eval_letter S (reduced_word_free_sset S dec) a

def constructed_free_group_left_mul (S : Type) (dec : DecidableEquality S) (a : S)
  (t : USym (constructed_free_group S dec))
  : Id (ReducedWord S)
      (constructed_free_group_usym_equiv S dec .map
        (usym_mul (constructed_free_group S dec) t (constructed_free_group_generator S dec a)))
      (reduced_letter_action S dec (inl. a) (constructed_free_group_usym_equiv S dec .map t))
  ≔ fsc_loop_left S (reduced_word_free_sset S dec) a t

{` Litmus 1: the free group on Bool is not abelian. `}
def free_bool_group : Group ≔ constructed_free_group Bool fw_bool_decidable_equality

def free_bool_two_letters (a b : Bool)
  : Id (ReducedWord Bool)
      (constructed_free_group_usym_equiv Bool fw_bool_decidable_equality .map
        (usym_mul free_bool_group (constructed_free_group_generator Bool fw_bool_decidable_equality b)
          (constructed_free_group_generator Bool fw_bool_decidable_equality a)))
      (reduced_letter_action Bool fw_bool_decidable_equality (inl. a)
        (reduced_letter_action Bool fw_bool_decidable_equality (inl. b) (reduced_word_empty Bool)))
  ≔ let dec ≔ fw_bool_decidable_equality in
    let ev ≔ constructed_free_group_usym_equiv Bool dec .map in
    let g ≔ constructed_free_group_generator Bool dec in
    concat (ReducedWord Bool) (ev (usym_mul free_bool_group (g b) (g a)))
      (reduced_letter_action Bool dec (inl. a) (ev (g b)))
      (reduced_letter_action Bool dec (inl. a) (reduced_letter_action Bool dec (inl. b) (reduced_word_empty Bool)))
      (constructed_free_group_left_mul Bool dec a (g b))
      (refl (reduced_letter_action Bool dec (inl. a)) (constructed_free_group_generator_word Bool dec b))

{` The two products of the generators evaluate to the words "true false"
   and "false true" (computed by refl). `}
def free_bool_word_true_false
  : Id (SignedWord Bool)
      (reduced_letter_action Bool fw_bool_decidable_equality (inl. true.)
        (reduced_letter_action Bool fw_bool_decidable_equality (inl. false.) (reduced_word_empty Bool)) .fst)
      (cons. (inl. true.) (cons. (inl. false.) nil.))
  ≔ refl (cons. (inl. true.) (cons. (inl. false.) nil.) : SignedWord Bool)

def free_bool_generators_noncommuting
  : Id (USym free_bool_group)
      (usym_mul free_bool_group (constructed_free_group_generator Bool fw_bool_decidable_equality true.)
        (constructed_free_group_generator Bool fw_bool_decidable_equality false.))
      (usym_mul free_bool_group (constructed_free_group_generator Bool fw_bool_decidable_equality false.)
        (constructed_free_group_generator Bool fw_bool_decidable_equality true.))
    → Empty
  ≔ p ↦
    let dec ≔ fw_bool_decidable_equality in
    let ev ≔ constructed_free_group_usym_equiv Bool dec .map in
    let g ≔ constructed_free_group_generator Bool dec in
    let w ≔ concat (ReducedWord Bool)
      (reduced_letter_action Bool dec (inl. false.) (reduced_letter_action Bool dec (inl. true.) (reduced_word_empty Bool)))
      (ev (usym_mul free_bool_group (g true.) (g false.)))
      (reduced_letter_action Bool dec (inl. true.) (reduced_letter_action Bool dec (inl. false.) (reduced_word_empty Bool)))
      (inverse (ReducedWord Bool) (ev (usym_mul free_bool_group (g true.) (g false.)))
        (reduced_letter_action Bool dec (inl. false.) (reduced_letter_action Bool dec (inl. true.) (reduced_word_empty Bool)))
        (free_bool_two_letters false. true.))
      (concat (ReducedWord Bool) (ev (usym_mul free_bool_group (g true.) (g false.)))
        (ev (usym_mul free_bool_group (g false.) (g true.)))
        (reduced_letter_action Bool dec (inl. true.) (reduced_letter_action Bool dec (inl. false.) (reduced_word_empty Bool)))
        (refl ev p) (free_bool_two_letters true. false.)) in
    bool_encode false. true.
      (sum_encode Bool Bool (inl. false.) (inl. true.)
        (list_encode (SignedLetter Bool) (cons. (inl. false.) (cons. (inl. true.) nil.))
          (cons. (inl. true.) (cons. (inl. false.) nil.)) (w .fst) .fst))

def free_bool_group_not_abelian : IsAbelian free_bool_group → Empty
  ≔ h ↦ free_bool_generators_noncommuting
      (h (constructed_free_group_generator Bool fw_bool_decidable_equality true.)
        (constructed_free_group_generator Bool fw_bool_decidable_equality false.))

{` Litmus 2: a free group signature on 1 is a circle; the constructed free
   group on 1 has USym ≃ Int (n ↦ loop^n). `}
def free_unit_loop_family (F : FreeGroupSignature Unit) (P : F .carrier → Type)
  (d : CircleBoundary (F .carrier) (F .base) (F .loop star.) P) (s : Unit)
  : Id P (F .loop s) (d .fst) (d .fst)
  ≔ match s [ star. ↦ d .snd ]

def free_unit_circle_boundary (F : FreeGroupSignature Unit) (P : F .carrier → Type)
  (u : FreeGroupBoundary Unit (F .carrier) (F .base) (F .loop) P)
  : CircleBoundary (F .carrier) (F .base) (F .loop star.) P
  ≔ (u .fst, u .snd star.)

def free_group_unit_circle (F : FreeGroupSignature Unit) : CircleSignature
  ≔ (F .carrier, F .base, F .loop star.,
     P d ↦ (F .induction P (d .fst, free_unit_loop_family F P d) .fst,
       refl (free_unit_circle_boundary F P) (F .induction P (d .fst, free_unit_loop_family F P d) .snd)))

def constructed_free_group_unit_integers
  : BookEquiv Int (USym (constructed_free_group Unit unit_decidable_equality))
  ≔ circle_group_usym_integers (free_group_unit_circle (constructed_free_group_signature Unit unit_decidable_equality))

{` Conversely every circle is a free group signature on 1. `}
def circle_free_unit_boundary (C : CircleSignature) (P : C .carrier → Type)
  (d : FreeGroupBoundary Unit (C .carrier) (C .base) (_ ↦ C .loop) P)
  : CircleBoundary (C .carrier) (C .base) (C .loop) P
  ≔ (d .fst, d .snd star.)

def circle_free_unit_lift (C : CircleSignature) (P : C .carrier → Type)
  (u : CircleBoundary (C .carrier) (C .base) (C .loop) P)
  : FreeGroupBoundary Unit (C .carrier) (C .base) (_ ↦ C .loop) P
  ≔ (u .fst, _ ↦ u .snd)

def circle_free_unit_lift_eta (C : CircleSignature) (P : C .carrier → Type)
  (d : FreeGroupBoundary Unit (C .carrier) (C .base) (_ ↦ C .loop) P)
  : Id (FreeGroupBoundary Unit (C .carrier) (C .base) (_ ↦ C .loop) P)
      (circle_free_unit_lift C P (circle_free_unit_boundary C P d)) d
  ≔ (refl (d .fst), funext Unit (_ ↦ Id P (C .loop) (d .fst) (d .fst)) (_ ↦ d .snd star.) (d .snd)
      (s ↦ match s [ star. ↦ refl (d .snd star.) ]))

def circle_free_signature (C : CircleSignature) : FreeGroupSignature Unit
  ≔ (C .carrier, C .base, _ ↦ C .loop,
     P d ↦ (C .induction P (circle_free_unit_boundary C P d) .fst,
       concat (FreeGroupBoundary Unit (C .carrier) (C .base) (_ ↦ C .loop) P)
         (free_group_evaluate Unit (C .carrier) (C .base) (_ ↦ C .loop) P (C .induction P (circle_free_unit_boundary C P d) .fst))
         (circle_free_unit_lift C P (circle_free_unit_boundary C P d)) d
         (refl (circle_free_unit_lift C P) (C .induction P (circle_free_unit_boundary C P d) .snd))
         (circle_free_unit_lift_eta C P d)))

def circle_free_signature_pointed (C : CircleSignature)
  : Id Pointed (free_pointed Unit (circle_free_signature C)) (circle_pointed C)
  ≔ refl (circle_pointed C)
