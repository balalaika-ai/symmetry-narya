export "05-free"
export "../../../src/866-free-group-examples"

{` Bridges for congp.tex, section "Free groups" (blind file 05-free):
   def:bfree, the signed letters (782), reduced words and deletions (811),
   the xca on ρ_S (819), R_S and D_S (824), the remark 842, the
   interpretation ⟦−⟧ (857), thm:free-group-elements (869) and the xca on R_1
   (929). The wedge xca (937) is in bridge-05b-free.

   A blind signature on a set S is fieldwise one of ours on S .fst (the
   boundary and evaluation are the same Σ-terms). The blind ρ_S uses the
   decidable equality of a DecidableSet and its own complementation; it agrees
   with our word_reduction at decidable_set_equality pointwise (b05_rho_eq, by
   induction on words), so the two images R_S are equivalent by a map that is
   the identity on the underlying word (b05_image_equiv). The blind ⟦−⟧
   agrees with ours by induction on words. `}

{` def:bfree. `}
def b05_sig (S : SetTypes) (F : BlindFreeGroupSignature S) : FreeGroupSignature (S .fst)
  ≔ (F .carrier, F .base, F .loop, F .induction)

def b05_sig_back (S : SetTypes) (F : FreeGroupSignature (S .fst)) : BlindFreeGroupSignature S
  ≔ (F .carrier, F .base, F .loop, F .induction)

def bridge_def_free_signature (S : SetTypes) : Equiv (BlindFreeGroupSignature S) (FreeGroupSignature (S .fst))
  ≔ quasi_inverse_equiv (BlindFreeGroupSignature S) (FreeGroupSignature (S .fst)) (b05_sig S) (b05_sig_back S)
      (F ↦ refl F) (F ↦ refl F)

def bridge_def_free_pointed (S : SetTypes) (F : BlindFreeGroupSignature S)
  : Id Pointed (blind_free_pointed S F) (free_pointed (S .fst) (b05_sig S F))
  ≔ refl (blind_free_pointed S F)

def bridge_def_free_infty_group (S : SetTypes) (F : BlindFreeGroupSignature S)
  : Id InftyGroup (blind_free_infty_group S F) (free_infty_group (S .fst) (b05_sig S F))
  ≔ (classifying ≔
      (refl (F .carrier), refl (F .base),
       connected_prop (F .carrier) (blind_free_connected S F) (free_connected (S .fst) (b05_sig S F))))

def bridge_def_free_group (S : SetTypes) (dec : DecidableEquality (S .fst)) (F : BlindFreeGroupSignature S)
  (hF : isGroupoid (F .carrier))
  : Id Group (blind_free_group S F hF) (free_group (S .fst) dec (b05_sig S F))
  ≔ (classifying ≔
      (refl (F .carrier), refl (F .base),
       connected_prop (F .carrier) (blind_free_connected S F) (free_connected (S .fst) (b05_sig S F)),
       isgroupoid_isprop (F .carrier) hF (free_signature_groupoid (S .fst) dec (b05_sig S F))))

{` congp.tex:782. `}
def b05_comp_eq (S : Type) (x : Sum S S) : Id (Sum S S) (blind_complement S x) (letter_complement S x)
  ≔ match x [ inl. a ↦ refl (inr. a : Sum S S) | inr. a ↦ refl (inl. a : Sum S S) ]

def bridge_def_complement (S : Type) : Id (Sum S S → Sum S S) (letter_complement S) (blind_complement S)
  ≔ funext (Sum S S) (_ ↦ Sum S S) (letter_complement S) (blind_complement S)
      (x ↦ inverse (Sum S S) (blind_complement S x) (letter_complement S x) (b05_comp_eq S x))

def bridge_signed_claims : blind_signed_claims
  ≔ S dS ↦
    (signed_letter_decidable_set S (decidable_set_equality S dS),
     transport (Sum S S → Sum S S)
       (c ↦ Product ((x : Sum S S) → Id (Sum S S) (c (c x)) x) (BookIsEquiv (Sum S S) (Sum S S) c))
       (letter_complement S) (blind_complement S) (bridge_def_complement S)
       (letter_complement_involutive S,
        book_equivalence (Sum S S) (Sum S S) (letter_complement_equiv S) .equiv))

{` congp.tex:811: reducedness, one deletion step, n deletion steps. `}
def b05_red_from_of (S : Type) (x : Sum S S) (v : List (Sum S S)) (h : BlindIsReducedFrom S x v)
  : Product (WordHeadNotComplement S x v) (IsReducedWord S v)
  ≔ match v [
  | nil. ↦ (star., star.)
  | cons. y v' ↦ (n ↦ h .fst (concat (Sum S S) y (letter_complement S x) (blind_complement S x) n
        (inverse (Sum S S) (blind_complement S x) (letter_complement S x) (b05_comp_eq S x))),
      b05_red_from_of S y v' (h .snd)) ]

def b05_red_from_to (S : Type) (x : Sum S S) (v : List (Sum S S))
  (h : Product (WordHeadNotComplement S x v) (IsReducedWord S v)) : BlindIsReducedFrom S x v
  ≔ match v [
  | nil. ↦ star.
  | cons. y v' ↦ (n ↦ h .fst (concat (Sum S S) y (blind_complement S x) (letter_complement S x) n (b05_comp_eq S x)),
      b05_red_from_to S y v' (h .snd)) ]

def b05_red_of_blind (S : Type) (w : List (Sum S S)) (h : BlindIsReduced S w) : IsReducedWord S w
  ≔ match w [ nil. ↦ star. | cons. x v ↦ b05_red_from_of S x v h ]

def b05_red_to_blind (S : Type) (w : List (Sum S S)) (h : IsReducedWord S w) : BlindIsReduced S w
  ≔ match w [ nil. ↦ star. | cons. x v ↦ b05_red_from_to S x v h ]

def bridge_def_is_reduced (S : Type) (w : List (Sum S S))
  : Product (BlindIsReduced S w → IsReducedWord S w) (IsReducedWord S w → BlindIsReduced S w)
  ≔ (b05_red_of_blind S w, b05_red_to_blind S w)

def b05_cpath (S : Type) (l r : List (Sum S S)) (x : Sum S S)
  : Id (List (Sum S S)) (append (Sum S S) l (cons. x (cons. (blind_complement S x) r)))
      (append (Sum S S) l (cons. x (cons. (letter_complement S x) r)))
  ≔ refl ((c ↦ append (Sum S S) l (cons. x (cons. c r))) : Sum S S → List (Sum S S)) (b05_comp_eq S x)

def b05_step_of_blind (S : Type) (u v : List (Sum S S)) (d : BlindDeleteStep S u v) : WordDeletionStep S u v
  ≔ let l ≔ d .fst in let r ≔ d .snd .fst in let x ≔ d .snd .snd .fst in
    (l, (x, (r,
      (concat (List (Sum S S)) u (append (Sum S S) l (cons. x (cons. (blind_complement S x) r)))
         (append (Sum S S) l (cons. x (cons. (letter_complement S x) r)))
         (d .snd .snd .snd .fst) (b05_cpath S l r x),
       d .snd .snd .snd .snd))))

def b05_step_to_blind (S : Type) (u v : List (Sum S S)) (d : WordDeletionStep S u v) : BlindDeleteStep S u v
  ≔ let l ≔ d .fst in let x ≔ d .snd .fst in let r ≔ d .snd .snd .fst in
    (l, (r, (x,
      (concat (List (Sum S S)) u (append (Sum S S) l (cons. x (cons. (letter_complement S x) r)))
         (append (Sum S S) l (cons. x (cons. (blind_complement S x) r)))
         (d .snd .snd .snd .fst)
         (inverse (List (Sum S S)) (append (Sum S S) l (cons. x (cons. (blind_complement S x) r)))
            (append (Sum S S) l (cons. x (cons. (letter_complement S x) r))) (b05_cpath S l r x)),
       d .snd .snd .snd .snd))))

def bridge_def_delete_step (S : Type) (u v : List (Sum S S))
  : Product (BlindDeleteStep S u v → WordDeletionStep S u v) (WordDeletionStep S u v → BlindDeleteStep S u v)
  ≔ (b05_step_of_blind S u v, b05_step_to_blind S u v)

def b05_in_of_blind (S : Type) (k : Nat) (u w : List (Sum S S)) (d : BlindReducesIn S k u w) : WordDeletions S k u w
  ≔ match k [
  | zero. ↦ d
  | suc. j ↦ (d .fst, (b05_step_of_blind S u (d .fst) (d .snd .fst), b05_in_of_blind S j (d .fst) w (d .snd .snd))) ]

def b05_in_to_blind (S : Type) (k : Nat) (u w : List (Sum S S)) (d : WordDeletions S k u w) : BlindReducesIn S k u w
  ≔ match k [
  | zero. ↦ d
  | suc. j ↦ (d .fst, (b05_step_to_blind S u (d .fst) (d .snd .fst), b05_in_to_blind S j (d .fst) w (d .snd .snd))) ]

def bridge_def_reduces_to (S : Type) (u w : List (Sum S S))
  : Product (BlindReducesTo S u w → WordReducesTo S u w) (WordReducesTo S u w → BlindReducesTo S u w)
  ≔ (d ↦ (d .fst, b05_in_of_blind S (d .fst) u w (d .snd)), d ↦ (d .fst, b05_in_to_blind S (d .fst) u w (d .snd)))

{` congp.tex:819: the blind ρ_S is ours. `}
def b05_choose_l (S : Type) (a : S) (y : Sum S S) (r : List (Sum S S)) (d : Decidable (Id (Sum S S) y (inr. a)))
  : Id (List (Sum S S)) (blind_reduce_choose S (inl. a) y r d) (fw_cancel_or_cons S (inl. a) y r d)
  ≔ match d [ inl. _ ↦ refl r | inr. _ ↦ refl (cons. (inl. a) (cons. y r) : List (Sum S S)) ]

def b05_choose_r (S : Type) (a : S) (y : Sum S S) (r : List (Sum S S)) (d : Decidable (Id (Sum S S) y (inl. a)))
  : Id (List (Sum S S)) (blind_reduce_choose S (inr. a) y r d) (fw_cancel_or_cons S (inr. a) y r d)
  ≔ match d [ inl. _ ↦ refl r | inr. _ ↦ refl (cons. (inr. a) (cons. y r) : List (Sum S S)) ]

def b05_cons_eq (S : Type) (dS : DecidableSet S) (x : Sum S S) (r : List (Sum S S))
  : Id (List (Sum S S)) (blind_reduce_cons S dS x r) (word_letter_reduce S (decidable_set_equality S dS) x r)
  ≔ match r [
  | nil. ↦ refl (cons. x nil. : List (Sum S S))
  | cons. y r' ↦ match x [
    | inl. a ↦ b05_choose_l S a y r' (blind_signed_decidable S dS y (inr. a))
    | inr. a ↦ b05_choose_r S a y r' (blind_signed_decidable S dS y (inl. a)) ] ]

def b05_rho_eq (S : Type) (dS : DecidableSet S) (w : List (Sum S S))
  : Id (List (Sum S S)) (blind_rho S dS w) (word_reduction S (decidable_set_equality S dS) w)
  ≔ let dec ≔ decidable_set_equality S dS in
    match w [
    | nil. ↦ refl (nil. : List (Sum S S))
    | cons. x v ↦ concat (List (Sum S S)) (blind_reduce_cons S dS x (blind_rho S dS v))
        (blind_reduce_cons S dS x (word_reduction S dec v)) (word_letter_reduce S dec x (word_reduction S dec v))
        (refl (blind_reduce_cons S dS x) (b05_rho_eq S dS v)) (b05_cons_eq S dS x (word_reduction S dec v)) ]

def bridge_def_rho (S : Type) (dS : DecidableSet S)
  : Id (List (Sum S S) → List (Sum S S)) (blind_rho S dS) (word_reduction S (decidable_set_equality S dS))
  ≔ funext (List (Sum S S)) (_ ↦ List (Sum S S)) (blind_rho S dS) (word_reduction S (decidable_set_equality S dS))
      (b05_rho_eq S dS)

def bridge_xca_rho : blind_xca_rho
  ≔ S dS w ↦
    let dec ≔ decidable_set_equality S dS in
    let L ≔ List (Sum S S) in
    let back ≔ inverse L (blind_rho S dS w) (word_reduction S dec w) (b05_rho_eq S dS w) in
    (b05_red_to_blind S (blind_rho S dS w)
       (transport L (IsReducedWord S) (word_reduction S dec w) (blind_rho S dS w) back (word_reduction_reduced S dec w)),
     bridge_def_reduces_to S w (blind_rho S dS w) .snd
       (transport L (v ↦ WordReducesTo S w v) (word_reduction S dec w) (blind_rho S dS w) back
          (word_reduces_to_reduction S dec w)))

{` congp.tex:824. Images of pointwise equal maps, identity on the first component. `}
def b05_image_map (A B : Type) (f g : A → B) (h : (a : A) → Id B (f a) (g a)) (r : Image A B f) : Image A B g
  ≔ (r .fst, mere_rec (BookFiber A B f (r .fst)) (Mere (BookFiber A B g (r .fst))) (mere_isprop (BookFiber A B g (r .fst)))
      (u ↦ mere (BookFiber A B g (r .fst)) (u .fst, concat B (r .fst) (f (u .fst)) (g (u .fst)) (u .snd) (h (u .fst))))
      (r .snd))

def b05_image_equiv (A B : Type) (f g : A → B) (h : (a : A) → Id B (f a) (g a)) : Equiv (Image A B f) (Image A B g)
  ≔ quasi_inverse_equiv (Image A B f) (Image A B g) (b05_image_map A B f g h)
      (b05_image_map A B g f (a ↦ inverse B (f a) (g a) (h a)))
      (r ↦ subtype_equal B (b ↦ Mere (BookFiber A B f b)) (b ↦ mere_isprop (BookFiber A B f b))
        (b05_image_map A B g f (a ↦ inverse B (f a) (g a) (h a)) (b05_image_map A B f g h r)) r (refl (r .fst)))
      (r ↦ subtype_equal B (b ↦ Mere (BookFiber A B g b)) (b ↦ mere_isprop (BookFiber A B g b))
        (b05_image_map A B f g h (b05_image_map A B g f (a ↦ inverse B (f a) (g a) (h a)) r)) r (refl (r .fst)))

def bridge_def_reduced_words (S : Type) (dS : DecidableSet S)
  : Equiv (BlindReducedWords S dS) (ReducedWordImage S (decidable_set_equality S dS))
  ≔ b05_image_equiv (List (Sum S S)) (List (Sum S S)) (blind_rho S dS) (word_reduction S (decidable_set_equality S dS))
      (b05_rho_eq S dS)

def bridge_def_reduced_words_fst (S : Type) (dS : DecidableSet S) (r : BlindReducedWords S dS)
  : Id (List (Sum S S)) (bridge_def_reduced_words S dS .map r .fst) (r .fst)
  ≔ refl (r .fst)

def b05_dyck_to (S : Type) (dS : DecidableSet S) (u : BlindDyckWords S dS) : DyckWord S (decidable_set_equality S dS)
  ≔ (u .fst, concat (List (Sum S S)) nil. (blind_rho S dS (u .fst)) (word_reduction S (decidable_set_equality S dS) (u .fst))
      (u .snd) (b05_rho_eq S dS (u .fst)))

def b05_dyck_from (S : Type) (dS : DecidableSet S) (u : DyckWord S (decidable_set_equality S dS)) : BlindDyckWords S dS
  ≔ (u .fst, concat (List (Sum S S)) nil. (word_reduction S (decidable_set_equality S dS) (u .fst)) (blind_rho S dS (u .fst))
      (u .snd) (inverse (List (Sum S S)) (blind_rho S dS (u .fst)) (word_reduction S (decidable_set_equality S dS) (u .fst))
        (b05_rho_eq S dS (u .fst))))

def bridge_def_dyck_words (S : Type) (dS : DecidableSet S)
  : Equiv (BlindDyckWords S dS) (DyckWord S (decidable_set_equality S dS))
  ≔ let dec ≔ decidable_set_equality S dS in
    let L ≔ List (Sum S S) in
    let hL : (a b : L) → isProp (Id L a b) ≔ signed_word_set S dec in
    quasi_inverse_equiv (BlindDyckWords S dS) (DyckWord S dec) (b05_dyck_to S dS) (b05_dyck_from S dS)
      (u ↦ subtype_equal L (w ↦ Id L nil. (blind_rho S dS w)) (w ↦ hL nil. (blind_rho S dS w))
        (b05_dyck_from S dS (b05_dyck_to S dS u)) u (refl (u .fst)))
      (u ↦ subtype_equal L (w ↦ Id L nil. (word_reduction S dec w)) (w ↦ hL nil. (word_reduction S dec w))
        (b05_dyck_to S dS (b05_dyck_from S dS u)) u (refl (u .fst)))

{` congp.tex:842, from word_quotient_image_equiv. `}
def bridge_rem_reduction_quotient : blind_rem_reduction_quotient
  ≔ S dS ↦
    let dec ≔ decidable_set_equality S dS in
    let L ≔ List (Sum S S) in
    let h ≔ b05_rho_eq S dS in
    (word_reduction_relation S dec,
     (u v ↦ (p ↦ concat L (blind_rho S dS u) (word_reduction S dec u) (blind_rho S dS v) (h u)
               (concat L (word_reduction S dec u) (word_reduction S dec v) (blind_rho S dS v) p
                  (inverse L (blind_rho S dS v) (word_reduction S dec v) (h v))),
             q ↦ concat L (word_reduction S dec u) (blind_rho S dS u) (word_reduction S dec v)
               (inverse L (blind_rho S dS u) (word_reduction S dec u) (h u))
               (concat L (blind_rho S dS u) (blind_rho S dS v) (word_reduction S dec v) q (h v))),
      (book_equivalence (WordReductionQuotient S dec) (BlindReducedWords S dS)
         (compose_equiv (WordReductionQuotient S dec) (ReducedWordImage S dec) (BlindReducedWords S dS)
            (word_quotient_image_equiv S dec)
            (b05_image_equiv L L (word_reduction S dec) (blind_rho S dS)
               (a ↦ inverse L (blind_rho S dS a) (word_reduction S dec a) (h a)))),
       u ↦ inverse L (blind_rho S dS u) (word_reduction S dec u) (h u))))

{` congp.tex:857. `}
def b05_interp_eq (S : SetTypes) (F : BlindFreeGroupSignature S) (w : List (Sum (S .fst) (S .fst)))
  : Id (Id (F .carrier) (F .base) (F .base)) (blind_interp S F w) (free_word_interpretation (S .fst) (b05_sig S F) w)
  ≔ let X ≔ F .carrier in let b ≔ F .base in
    match w [
    | nil. ↦ refl (refl b)
    | cons. x v ↦ match x [
      | inl. a ↦ refl ((p ↦ concat X b b b p (F .loop a)) : Id X b b → Id X b b) (b05_interp_eq S F v)
      | inr. a ↦ refl ((p ↦ concat X b b b p (inverse X b b (F .loop a))) : Id X b b → Id X b b) (b05_interp_eq S F v) ] ]

def bridge_def_interp (S : SetTypes) (F : BlindFreeGroupSignature S)
  : Id (List (Sum (S .fst) (S .fst)) → Id (F .carrier) (F .base) (F .base))
      (blind_interp S F) (free_word_interpretation (S .fst) (b05_sig S F))
  ≔ funext (List (Sum (S .fst) (S .fst))) (_ ↦ Id (F .carrier) (F .base) (F .base))
      (blind_interp S F) (free_word_interpretation (S .fst) (b05_sig S F)) (b05_interp_eq S F)

{` thm:free-group-elements, from free_group_elements_equiv. `}
def bridge_thm_free_group_elements : blind_thm_free_group_elements
  ≔ S dS F ↦
    let dec ≔ decidable_set_equality S dS in
    let S' ≔ blind_decidable_settype S dS in
    let L ≔ List (Sum S S) in
    let P ≔ Id (F .carrier) (F .base) (F .base) in
    let F' ≔ b05_sig S' F in
    transport (BlindReducedWords S dS → P) (f ↦ BookIsEquiv (BlindReducedWords S dS) P f)
      (r ↦ free_word_interpretation S F' (r .fst)) (r ↦ blind_interp S' F (r .fst))
      (funext (BlindReducedWords S dS) (_ ↦ P) (r ↦ free_word_interpretation S F' (r .fst)) (r ↦ blind_interp S' F (r .fst))
        (r ↦ inverse P (blind_interp S' F (r .fst)) (free_word_interpretation S F' (r .fst)) (b05_interp_eq S' F (r .fst))))
      (book_equivalence (BlindReducedWords S dS) P
        (compose_equiv (BlindReducedWords S dS) (ReducedWordImage S dec) P
          (bridge_def_reduced_words S dS) (free_group_elements_equiv S dec F')) .equiv)

{` congp.tex:929: first for Unit with any decidable-set structure and any
   point, from xca_reduced_words_one_integers, then along Unit = Fin 1. `}
def B05OneIntegers (S : Type) (dS : DecidableSet S) (a : S) : Type
  ≔ Σ (BookEquiv (BlindReducedWords S dS) Int) (e ↦
      Product (Id Int (e .map (blind_rs_empty S dS)) int_zero)
        ((r : BlindReducedWords S dS) → Id Int (e .map (blind_rs_succ S dS a r)) (int_succ (e .map r))))

def b05_unit_rho_eq (dS : DecidableSet Unit) (w : List (Sum Unit Unit))
  : Id (List (Sum Unit Unit)) (blind_rho Unit dS w) (word_reduction Unit unit_decidable_equality w)
  ≔ concat (List (Sum Unit Unit)) (blind_rho Unit dS w) (word_reduction Unit (decidable_set_equality Unit dS) w)
      (word_reduction Unit unit_decidable_equality w) (b05_rho_eq Unit dS w)
      (refl ((d ↦ word_reduction Unit d w) : DecidableEquality Unit → List (Sum Unit Unit))
        (decidable_equality_prop Unit unit_set (decidable_set_equality Unit dS) unit_decidable_equality))

def b05_unit_equiv (dS : DecidableSet Unit) : Equiv (BlindReducedWords Unit dS) Int
  ≔ compose_equiv (BlindReducedWords Unit dS) (ReducedWordImage Unit unit_decidable_equality) Int
      (b05_image_equiv (List (Sum Unit Unit)) (List (Sum Unit Unit)) (blind_rho Unit dS)
        (word_reduction Unit unit_decidable_equality) (b05_unit_rho_eq dS))
      reduced_words_one_integers_equiv

def b05_unit_one_integers (dS : DecidableSet Unit) (a : Unit) : B05OneIntegers Unit dS a
  ≔ match a [
  | star. ↦
    (book_equivalence (BlindReducedWords Unit dS) Int (b05_unit_equiv dS),
     (refl int_zero,
      r ↦ concat Int (unit_word_degree (blind_rho Unit dS (cons. (inl. star.) (r .fst))))
        (unit_word_degree (word_reduction Unit unit_decidable_equality (cons. (inl. star.) (r .fst))))
        (int_succ (unit_word_degree (r .fst)))
        (refl unit_word_degree (b05_unit_rho_eq dS (cons. (inl. star.) (r .fst))))
        (unit_word_degree_reduction (cons. (inl. star.) (r .fst))))) ]

def b05_unit_fin_one : Equiv Unit blind_fin_one
  ≔ canonical_inverse_equiv blind_fin_one Unit fin_one_equiv

def bridge_xca_reduced_one_integers : blind_xca_reduced_one_integers
  ≔ transport Type (S ↦ (dS : DecidableSet S) (a : S) → B05OneIntegers S dS a) Unit blind_fin_one
      (ua Unit blind_fin_one b05_unit_fin_one) b05_unit_one_integers blind_fin_one_dset blind_fin_one_star
