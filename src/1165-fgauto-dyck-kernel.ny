export "865-free-group"

{` Chapter 11, automata part 16: the running-text claim at
   fggroups.tex:870-871, "Let iota : F(S) → S~* map an element of the free
   group to the corresponding reduced word.  The kernel of iota is the
   2-sided Dyck language D_S."

   iota is injective, so its kernel is not meant literally; the claim is
   about the projection S~* → F(S), w |-> [w], of which iota is a section:
   its kernel is D_S, the words with rho(w) = eps (module 861's DyckWord is
   the fiber of rho over eps).  Stated for the free group of any
   FreeGroupSignature F (in particular the constructed one, module 882,
   whose USym is judgmentally that of free_group at the constructed
   signature): [w] = 1 iff rho(w) = eps (fgauto_kernel_dyck); the section
   property iota [w] = rho(w) is the equivalence of module 864
   (fgauto_iota_section). `}

def fgauto_iota (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (g : USym (free_group S dec F)) : SignedWord S
  ≔ equiv_inverse_map (ReducedWord S) (USym (free_group S dec F)) (free_group_usym_reduced_words S dec F) g .fst

def fgauto_iota_section (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (r : ReducedWord S)
  : Id (SignedWord S) (fgauto_iota S dec F (free_group_word S dec F (r .fst))) (r .fst)
  ≔ refl ((z ↦ z .fst) : ReducedWord S → SignedWord S)
      (inverse (ReducedWord S) r
        (equiv_inverse_map (ReducedWord S) (USym (free_group S dec F)) (free_group_usym_reduced_words S dec F)
          (free_group_usym_reduced_words S dec F .map r))
        (equiv_unit (ReducedWord S) (USym (free_group S dec F)) (free_group_usym_reduced_words S dec F) r))

def fgauto_kernel_dyck (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (w : SignedWord S)
  : Product (Id (USym (free_group S dec F)) (free_group_word S dec F w) (usym_unit (free_group S dec F))
        → Id (SignedWord S) (word_reduction S dec w) nil.)
      (Id (SignedWord S) (word_reduction S dec w) nil.
        → Id (USym (free_group S dec F)) (free_group_word S dec F w) (usym_unit (free_group S dec F)))
  ≔ let G ≔ USym (free_group S dec F) in
    let e ≔ free_group_usym_reduced_words S dec F in
    let rw : ReducedWord S ≔ (word_reduction S dec w, word_reduction_reduced S dec w) in
    let red : Id G (free_group_word S dec F (word_reduction S dec w)) (free_group_word S dec F w)
      ≔ free_word_interpretation_reduction S dec F w in
    (h ↦ refl ((z ↦ z .fst) : ReducedWord S → SignedWord S)
       (equivalence_injective (ReducedWord S) G e rw (reduced_word_empty S)
         (concat G (e .map rw) (free_group_word S dec F w) (usym_unit (free_group S dec F)) red h)),
     h ↦ concat G (free_group_word S dec F w) (free_group_word S dec F (word_reduction S dec w)) (usym_unit (free_group S dec F))
       (inverse G (free_group_word S dec F (word_reduction S dec w)) (free_group_word S dec F w) red)
       (refl (free_group_word S dec F) h))
