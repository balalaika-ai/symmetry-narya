export "1157-fgauto-stallings-vertices"
export "1160-fgauto-languages"
export "700-monoids-and-group-laws"

{` Chapter 11, automata part 12: the theorem at fggroups.tex:959, "A
   subgroup H of G is recognizable iff it has finite index".

   G is the finitely generated group of the preceding theorems (891): an
   abstract group with a map a : S → G from a finite set S of generators
   whose matched homomorphism S~* → G is surjective (FgautoGeneratesGroup).
   H is a subgroup given as a subset closed under unit, product and
   inverse; its index is the number of right cosets H g (set quotient of G
   by g ~ g' iff g g'^-1 in H), and "finite index" means that this set is
   finite.  Recognizable: recognized by a finite right G-action (module
   1160).

   "<=": G acts on the finite set of cosets by right multiplication; H is
   the set of g with H g = H.
   "=>": cosets have decidable equality (H g = H g' iff q0 . g g'^-1 lies in
   the decidable subset F); g |-> (q |-> q . g) has a finite image (a set of
   maps Fin n → Fin n), computed by a breadth-first search in the graph whose
   vertices are all maps Fin n → Fin n and whose edges are the right
   actions of the generators (module 1155), and elements with the same
   image lie in the same coset.  Hence the cosets are the image of a finite
   set and, having decidable equality, form a finite set.  Finite generation
   of G is needed for this constructive argument (the book's G is
   finitely generated). `}

{` Subgroups of an abstract group and right cosets. `}
def FgautoAbstractSubgroup (G : AbstractGroup) (H : Subtypes (G .carrier)) : Type
  ≔ Product (H (G .unit) .fst)
      (Product ((g h : G .carrier) → H g .fst → H h .fst → H (G .mul g h) .fst)
        ((g : G .carrier) → H g .fst → H (G .inv g) .fst))

def fgauto_group_subset_transport (G : AbstractGroup) (H : Subtypes (G .carrier)) (g h : G .carrier)
  (e : Id (G .carrier) g h) (m : H g .fst) : H h .fst
  ≔ transport (G .carrier) (z ↦ H z .fst) g h e m

def fgauto_group_coset_relation (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  : EquivalenceRelation (G .carrier)
  ≔ let C ≔ G .carrier in
    let m ≔ G .mul in
    let i ≔ G .inv in
    (g g' ↦ H (m g (i g')),
     g ↦ fgauto_group_subset_transport G H (G .unit) (m g (i g)) (inverse C (m g (i g)) (G .unit) (G .laws .inv_right g)) (hH .fst),
     g g' h ↦ fgauto_group_subset_transport G H (i (m g (i g'))) (m g' (i g))
       (concat C (i (m g (i g'))) (m (i (i g')) (i g)) (m g' (i g)) (ag_inv_mul G g (i g'))
         (refl ((z ↦ m z (i g)) : C → C) (ag_inv_inv G g')))
       (hH .snd .snd (m g (i g')) h),
     g g' g'' h1 h2 ↦ fgauto_group_subset_transport G H (m (m g (i g')) (m g' (i g''))) (m g (i g''))
       (concat C (m (m g (i g')) (m g' (i g''))) (m g (m (i g') (m g' (i g'')))) (m g (i g''))
         (inverse C (m g (m (i g') (m g' (i g'')))) (m (m g (i g')) (m g' (i g''))) (G .laws .assoc g (i g') (m g' (i g''))))
         (refl (m g) (ag_mul_inv_cancel_left G g' (i g''))))
       (hH .snd .fst (m g (i g')) (m g' (i g'')) h1 h2))

def FgautoGroupCosets (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H) : Type
  ≔ Quotient (G .carrier) (fgauto_group_coset_relation G H hH)

def FgautoGroupFiniteIndex (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H) : Type
  ≔ IsFinite (FgautoGroupCosets G H hH)

{` "<=": the action on the cosets. `}
def fgauto_coset_act (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (z : FgautoGroupCosets G H hH) (g : G .carrier) : FgautoGroupCosets G H hH
  ≔ let R ≔ fgauto_group_coset_relation G H hH in
    let C ≔ G .carrier in
    let m ≔ G .mul in
    let i ≔ G .inv in
    quotient_rec C (FgautoGroupCosets G H hH) R (quotient_set C R) (k ↦ quotient_class C R (m k g))
      (k k' r ↦ quotient_encode C R (m k g) (m k' g)
        (fgauto_group_subset_transport G H (m k (i k')) (m (m k g) (i (m k' g)))
          (calc
            m k (i k') = m (m (m k g) (i g)) (i k')
              by refl ((y ↦ m y (i k')) : C → C) (inverse C (m (m k g) (i g)) k (ag_mul_inv_cancel_right G k g))
            = m (m k g) (m (i g) (i k'))
              by inverse C (m (m k g) (m (i g) (i k'))) (m (m (m k g) (i g)) (i k')) (G .laws .assoc (m k g) (i g) (i k'))
            = m (m k g) (i (m k' g))
              by refl (m (m k g)) (inverse C (i (m k' g)) (m (i g) (i k')) (ag_inv_mul G k' g)) ∎)
          r))
      z

def fgauto_coset_act_class (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (k g : G .carrier)
  : Id (FgautoGroupCosets G H hH) (fgauto_coset_act G H hH (quotient_class (G .carrier) (fgauto_group_coset_relation G H hH) k) g)
      (quotient_class (G .carrier) (fgauto_group_coset_relation G H hH) (G .mul k g))
  ≔ refl (quotient_class (G .carrier) (fgauto_group_coset_relation G H hH) (G .mul k g))

{` Proposition-valued induction on cosets. `}
def fgauto_coset_ind_prop (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (P : FgautoGroupCosets G H hH → Type) (hP : (z : FgautoGroupCosets G H hH) → isProp (P z))
  (h : (k : G .carrier) → P (quotient_class (G .carrier) (fgauto_group_coset_relation G H hH) k))
  (z : FgautoGroupCosets G H hH) : P z
  ≔ let R ≔ fgauto_group_coset_relation G H hH in
    mere_rec (BookFiber (G .carrier) (FgautoGroupCosets G H hH) (quotient_class (G .carrier) R) z) (P z) (hP z)
      (y ↦ transport (FgautoGroupCosets G H hH) P (quotient_class (G .carrier) R (y .fst)) z
        (inverse (FgautoGroupCosets G H hH) z (quotient_class (G .carrier) R (y .fst)) (y .snd)) (h (y .fst)))
      (quotient_surjective (G .carrier) R z)

def fgauto_coset_act_unit (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (z : FgautoGroupCosets G H hH) : Id (FgautoGroupCosets G H hH) (fgauto_coset_act G H hH z (G .unit)) z
  ≔ let R ≔ fgauto_group_coset_relation G H hH in
    fgauto_coset_ind_prop G H hH (z ↦ Id (FgautoGroupCosets G H hH) (fgauto_coset_act G H hH z (G .unit)) z)
      (z ↦ quotient_set (G .carrier) R (fgauto_coset_act G H hH z (G .unit)) z)
      (k ↦ refl (quotient_class (G .carrier) R) (G .laws .unit_right k)) z

def fgauto_coset_act_mul (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (z : FgautoGroupCosets G H hH) (g g' : G .carrier)
  : Id (FgautoGroupCosets G H hH) (fgauto_coset_act G H hH z (G .mul g g'))
      (fgauto_coset_act G H hH (fgauto_coset_act G H hH z g) g')
  ≔ let R ≔ fgauto_group_coset_relation G H hH in
    fgauto_coset_ind_prop G H hH
      (z ↦ Id (FgautoGroupCosets G H hH) (fgauto_coset_act G H hH z (G .mul g g'))
        (fgauto_coset_act G H hH (fgauto_coset_act G H hH z g) g'))
      (z ↦ quotient_set (G .carrier) R (fgauto_coset_act G H hH z (G .mul g g'))
        (fgauto_coset_act G H hH (fgauto_coset_act G H hH z g) g'))
      (k ↦ refl (quotient_class (G .carrier) R) (G .laws .assoc k g g')) z

{` H g = H iff g in H. `}
def fgauto_coset_unit_iff (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (g : G .carrier)
  : FgautoIff (H g .fst)
      (Id (FgautoGroupCosets G H hH) (quotient_class (G .carrier) (fgauto_group_coset_relation G H hH) g)
        (quotient_class (G .carrier) (fgauto_group_coset_relation G H hH) (G .unit)))
  ≔ let R ≔ fgauto_group_coset_relation G H hH in
    let C ≔ G .carrier in
    let p : Id C (G .mul g (G .inv (G .unit))) g
      ≔ concat C (G .mul g (G .inv (G .unit))) (G .mul g (G .unit)) g
          (refl (G .mul g) (ag_inv_unit G)) (G .laws .unit_right g) in
    (h ↦ quotient_encode C R g (G .unit) (fgauto_group_subset_transport G H g (G .mul g (G .inv (G .unit))) (inverse C (G .mul g (G .inv (G .unit))) g p) h),
     e ↦ fgauto_group_subset_transport G H (G .mul g (G .inv (G .unit))) g p (quotient_effective C R g (G .unit) .map e))

def fgauto_finite_index_recognizable (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (hf : FgautoGroupFiniteIndex G H hH) : FgautoRecognizable (fgauto_group_monoid G) (g ↦ H g .fst)
  ≔ let R ≔ fgauto_group_coset_relation G H hH in
    let C ≔ FgautoGroupCosets G H hH in
    let M ≔ fgauto_group_monoid G in
    let goal ≔ FgautoRecognizable M (g ↦ H g .fst) in
    mere_rec (Σ Nat (N ↦ Id Type C (Fin N))) goal
      (mere_isprop (Σ (FgautoFiniteAction M) (A ↦ Σ (Fin (A .asize)) (q0 ↦ Σ (Fin (A .asize) → Bool) (F ↦
         FgautoRecognizes M A q0 F (g ↦ H g .fst))))))
      (z ↦
        let N ≔ z .fst in
        let e ≔ id_to_equiv C (Fin N) (z .snd) in
        let ei ≔ equiv_inverse_map C (Fin N) e in
        let act : Fin N → G .carrier → Fin N ≔ q g ↦ e .map (fgauto_coset_act G H hH (ei q) g) in
        let A : FgautoFiniteAction M
          ≔ (N, act,
             q ↦ concat (Fin N) (act q (G .unit)) (e .map (ei q)) q
               (refl (e .map) (fgauto_coset_act_unit G H hH (ei q))) (equiv_counit C (Fin N) e q),
             q g g' ↦ concat (Fin N) (act q (G .mul g g'))
               (e .map (fgauto_coset_act G H hH (fgauto_coset_act G H hH (ei q) g) g')) (act (act q g) g')
               (refl (e .map) (fgauto_coset_act_mul G H hH (ei q) g g'))
               (refl ((y ↦ e .map (fgauto_coset_act G H hH y g')) : C → Fin N)
                 (equiv_unit C (Fin N) e (fgauto_coset_act G H hH (ei q) g)))) in
        let q0 ≔ e .map (quotient_class (G .carrier) R (G .unit)) in
        let F : Fin N → Bool ≔ q ↦ fgauto_decision_bool (Id (Fin N) q q0) (fin_decidable_equality N q q0) in
        let actq0 : (g : G .carrier) → Id (Fin N) (act q0 g) (e .map (quotient_class (G .carrier) R g))
          ≔ g ↦ concat (Fin N) (act q0 g) (e .map (fgauto_coset_act G H hH (quotient_class (G .carrier) R (G .unit)) g))
              (e .map (quotient_class (G .carrier) R g))
              (refl ((y ↦ e .map (fgauto_coset_act G H hH y g)) : C → Fin N)
                (inverse C (quotient_class (G .carrier) R (G .unit)) (ei q0) (equiv_unit C (Fin N) e (quotient_class (G .carrier) R (G .unit)))))
              (refl ((y ↦ e .map (quotient_class (G .carrier) R y)) : G .carrier → Fin N) (G .laws .unit_left g)) in
        mere (Σ (FgautoFiniteAction M) (A ↦ Σ (Fin (A .asize)) (q0 ↦ Σ (Fin (A .asize) → Bool) (F ↦
            FgautoRecognizes M A q0 F (g ↦ H g .fst)))))
          (A, (q0, (F, g ↦
            (h ↦ fgauto_decision_bool_true (Id (Fin N) (act q0 g) q0) (fin_decidable_equality N (act q0 g) q0)
               (concat (Fin N) (act q0 g) (e .map (quotient_class (G .carrier) R g)) q0 (actq0 g)
                 (refl (e .map) (fgauto_coset_unit_iff G H hH g .fst h))),
             t ↦ fgauto_coset_unit_iff G H hH g .snd
               (equivalence_injective C (Fin N) e (quotient_class (G .carrier) R g) (quotient_class (G .carrier) R (G .unit))
                 (concat (Fin N) (e .map (quotient_class (G .carrier) R g)) (act q0 g) q0
                   (inverse (Fin N) (act q0 g) (e .map (quotient_class (G .carrier) R g)) (actq0 g))
                   (fgauto_decision_bool_reflect (Id (Fin N) (act q0 g) q0) (fin_decidable_equality N (act q0 g) q0) t))))))))
      hf

{` "=>".  Finite lists: elements of Fin m, maps Fin k → B, signed letters. `}
def fgauto_fin_list (m : Nat) : List (Fin m)
  ≔ match m [
  | zero. ↦ nil.
  | suc. k ↦ cons. (inr. star.) (fgauto_list_map (Fin k) (Fin (suc. k)) (j ↦ inl. j) (fgauto_fin_list k)) ]

def fgauto_fin_list_complete (m : Nat) (i : Fin m) : FgautoMem (Fin m) i (fgauto_fin_list m)
  ≔ match m [
  | zero. ↦ match i []
  | suc. k ↦ match i [
    | inl. j ↦ inr. (fgauto_mem_map (Fin k) (Fin (suc. k)) (j0 ↦ inl. j0) j (fgauto_fin_list k) (fgauto_fin_list_complete k j))
    | inr. u ↦ inl. (inr. (unit_prop u star.)) ] ]

def fgauto_list_bind (A B : Type) (l : List A) (k : A → List B) : List B
  ≔ match l [ nil. ↦ nil. | cons. a t ↦ append B (k a) (fgauto_list_bind A B t k) ]

def fgauto_mem_bind (A B : Type) (l : List A) (k : A → List B) (a : A) (b : B) (ma : FgautoMem A a l)
  (mb : FgautoMem B b (k a)) : FgautoMem B b (fgauto_list_bind A B l k)
  ≔ match l [
  | nil. ↦ match ma []
  | cons. a' t ↦ match ma [
    | inl. e ↦ fgauto_mem_append_left B b (k a') (fgauto_list_bind A B t k)
        (transport A (z ↦ FgautoMem B b (k z)) a a' e mb)
    | inr. m ↦ fgauto_mem_append_right B b (k a') (fgauto_list_bind A B t k) (fgauto_mem_bind A B t k a b m mb) ] ]

def fgauto_fin_extend (B : Type) (k : Nat) (g : Fin k → B) (b : B) : Fin (suc. k) → B
  ≔ [ inl. j ↦ g j | inr. _ ↦ b ]

def fgauto_fin_zero_fun (B : Type) : Fin zero. → B ≔ i ↦ match i []

def fgauto_fin_functions (B : Type) (lB : List B) (k : Nat) : List (Fin k → B)
  ≔ match k [
  | zero. ↦ cons. (fgauto_fin_zero_fun B) nil.
  | suc. k' ↦ fgauto_list_bind (Fin k' → B) (Fin (suc. k') → B) (fgauto_fin_functions B lB k')
      (g ↦ fgauto_list_map B (Fin (suc. k') → B) (b ↦ fgauto_fin_extend B k' g b) lB) ]

def fgauto_fin_functions_complete (B : Type) (lB : List B) (cB : (b : B) → FgautoMem B b lB) (k : Nat) (f : Fin k → B)
  : FgautoMem (Fin k → B) f (fgauto_fin_functions B lB k)
  ≔ match k [
  | zero. ↦ inl. (funext (Fin zero.) (_ ↦ B) f (fgauto_fin_zero_fun B) (i ↦ match i []))
  | suc. k' ↦
    let g : Fin k' → B ≔ j ↦ f (inl. j) in
    let b ≔ f (inr. star.) in
    let p : Id (Fin (suc. k') → B) f (fgauto_fin_extend B k' g b)
      ≔ funext (Fin (suc. k')) (_ ↦ B) f (fgauto_fin_extend B k' g b)
          (i ↦ match i [ inl. j ↦ refl (f (inl. j)) | inr. u ↦ match u [ star. ↦ refl (f (inr. star.)) ] ]) in
    fgauto_mem_transport (Fin (suc. k') → B) (fgauto_fin_extend B k' g b) f (fgauto_fin_functions B lB (suc. k'))
      (inverse (Fin (suc. k') → B) f (fgauto_fin_extend B k' g b) p)
      (fgauto_mem_bind (Fin k' → B) (Fin (suc. k') → B) (fgauto_fin_functions B lB k')
        (g0 ↦ fgauto_list_map B (Fin (suc. k') → B) (b0 ↦ fgauto_fin_extend B k' g0 b0) lB) g (fgauto_fin_extend B k' g b)
        (fgauto_fin_functions_complete B lB cB k' g)
        (fgauto_mem_map B (Fin (suc. k') → B) (b0 ↦ fgauto_fin_extend B k' g b0) b lB (cB b))) ]

def fgauto_fin_fun_decidable_equality (n m : Nat) : DecidableEquality (Fin n → Fin m)
  ≔ f g ↦ match fin_forall_decidable n (i ↦ Id (Fin m) (f i) (g i)) (i ↦ fin_decidable_equality m (f i) (g i)) [
  | inl. h ↦ inl. (funext (Fin n) (_ ↦ Fin m) f g h)
  | inr. no ↦ inr. (p ↦ no (happly (Fin n) (_ ↦ Fin m) f g p)) ]

def fgauto_signed_letters (S : Type) (l : List S) : List (SignedLetter S)
  ≔ append (SignedLetter S) (fgauto_list_map S (SignedLetter S) (s ↦ inl. s) l) (fgauto_list_map S (SignedLetter S) (s ↦ inr. s) l)

def fgauto_signed_letters_complete (S : Type) (l : List S) (c : (s : S) → FgautoMem S s l) (x : SignedLetter S)
  : FgautoMem (SignedLetter S) x (fgauto_signed_letters S l)
  ≔ match x [
  | inl. s ↦ fgauto_mem_append_left (SignedLetter S) (inl. s) (fgauto_list_map S (SignedLetter S) (s0 ↦ inl. s0) l)
      (fgauto_list_map S (SignedLetter S) (s0 ↦ inr. s0) l) (fgauto_mem_map S (SignedLetter S) (s0 ↦ inl. s0) s l (c s))
  | inr. s ↦ fgauto_mem_append_right (SignedLetter S) (inr. s) (fgauto_list_map S (SignedLetter S) (s0 ↦ inl. s0) l)
      (fgauto_list_map S (SignedLetter S) (s0 ↦ inr. s0) l) (fgauto_mem_map S (SignedLetter S) (s0 ↦ inr. s0) s l (c s)) ]

def fgauto_finite_enumeration (S : Type) (m : Nat) (e : Equiv S (Fin m))
  : Σ (List S) (l ↦ (s : S) → FgautoMem S s l)
  ≔ let ei ≔ equiv_inverse_map S (Fin m) e in
    (fgauto_list_map (Fin m) S ei (fgauto_fin_list m),
     s ↦ fgauto_mem_transport S (ei (e .map s)) s (fgauto_list_map (Fin m) S ei (fgauto_fin_list m))
       (inverse S s (ei (e .map s)) (equiv_unit S (Fin m) e s))
       (fgauto_mem_map (Fin m) S ei (e .map s) (fgauto_fin_list m) (fgauto_fin_list_complete m (e .map s))))

{` Edges given by list membership are steps. `}
def fgauto_mem_edge_step (S V : Type) (E : List (FgautoEdge S V)) (e : FgautoEdge S V) (m : FgautoMem (FgautoEdge S V) e E)
  : FgautoStep S V E (e .src) (e .lab) (e .tgt)
  ≔ match E [
  | nil. ↦ match m []
  | cons. e' E' ↦ match m [
    | inl. p ↦ inl. (refl ((z ↦ z .src) : FgautoEdge S V → V) p,
        (refl ((z ↦ z .lab) : FgautoEdge S V → SignedLetter S) p, refl ((z ↦ z .tgt) : FgautoEdge S V → V) p))
    | inr. m' ↦ inr. (fgauto_mem_edge_step S V E' e m') ] ]

{` The transition graph of a finite action on Fin N through the generators. `}
def fgauto_trans_step (S : Type) (G : AbstractGroup) (a : S → G .carrier) (A : FgautoFiniteAction (fgauto_group_monoid G))
  (f : Fin (A .asize) → Fin (A .asize)) (x : SignedLetter S) : Fin (A .asize) → Fin (A .asize)
  ≔ q ↦ A .aact (f q) (fgauto_matched_letter S G a x)

def fgauto_trans_edges_at (S : Type) (G : AbstractGroup) (a : S → G .carrier) (A : FgautoFiniteAction (fgauto_group_monoid G))
  (L : List (SignedLetter S)) (f : Fin (A .asize) → Fin (A .asize)) : List (FgautoEdge S (Fin (A .asize) → Fin (A .asize)))
  ≔ fgauto_list_map (SignedLetter S) (FgautoEdge S (Fin (A .asize) → Fin (A .asize)))
      (x ↦ (f, x, fgauto_trans_step S G a A f x)) L

def fgauto_trans_edges (S : Type) (G : AbstractGroup) (a : S → G .carrier) (A : FgautoFiniteAction (fgauto_group_monoid G))
  (L : List (SignedLetter S)) : List (FgautoEdge S (Fin (A .asize) → Fin (A .asize)))
  ≔ fgauto_list_bind (Fin (A .asize) → Fin (A .asize)) (FgautoEdge S (Fin (A .asize) → Fin (A .asize)))
      (fgauto_fin_functions (Fin (A .asize)) (fgauto_fin_list (A .asize)) (A .asize))
      (fgauto_trans_edges_at S G a A L)

def fgauto_trans_edges_at_functional (S : Type) (G : AbstractGroup) (a : S → G .carrier)
  (A : FgautoFiniteAction (fgauto_group_monoid G)) (L : List (SignedLetter S)) (f : Fin (A .asize) → Fin (A .asize))
  (p : Fin (A .asize) → Fin (A .asize)) (x : SignedLetter S) (q : Fin (A .asize) → Fin (A .asize))
  (s : FgautoStep S (Fin (A .asize) → Fin (A .asize)) (fgauto_trans_edges_at S G a A L f) p x q)
  : Id (Fin (A .asize) → Fin (A .asize)) q (fgauto_trans_step S G a A p x)
  ≔ match L [
  | nil. ↦ match s []
  | cons. y L' ↦ match s [
    | inl. t ↦ concat (Fin (A .asize) → Fin (A .asize)) q (fgauto_trans_step S G a A f y) (fgauto_trans_step S G a A p x)
        (t .snd .snd)
        (refl ((u v ↦ fgauto_trans_step S G a A u v) : (Fin (A .asize) → Fin (A .asize)) → SignedLetter S → Fin (A .asize) → Fin (A .asize))
          (inverse (Fin (A .asize) → Fin (A .asize)) p f (t .fst)) (inverse (SignedLetter S) x y (t .snd .fst)))
    | inr. s' ↦ fgauto_trans_edges_at_functional S G a A L' f p x q s' ] ]

def fgauto_bind_edges_functional (S V : Type) (step : V → SignedLetter S → V) (U : List V)
  (k : V → List (FgautoEdge S V))
  (hk : (f p : V) (x : SignedLetter S) (q : V) → FgautoStep S V (k f) p x q → Id V q (step p x))
  (p : V) (x : SignedLetter S) (q : V) (s : FgautoStep S V (fgauto_list_bind V (FgautoEdge S V) U k) p x q)
  : Id V q (step p x)
  ≔ match U [
  | nil. ↦ match s []
  | cons. f U' ↦ match fgauto_step_append_split S V (k f) (fgauto_list_bind V (FgautoEdge S V) U' k) p x q s [
    | inl. s1 ↦ hk f p x q s1
    | inr. s2 ↦ fgauto_bind_edges_functional S V step U' k hk p x q s2 ] ]

{` Runs of the transition graph compute the action of the word. `}
def fgauto_trans_run_value (S : Type) (G : AbstractGroup) (a : S → G .carrier) (A : FgautoFiniteAction (fgauto_group_monoid G))
  (L : List (SignedLetter S)) (g : Fin (A .asize) → Fin (A .asize)) (w : SignedWord S) (f : Fin (A .asize) → Fin (A .asize))
  (r : FgautoRun S (Fin (A .asize) → Fin (A .asize)) (fgauto_trans_edges S G a A L) g w f) (q : Fin (A .asize))
  : Id (Fin (A .asize)) (f q) (A .aact (g q) (fgauto_matched_hom S G a w))
  ≔ let N ≔ A .asize in
    match w [
    | nil. ↦ concat (Fin N) (f q) (g q) (A .aact (g q) (G .unit))
        (inverse (Fin N) (g q) (f q) (happly (Fin N) (_ ↦ Fin N) g f r q))
        (inverse (Fin N) (A .aact (g q) (G .unit)) (g q) (A .aunit (g q)))
    | cons. x w' ↦
      let rr ≔ r .fst in
      let ev : Id (Fin N → Fin N) rr (fgauto_trans_step S G a A g x)
        ≔ fgauto_bind_edges_functional S (Fin N → Fin N) (fgauto_trans_step S G a A)
            (fgauto_fin_functions (Fin N) (fgauto_fin_list N) N) (fgauto_trans_edges_at S G a A L)
            (fgauto_trans_edges_at_functional S G a A L) g x rr (r .snd .fst) in
      concat (Fin N) (f q) (A .aact (rr q) (fgauto_matched_hom S G a w'))
        (A .aact (g q) (fgauto_matched_hom S G a (cons. x w')))
        (fgauto_trans_run_value S G a A L rr w' f (r .snd .snd) q)
        (concat (Fin N) (A .aact (rr q) (fgauto_matched_hom S G a w'))
          (A .aact (A .aact (g q) (fgauto_matched_letter S G a x)) (fgauto_matched_hom S G a w'))
          (A .aact (g q) (fgauto_matched_hom S G a (cons. x w')))
          (refl ((y ↦ A .aact y (fgauto_matched_hom S G a w')) : Fin N → Fin N) (happly (Fin N) (_ ↦ Fin N) rr (fgauto_trans_step S G a A g x) ev q))
          (inverse (Fin N) (A .aact (g q) (fgauto_matched_hom S G a (cons. x w')))
            (A .aact (A .aact (g q) (fgauto_matched_letter S G a x)) (fgauto_matched_hom S G a w'))
            (A .amul (g q) (fgauto_matched_letter S G a x) (fgauto_matched_hom S G a w')))) ]

def fgauto_trans_run_exists (S : Type) (G : AbstractGroup) (a : S → G .carrier) (A : FgautoFiniteAction (fgauto_group_monoid G))
  (L : List (SignedLetter S)) (cL : (x : SignedLetter S) → FgautoMem (SignedLetter S) x L)
  (g : Fin (A .asize) → Fin (A .asize)) (w : SignedWord S)
  : FgautoRun S (Fin (A .asize) → Fin (A .asize)) (fgauto_trans_edges S G a A L) g w
      (q ↦ A .aact (g q) (fgauto_matched_hom S G a w))
  ≔ let N ≔ A .asize in
    let U ≔ fgauto_fin_functions (Fin N) (fgauto_fin_list N) N in
    match w [
    | nil. ↦ funext (Fin N) (_ ↦ Fin N) g (q ↦ A .aact (g q) (G .unit))
        (q ↦ inverse (Fin N) (A .aact (g q) (G .unit)) (g q) (A .aunit (g q)))
    | cons. x w' ↦
      let st ≔ fgauto_trans_step S G a A g x in
      (st,
       (fgauto_mem_edge_step S (Fin N → Fin N) (fgauto_trans_edges S G a A L) (g, x, st)
          (fgauto_mem_bind (Fin N → Fin N) (FgautoEdge S (Fin N → Fin N)) U (fgauto_trans_edges_at S G a A L) g (g, x, st)
            (fgauto_fin_functions_complete (Fin N) (fgauto_fin_list N) (fgauto_fin_list_complete N) N g)
            (fgauto_mem_map (SignedLetter S) (FgautoEdge S (Fin N → Fin N)) (y ↦ (g, y, fgauto_trans_step S G a A g y)) x L (cL x))),
        fgauto_run_end S (Fin N → Fin N) (fgauto_trans_edges S G a A L) st w'
          (q ↦ A .aact (st q) (fgauto_matched_hom S G a w')) (q ↦ A .aact (g q) (fgauto_matched_hom S G a (cons. x w')))
          (funext (Fin N) (_ ↦ Fin N) (q ↦ A .aact (st q) (fgauto_matched_hom S G a w'))
            (q ↦ A .aact (g q) (fgauto_matched_hom S G a (cons. x w')))
            (q ↦ inverse (Fin N) (A .aact (g q) (fgauto_matched_hom S G a (cons. x w')))
              (A .aact (st q) (fgauto_matched_hom S G a w'))
              (A .amul (g q) (fgauto_matched_letter S G a x) (fgauto_matched_hom S G a w'))))
          (fgauto_trans_run_exists S G a A L cL st w'))) ]

{` Elements acting in the same way lie in the same coset. `}
def fgauto_same_action_coset (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (A : FgautoFiniteAction (fgauto_group_monoid G)) (q0 : Fin (A .asize)) (F : Fin (A .asize) → Bool)
  (hr : FgautoRecognizes (fgauto_group_monoid G) A q0 F (g ↦ H g .fst)) (x y : G .carrier)
  (h : (q : Fin (A .asize)) → Id (Fin (A .asize)) (A .aact q x) (A .aact q y))
  : H (G .mul x (G .inv y)) .fst
  ≔ let N ≔ A .asize in
    let iy ≔ G .inv y in
    let fq0 : Id Bool (F q0) true.
      ≔ transport (Fin N) (q ↦ Id Bool (F q) true.) (A .aact q0 (G .unit)) q0 (A .aunit q0) (hr (G .unit) .fst (hH .fst)) in
    hr (G .mul x iy) .snd
      (transport (Fin N) (q ↦ Id Bool (F q) true.) q0 (A .aact q0 (G .mul x iy))
        (calc
          q0 = A .aact q0 (G .unit) by inverse (Fin N) (A .aact q0 (G .unit)) q0 (A .aunit q0)
          = A .aact q0 (G .mul y iy) by refl (A .aact q0) (inverse (G .carrier) (G .mul y iy) (G .unit) (G .laws .inv_right y))
          = A .aact (A .aact q0 y) iy by A .amul q0 y iy
          = A .aact (A .aact q0 x) iy by refl ((z ↦ A .aact z iy) : Fin N → Fin N) (inverse (Fin N) (A .aact q0 x) (A .aact q0 y) (h q0))
          = A .aact q0 (G .mul x iy) by inverse (Fin N) (A .aact q0 (G .mul x iy)) (A .aact (A .aact q0 x) iy) (A .amul q0 x iy) ∎)
        fq0)

def fgauto_bool_decide_true (b : Bool) : Decidable (Id Bool b true.)
  ≔ match b [ true. ↦ inl. (refl (true. : Bool)) | false. ↦ inr. (e ↦ bool_encode false. true. e) ]

def fgauto_recognized_coset_decidable (G : AbstractGroup) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (A : FgautoFiniteAction (fgauto_group_monoid G)) (q0 : Fin (A .asize)) (F : Fin (A .asize) → Bool)
  (hr : FgautoRecognizes (fgauto_group_monoid G) A q0 F (g ↦ H g .fst))
  : DecidableRelation (G .carrier) (fgauto_group_coset_relation G H hH)
  ≔ x y ↦ match fgauto_bool_decide_true (F (A .aact q0 (G .mul x (G .inv y)))) [
  | inl. t ↦ inl. (hr (G .mul x (G .inv y)) .snd t)
  | inr. n ↦ inr. (h ↦ n (hr (G .mul x (G .inv y)) .fst h)) ]

{` The cosets are finite when H is recognized and G is generated by a. `}
def fgauto_recognized_finite_index_at (S : Type) (G : AbstractGroup) (a : S → G .carrier)
  (gen : FgautoGeneratesGroup S G a) (L : List (SignedLetter S)) (cL : (x : SignedLetter S) → FgautoMem (SignedLetter S) x L)
  (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (A : FgautoFiniteAction (fgauto_group_monoid G)) (q0 : Fin (A .asize)) (F : Fin (A .asize) → Bool)
  (hr : FgautoRecognizes (fgauto_group_monoid G) A q0 F (g ↦ H g .fst)) : FgautoGroupFiniteIndex G H hH
  ≔ let N ≔ A .asize in
    let V ≔ Fin N → Fin N in
    let dV ≔ fgauto_fin_fun_decidable_equality N N in
    let E ≔ fgauto_trans_edges S G a A L in
    let idf : V ≔ q ↦ q in
    let R ≔ fgauto_group_coset_relation G H hH in
    let C ≔ FgautoGroupCosets G H hH in
    let Rl ≔ fgauto_reached S V dV E idf in
    let nR ≔ length V Rl in
    let wordOf : Fin nR → SignedWord S ≔ i ↦ fgauto_tree_word S V dV E idf (fgauto_list_nth V Rl i) in
    let f : Fin nR → C ≔ i ↦ quotient_class (G .carrier) R (fgauto_matched_hom S G a (wordOf i)) in
    let surj : Surjective (Fin nR) C f
      ≔ fgauto_coset_ind_prop G H hH (z ↦ Mere (BookFiber (Fin nR) C f z)) (z ↦ mere_isprop (BookFiber (Fin nR) C f z))
          (k ↦ mere_rec (Σ (SignedWord S) (w ↦ Id (G .carrier) (fgauto_matched_hom S G a w) k))
            (Mere (BookFiber (Fin nR) C f (quotient_class (G .carrier) R k)))
            (mere_isprop (BookFiber (Fin nR) C f (quotient_class (G .carrier) R k)))
            (uw ↦
              let u ≔ uw .fst in
              let v : V ≔ q ↦ A .aact q (fgauto_matched_hom S G a u) in
              let mv ≔ fgauto_reach_complete S V dV E idf u v (fgauto_trans_run_exists S G a A L cL idf u) in
              let i ≔ fgauto_list_pos V dV v Rl mv in
              let t ≔ wordOf i in
              let rt ≔ fgauto_tree_word_run S V dV E idf (fgauto_list_nth V Rl i) (fgauto_list_nth_mem V Rl i) in
              let same : (q : Fin N) → Id (Fin N) (A .aact q (fgauto_matched_hom S G a u)) (A .aact q (fgauto_matched_hom S G a t))
                ≔ q ↦ concat (Fin N) (A .aact q (fgauto_matched_hom S G a u)) (fgauto_list_nth V Rl i q)
                    (A .aact q (fgauto_matched_hom S G a t))
                    (happly (Fin N) (_ ↦ Fin N) v (fgauto_list_nth V Rl i)
                      (inverse V (fgauto_list_nth V Rl i) v (fgauto_list_pos_nth V dV v Rl mv)) q)
                    (fgauto_trans_run_value S G a A L idf t (fgauto_list_nth V Rl i) rt q) in
              mere (BookFiber (Fin nR) C f (quotient_class (G .carrier) R k))
                (i, concat C (quotient_class (G .carrier) R k) (quotient_class (G .carrier) R (fgauto_matched_hom S G a u)) (f i)
                  (refl (quotient_class (G .carrier) R) (inverse (G .carrier) (fgauto_matched_hom S G a u) k (uw .snd)))
                  (quotient_encode (G .carrier) R (fgauto_matched_hom S G a u) (fgauto_matched_hom S G a t)
                    (fgauto_same_action_coset G H hH A q0 F hr (fgauto_matched_hom S G a u) (fgauto_matched_hom S G a t) same))))
            (gen k)) in
    finite_surjection_target (Fin nR) C (fin_is_finite nR)
      (quotient_decidable_equality (G .carrier) R (fgauto_recognized_coset_decidable G H hH A q0 F hr)) f surj

def fgauto_recognizable_finite_index (S : Type) (hS : IsFinite S) (G : AbstractGroup) (a : S → G .carrier)
  (gen : FgautoGeneratesGroup S G a) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  (hr : FgautoRecognizable (fgauto_group_monoid G) (g ↦ H g .fst)) : FgautoGroupFiniteIndex G H hH
  ≔ let M ≔ fgauto_group_monoid G in
    mere_rec (Σ Nat (m ↦ Id Type S (Fin m))) (FgautoGroupFiniteIndex G H hH)
      (mere_isprop (Σ Nat (n ↦ Id Type (FgautoGroupCosets G H hH) (Fin n))))
      (sm ↦
        let en ≔ fgauto_finite_enumeration S (sm .fst) (id_to_equiv S (Fin (sm .fst)) (sm .snd)) in
        mere_rec (Σ (FgautoFiniteAction M) (A ↦ Σ (Fin (A .asize)) (q0 ↦ Σ (Fin (A .asize) → Bool) (F ↦
            FgautoRecognizes M A q0 F (g ↦ H g .fst)))))
          (FgautoGroupFiniteIndex G H hH) (mere_isprop (Σ Nat (n ↦ Id Type (FgautoGroupCosets G H hH) (Fin n))))
          (z ↦ fgauto_recognized_finite_index_at S G a gen (fgauto_signed_letters S (en .fst))
            (fgauto_signed_letters_complete S (en .fst) (en .snd)) H hH (z .fst) (z .snd .fst) (z .snd .snd .fst)
            (z .snd .snd .snd)) hr) hS

{` fggroups.tex:959. `}
def fgauto_recognizable_iff_finite_index (S : Type) (hS : IsFinite S) (G : AbstractGroup) (a : S → G .carrier)
  (gen : FgautoGeneratesGroup S G a) (H : Subtypes (G .carrier)) (hH : FgautoAbstractSubgroup G H)
  : FgautoIff (FgautoRecognizable (fgauto_group_monoid G) (g ↦ H g .fst)) (FgautoGroupFiniteIndex G H hH)
  ≔ (fgauto_recognizable_finite_index S hS G a gen H hH, fgauto_finite_index_recognizable G H hH)
