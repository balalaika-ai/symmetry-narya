export "1021-lagrange-counting"
export "412-symmetric-group-two"
export "70-classical-principles"

{` Chapter 10, lem:Lagrangeascounting (fingp.tex 69-85), the claim in the
   proof that "G/H and H are finite" for every subgroup H of a finite group
   G. Constructively this claim is equivalent to the law of excluded middle
   (for propositions): for a proposition P, the subgroup H_P of Σ_2 whose
   G-set is z ↦ z/~_P (s ~_P t ⇔ s = t ∨ P) has G/H_P = Fin 2/~_P, which is
   finite exactly when P is decidable. Conversely, under excluded middle
   every subgroup is decidable, hence finite (module 1020). This is why
   lem:Lagrangeascounting assumes that H is finite. `}

def SubgroupsOfFiniteGroupsFinite : Type
  ≔ (G : Group) → IsFiniteGroup G → (S : Subgroups G) → IsFiniteGroup (subgroup_group G S)

{` The relation s ~_P t ⇔ ‖(s = t) + P‖ on a set. `}
def lem_collapse_relation (S : SetTypes) (P : Type) : EquivalenceRelation (S .fst)
  ≔ (s t ↦ (Mere (Sum (Id (S .fst) s t) P), mere_isprop (Sum (Id (S .fst) s t) P)),
     s ↦ mere (Sum (Id (S .fst) s s) P) (inl. (refl s)),
     s t r ↦ mere_rec (Sum (Id (S .fst) s t) P) (Mere (Sum (Id (S .fst) t s) P)) (mere_isprop (Sum (Id (S .fst) t s) P))
       (u ↦ mere (Sum (Id (S .fst) t s) P) (match u [ inl. e ↦ inl. (inverse (S .fst) s t e) | inr. p ↦ inr. p ])) r,
     s t w r q ↦ mere_rec (Sum (Id (S .fst) s t) P) (Mere (Sum (Id (S .fst) s w) P)) (mere_isprop (Sum (Id (S .fst) s w) P))
       (u ↦ mere_rec (Sum (Id (S .fst) t w) P) (Mere (Sum (Id (S .fst) s w) P)) (mere_isprop (Sum (Id (S .fst) s w) P))
         (v ↦ mere (Sum (Id (S .fst) s w) P) (match u [
           | inr. p ↦ inr. p
           | inl. e ↦ match v [ inl. e' ↦ inl. (concat (S .fst) s t w e e') | inr. p ↦ inr. p ] ])) q) r)

def lem_collapse_gset (P : Type) : GSet (symmetric_group two)
  ≔ z ↦ (Quotient (z .fst .fst) (lem_collapse_relation (z .fst) P),
         quotient_set (z .fst .fst) (lem_collapse_relation (z .fst) P))

def lem_collapse_class (P : Type) : GSetHom (symmetric_group two) (standard_symmetric_gset two) (lem_collapse_gset P)
  ≔ z s ↦ quotient_class (z .fst .fst) (lem_collapse_relation (z .fst) P) s

{` The standard Σ_2-set Fin 2 is transitive (the swap moves 1 to 0). `}
def sigma2_standard_transitive : IsTransitive (symmetric_group two) (standard_symmetric_gset two)
  ≔ let G ≔ symmetric_group two in
    let X ≔ standard_symmetric_gset two in
    let sw ≔ permutation_symmetry (standard_set two) fin2_swap_equiv in
    mere (Σ (Fin two) (x ↦ (y : Fin two) → Mere (Σ (USym G) (g ↦ Id (Fin two) x (gset_usym_act G X g y)))))
      (fin2_zero, y ↦ match y [
        | inr. u ↦ mere (Σ (USym G) (g ↦ Id (Fin two) fin2_zero (gset_usym_act G X g (inr. u))))
            (usym_unit G, concat (Fin two) fin2_zero (inr. u) (gset_usym_act G X (usym_unit G) (inr. u))
              (inr. (unit_prop star. u)) (inverse (Fin two) (gset_usym_act G X (usym_unit G) (inr. u)) (inr. u)
                (gset_act_unit G X (inr. u))))
        | inl. (inr. u) ↦ mere (Σ (USym G) (g ↦ Id (Fin two) fin2_zero (gset_usym_act G X g (inl. (inr. u)))))
            (sw, inr. (unit_prop star. u))
        | inl. (inl. e) ↦ match e [] ])

{` A surjection from a connected type has a connected codomain. `}
def fingp_connected_surjection (A B : Type) (f : A → B) (hA : Connected A) (hf : Surjective A B f) : Connected B
  ≔ (mere_rec A (Mere B) (mere_isprop B) (a ↦ mere B (f a)) (hA .fst),
     x y ↦ mere_rec (BookFiber A B f x) (Mere (Id B x y)) (mere_isprop (Id B x y))
       (u ↦ mere_rec (BookFiber A B f y) (Mere (Id B x y)) (mere_isprop (Id B x y))
         (v ↦ mere_rec (Id A (u .fst) (v .fst)) (Mere (Id B x y)) (mere_isprop (Id B x y))
           (r ↦ mere (Id B x y) (concat B x (f (u .fst)) y (u .snd)
             (concat B (f (u .fst)) (f (v .fst)) y (refl f r) (inverse B y (f (v .fst)) (v .snd)))))
           (hA .snd (u .fst) (v .fst)))
         (hf y))
       (hf x))

def lem_collapse_transitive (P : Type) : IsTransitive (symmetric_group two) (lem_collapse_gset P)
  ≔ let G ≔ symmetric_group two in
    let X ≔ standard_symmetric_gset two in
    let Y ≔ lem_collapse_gset P in
    let q ≔ lem_collapse_class P in
    let f : ActionType G X → ActionType G Y ≔ u ↦ (u .fst, q (u .fst) (u .snd)) in
    connected_action_type_transitive G Y
      (fingp_connected_surjection (ActionType G X) (ActionType G Y) f
        (transitive_action_type_connected G X sigma2_standard_transitive)
        (v ↦ mere_rec (BookFiber (v .fst .fst .fst) (Y (v .fst) .fst) (q (v .fst)) (v .snd))
          (Mere (BookFiber (ActionType G X) (ActionType G Y) f v))
          (mere_isprop (BookFiber (ActionType G X) (ActionType G Y) f v))
          (w ↦ mere (BookFiber (ActionType G X) (ActionType G Y) f v)
            ((v .fst, w .fst), (refl (v .fst), w .snd)))
          (quotient_surjective (v .fst .fst .fst) (lem_collapse_relation (v .fst .fst) P) (v .snd))))

def lem_collapse_subgroup (P : Type) : Subgroups (symmetric_group two)
  ≔ (lem_collapse_gset P, lem_collapse_class P (shape (symmetric_group two)) fin2_zero, lem_collapse_transitive P)

{` In G/H_P = Fin 2/~_P, the classes of 1 and 0 agree exactly when P holds. `}
def lem_collapse_classes_path (P : Type) (hP : isProp P)
  (e : Id (gset_underlying (symmetric_group two) (lem_collapse_gset P))
    (lem_collapse_class P (shape (symmetric_group two)) fin2_one)
    (lem_collapse_class P (shape (symmetric_group two)) fin2_zero)) : P
  ≔ let R ≔ lem_collapse_relation (standard_set two) P in
    mere_rec (Sum (Id (Fin two) fin2_one fin2_zero) P) P hP
      (u ↦ match u [
        | inl. r ↦ absurd P (fin2_zero_ne_one (inverse (Fin two) fin2_one fin2_zero r))
        | inr. p ↦ p ])
      (quotient_effective (Fin two) R fin2_one fin2_zero .map e)

def lem_collapse_classes_of_prop (P : Type) (p : P)
  : Id (gset_underlying (symmetric_group two) (lem_collapse_gset P))
      (lem_collapse_class P (shape (symmetric_group two)) fin2_one)
      (lem_collapse_class P (shape (symmetric_group two)) fin2_zero)
  ≔ quotient_encode (Fin two) (lem_collapse_relation (standard_set two) P) fin2_one fin2_zero
      (mere (Sum (Id (Fin two) fin2_one fin2_zero) P) (inr. p))

{` "Every subgroup of a finite group is finite" implies excluded middle. `}
def subgroups_finite_excluded_middle (all : SubgroupsOfFiniteGroupsFinite) : ExcludedMiddle
  ≔ P hP ↦
    let G ≔ symmetric_group two in
    let S ≔ lem_collapse_subgroup P in
    let c ≔ lem_collapse_class P (shape G) in
    match subgroup_gset_decidable_equality G (symmetric_group_finite two) S
      (all G (symmetric_group_finite two) S) (c fin2_one) (c fin2_zero) [
    | inl. e ↦ inl. (lem_collapse_classes_path P hP e)
    | inr. ne ↦ inr. (p ↦ ne (lem_collapse_classes_of_prop P p)) ]

{` Conversely, under excluded middle every subgroup is decidable, hence finite. `}
def excluded_middle_subgroups_finite (lem : ExcludedMiddle) : SubgroupsOfFiniteGroupsFinite
  ≔ G hG S ↦ subgroup_group_finite G hG S
      (x y ↦ lem (Id (gset_underlying G (S .gset)) x y) (gset_underlying_set G (S .gset) x y))

def subgroups_finite_iff_excluded_middle
  : Product (SubgroupsOfFiniteGroupsFinite → ExcludedMiddle) (ExcludedMiddle → SubgroupsOfFiniteGroupsFinite)
  ≔ (subgroups_finite_excluded_middle, excluded_middle_subgroups_finite)

{` Litmus: for P = Empty the collapsed set keeps 0 and 1 apart; for
   P = Unit they are identified. `}
def lem_collapse_empty_separates
  : Not (Id (gset_underlying (symmetric_group two) (lem_collapse_gset Empty))
      (lem_collapse_class Empty (shape (symmetric_group two)) fin2_one)
      (lem_collapse_class Empty (shape (symmetric_group two)) fin2_zero))
  ≔ e ↦ lem_collapse_classes_path Empty empty_prop e

def lem_collapse_unit_identifies
  : Id (gset_underlying (symmetric_group two) (lem_collapse_gset Unit))
      (lem_collapse_class Unit (shape (symmetric_group two)) fin2_one)
      (lem_collapse_class Unit (shape (symmetric_group two)) fin2_zero)
  ≔ lem_collapse_classes_of_prop Unit star.
