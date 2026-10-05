export "1030-subgroup-containment"
export "1024-subgroup-finiteness-lem"
export "973-abstract-subgroup-intersections"

{` Chapter 10, rem:noofsubgps (fingp.tex 35-40): "the number of
   subgroups" of a finite group. Constructively only decidable subgroups
   can be counted (module 1024: finiteness of all subgroups of finite groups
   is equivalent to excluded middle). This module identifies the decidable
   subgroups of an arbitrary group G with the Bool-valued abstract subgroups
   of abstr(G) (decidable_subgroups_closed_subsets_equiv, module 1041):

   - ClosedBoolSubsets 𝒢: functions A : 𝒢 → Bool whose truth family
     g ↦ (A g = true) is an abstract subgroup (IsAbstractSubgroup, module 973:
     contains the unit, closed under multiplication and inverses);
   - S ↦ the indicator of the stabilizer {g | g · pt = pt} of its point,
     which is decidable because S is (subgroup_fix_indicator);
   - A ↦ the subgroup (X_A, [refl]) with X_A(z) ≔ (sh_G = z)/~, where
     p ~ q iff A(p q⁻¹) = true (in concatenation order: first p, then q⁻¹);
     X_A is transitive (a quotient of the principal G-set), decidable (the
     relation is Bool-valued), and its point is fixed exactly by the g with
     A g = true (closed_subset_coset_fixes_iff). `}

{` Booleans of decidable types. `}
def decsub_bool (D : Type) (d : Decidable D) : Bool ≔ match d [ inl. _ ↦ true. | inr. _ ↦ false. ]

def decsub_bool_true (D : Type) (d : Decidable D) (x : D) : Id Bool (decsub_bool D d) true.
  ≔ match d [ inl. _ ↦ refl (true. : Bool) | inr. n ↦ absurd (Id Bool false. true.) (n x) ]

def decsub_bool_reflect (D : Type) (d : Decidable D) (t : Id Bool (decsub_bool D d) true.) : D
  ≔ match d [ inl. x ↦ x | inr. _ ↦ absurd D (bool_encode false. true. t) ]

def decsub_bool_unique (D : Type) (d : Decidable D) (b : Bool) (f : D → Id Bool b true.) (g : Id Bool b true. → D)
  : Id Bool (decsub_bool D d) b
  ≔ match d [
    | inl. x ↦ inverse Bool b true. (f x)
    | inr. n ↦ match b [
      | false. ↦ refl (false. : Bool)
      | true. ↦ absurd (Id Bool false. true.) (n (g (refl (true. : Bool)))) ] ]

{` Bool-valued abstract subgroups (closed decidable subsets). `}
def BoolSubgroupFamily (AG : AbstractGroup) (A : AG .carrier → Bool) : AG .carrier → Type
  ≔ g ↦ Id Bool (A g) true.

def ClosedBoolSubsets (AG : AbstractGroup) : Type
  ≔ Σ (AG .carrier → Bool) (A ↦ IsAbstractSubgroup AG (BoolSubgroupFamily AG A))

def is_abstract_subgroup_prop (AG : AbstractGroup) (P : AG .carrier → Type) : isProp (IsAbstractSubgroup AG P)
  ≔ let S ≔ AG .carrier in
    u v ↦
    let hP : (x : S) → isProp (P x) ≔ u .fst in
    (pi_prop S (x ↦ isProp (P x)) (x ↦ isprop_isprop (P x)) (u .fst) (v .fst),
     (hP (AG .unit) (u .snd .fst) (v .snd .fst),
      (pi_prop S (x ↦ (y : S) → P x → P y → P (AG .mul x y))
         (x ↦ pi_prop S (y ↦ P x → P y → P (AG .mul x y))
           (y ↦ pi_prop (P x) (_ ↦ P y → P (AG .mul x y))
             (_ ↦ pi_prop (P y) (_ ↦ P (AG .mul x y)) (_ ↦ hP (AG .mul x y)))))
         (u .snd .snd .fst) (v .snd .snd .fst),
       pi_prop S (x ↦ P x → P (AG .inv x))
         (x ↦ pi_prop (P x) (_ ↦ P (AG .inv x)) (_ ↦ hP (AG .inv x)))
         (u .snd .snd .snd) (v .snd .snd .snd))))

def closed_bool_subsets_prop (AG : AbstractGroup) (A : AG .carrier → Bool)
  : isProp (IsAbstractSubgroup AG (BoolSubgroupFamily AG A))
  ≔ is_abstract_subgroup_prop AG (BoolSubgroupFamily AG A)

def closed_bool_subsets_path (AG : AbstractGroup) (P Q : ClosedBoolSubsets AG)
  (h : (g : AG .carrier) → Id Bool (P .fst g) (Q .fst g)) : Id (ClosedBoolSubsets AG) P Q
  ≔ subtype_equal (AG .carrier → Bool) (A ↦ IsAbstractSubgroup AG (BoolSubgroupFamily AG A))
      (closed_bool_subsets_prop AG) P Q (funext (AG .carrier) (_ ↦ Bool) (P .fst) (Q .fst) h)

{` The type of decidable subgroups of G. `}
def DecidableSubgroups (G : Group) : Type ≔ Σ (Subgroups G) (IsDecidableSubgroup G)

def is_decidable_subgroup_prop (G : Group) (S : Subgroups G) : isProp (IsDecidableSubgroup G S)
  ≔ decidable_equality_prop (gset_underlying G (S .gset)) (gset_underlying_set G (S .gset))

{` Direction 1: the indicator of the stabilizer of the point. `}
def SubgroupPointFixed (G : Group) (S : Subgroups G) (g : USym G) : Type
  ≔ Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point)

def subgroup_fix_indicator (G : Group) (S : Subgroups G) (dS : IsDecidableSubgroup G S) (g : USym G) : Bool
  ≔ decsub_bool (SubgroupPointFixed G S g) (dS (gset_usym_act G (S .gset) g (S .point)) (S .point))

def subgroup_fix_indicator_true (G : Group) (S : Subgroups G) (dS : IsDecidableSubgroup G S) (g : USym G)
  (r : SubgroupPointFixed G S g) : Id Bool (subgroup_fix_indicator G S dS g) true.
  ≔ decsub_bool_true (SubgroupPointFixed G S g) (dS (gset_usym_act G (S .gset) g (S .point)) (S .point)) r

def subgroup_fix_indicator_reflect (G : Group) (S : Subgroups G) (dS : IsDecidableSubgroup G S) (g : USym G)
  (t : Id Bool (subgroup_fix_indicator G S dS g) true.) : SubgroupPointFixed G S g
  ≔ decsub_bool_reflect (SubgroupPointFixed G S g) (dS (gset_usym_act G (S .gset) g (S .point)) (S .point)) t

{` The stabilizer of a point of a G-set is an abstract subgroup. `}
def point_fixed_unit (G : Group) (S : Subgroups G) : SubgroupPointFixed G S (usym_unit G)
  ≔ gset_act_unit G (S .gset) (S .point)

def point_fixed_mul (G : Group) (S : Subgroups G) (g h : USym G) (rg : SubgroupPointFixed G S g)
  (rh : SubgroupPointFixed G S h) : SubgroupPointFixed G S (usym_mul G g h)
  ≔ let X ≔ S .gset in let Xu ≔ gset_underlying G X in let x ≔ S .point in
    concat Xu (gset_usym_act G X (usym_mul G g h) x) (gset_usym_act G X g (gset_usym_act G X h x)) x
      (gset_act_mul G X g h x)
      (concat Xu (gset_usym_act G X g (gset_usym_act G X h x)) (gset_usym_act G X g x) x
        (refl (gset_usym_act G X g) rh) rg)

def point_fixed_inv (G : Group) (S : Subgroups G) (g : USym G) (rg : SubgroupPointFixed G S g)
  : SubgroupPointFixed G S (usym_inv G g)
  ≔ let X ≔ S .gset in let Xu ≔ gset_underlying G X in let x ≔ S .point in
    concat Xu (gset_usym_act G X (usym_inv G g) x) (gset_usym_act G X (usym_inv G g) (gset_usym_act G X g x)) x
      (refl (gset_usym_act G X (usym_inv G g)) (inverse Xu (gset_usym_act G X g x) x rg))
      (gset_act_inv_left G X g x)

def subgroup_fix_indicator_closed (G : Group) (S : Subgroups G) (dS : IsDecidableSubgroup G S)
  : IsAbstractSubgroup (abstr G) (BoolSubgroupFamily (abstr G) (subgroup_fix_indicator G S dS))
  ≔ let A ≔ subgroup_fix_indicator G S dS in
    (g ↦ bool_set (A g) true.,
     (subgroup_fix_indicator_true G S dS (usym_unit G) (point_fixed_unit G S),
      (g h tg th ↦ subgroup_fix_indicator_true G S dS (usym_mul G g h)
         (point_fixed_mul G S g h (subgroup_fix_indicator_reflect G S dS g tg) (subgroup_fix_indicator_reflect G S dS h th)),
       g tg ↦ subgroup_fix_indicator_true G S dS (usym_inv G g)
         (point_fixed_inv G S g (subgroup_fix_indicator_reflect G S dS g tg)))))

def decidable_subgroup_closed_subset (G : Group) (u : DecidableSubgroups G) : ClosedBoolSubsets (abstr G)
  ≔ (subgroup_fix_indicator G (u .fst) (u .snd), subgroup_fix_indicator_closed G (u .fst) (u .snd))

{` Direction 2: the coset G-set of a closed subset. Membership along paths. `}
def closed_subset_member_path (G : Group) (P : ClosedBoolSubsets (abstr G)) (x y : USym G) (e : Id (USym G) x y)
  (h : Id Bool (P .fst x) true.) : Id Bool (P .fst y) true.
  ≔ transport (USym G) (g ↦ Id Bool (P .fst g) true.) x y e h

{` The loop p q⁻¹ at sh_G for p, q : sh_G = z. `}
def coset_loop (G : Group) (z : BG G .carrier) (p q : Id (BG G .carrier) (shape G) z) : USym G
  ≔ concat (BG G .carrier) (shape G) z (shape G) p (inverse (BG G .carrier) (shape G) z q)

def coset_loop_refl (G : Group) (z : BG G .carrier) (p : Id (BG G .carrier) (shape G) z)
  : Id (USym G) (usym_unit G) (coset_loop G z p p)
  ≔ inverse (USym G) (coset_loop G z p p) (usym_unit G) (concat_inverse_right (BG G .carrier) (shape G) z p)

def coset_loop_symm (G : Group) (z : BG G .carrier) (p q : Id (BG G .carrier) (shape G) z)
  : Id (USym G) (usym_inv G (coset_loop G z p q)) (coset_loop G z q p)
  ≔ let B ≔ BG G .carrier in let s ≔ shape G in
    concat (USym G) (usym_inv G (coset_loop G z p q))
      (concat B s z s (inverse B z s (inverse B s z q)) (inverse B s z p)) (coset_loop G z q p)
      (inverse_concat B s z s p (inverse B s z q))
      (refl ((r ↦ concat B s z s r (inverse B s z p)) : Id B s z → USym G) (inverse_inverse B s z q))

def coset_loop_trans (G : Group) (z : BG G .carrier) (p q r : Id (BG G .carrier) (shape G) z)
  : Id (USym G) (usym_mul G (coset_loop G z q r) (coset_loop G z p q)) (coset_loop G z p r)
  ≔ let B ≔ BG G .carrier in let s ≔ shape G in
    let qi ≔ inverse B s z q in let ri ≔ inverse B s z r in
    concat (USym G) (concat B s s s (coset_loop G z p q) (coset_loop G z q r))
      (concat B s z s p (concat B z s s qi (concat B s z s q ri))) (coset_loop G z p r)
      (concat_assoc B s z s s p qi (concat B s z s q ri))
      (refl (concat B s z s p) (concat_left_inverse B s z s q ri))

def closed_subset_coset_relation (G : Group) (P : ClosedBoolSubsets (abstr G)) (z : BG G .carrier)
  : EquivalenceRelation (Id (BG G .carrier) (shape G) z)
  ≔ let c ≔ P .snd in
    (p q ↦ (Id Bool (P .fst (coset_loop G z p q)) true., bool_set (P .fst (coset_loop G z p q)) true.),
     p ↦ closed_subset_member_path G P (usym_unit G) (coset_loop G z p p) (coset_loop_refl G z p) (c .snd .fst),
     p q h ↦ closed_subset_member_path G P (usym_inv G (coset_loop G z p q)) (coset_loop G z q p)
       (coset_loop_symm G z p q) (c .snd .snd .snd (coset_loop G z p q) h),
     p q r h k ↦ closed_subset_member_path G P (usym_mul G (coset_loop G z q r) (coset_loop G z p q))
       (coset_loop G z p r) (coset_loop_trans G z p q r)
       (c .snd .snd .fst (coset_loop G z q r) (coset_loop G z p q) k h))

def closed_subset_coset_gset (G : Group) (P : ClosedBoolSubsets (abstr G)) : GSet G
  ≔ z ↦ (Quotient (Id (BG G .carrier) (shape G) z) (closed_subset_coset_relation G P z),
         quotient_set (Id (BG G .carrier) (shape G) z) (closed_subset_coset_relation G P z))

def closed_subset_coset_class (G : Group) (P : ClosedBoolSubsets (abstr G))
  : GSetHom G (principal_gset G) (closed_subset_coset_gset G P)
  ≔ z p ↦ quotient_class (Id (BG G .carrier) (shape G) z) (closed_subset_coset_relation G P z) p

def closed_subset_coset_transitive (G : Group) (P : ClosedBoolSubsets (abstr G))
  : IsTransitive G (closed_subset_coset_gset G P)
  ≔ let X ≔ principal_gset G in
    let Y ≔ closed_subset_coset_gset G P in
    let q ≔ closed_subset_coset_class G P in
    let f : ActionType G X → ActionType G Y ≔ u ↦ (u .fst, q (u .fst) (u .snd)) in
    connected_action_type_transitive G Y
      (fingp_connected_surjection (ActionType G X) (ActionType G Y) f
        (transitive_action_type_connected G X (principal_gset_transitive G))
        (v ↦ mere_rec (BookFiber (Id (BG G .carrier) (shape G) (v .fst)) (Y (v .fst) .fst) (q (v .fst)) (v .snd))
          (Mere (BookFiber (ActionType G X) (ActionType G Y) f v))
          (mere_isprop (BookFiber (ActionType G X) (ActionType G Y) f v))
          (w ↦ mere (BookFiber (ActionType G X) (ActionType G Y) f v) ((v .fst, w .fst), (refl (v .fst), w .snd)))
          (quotient_surjective (Id (BG G .carrier) (shape G) (v .fst)) (closed_subset_coset_relation G P (v .fst))
            (v .snd))))

def closed_subset_subgroup (G : Group) (P : ClosedBoolSubsets (abstr G)) : Subgroups G
  ≔ (closed_subset_coset_gset G P, closed_subset_coset_class G P (shape G) (usym_unit G),
     closed_subset_coset_transitive G P)

def closed_subset_subgroup_decidable (G : Group) (P : ClosedBoolSubsets (abstr G))
  : IsDecidableSubgroup G (closed_subset_subgroup G P)
  ≔ quotient_decidable_equality (USym G) (closed_subset_coset_relation G P (shape G))
      (p q ↦ bool_true_decidable (P .fst (coset_loop G (shape G) p q)))

def closed_subset_decidable_subgroup (G : Group) (P : ClosedBoolSubsets (abstr G)) : DecidableSubgroups G
  ≔ (closed_subset_subgroup G P, closed_subset_subgroup_decidable G P)

{` The stabilizer of [refl] is P. First g · [refl] = [g · refl], and the
   loop (g · refl) refl⁻¹ = (refl g) refl⁻¹ is g. `}
def coset_loop_act_refl (G : Group) (g : USym G)
  : Id (USym G) (coset_loop G (shape G) (usym_mul G g (usym_unit G)) (usym_unit G)) g
  ≔ let B ≔ BG G .carrier in let s ≔ shape G in
    let rg ≔ concat B s s s (refl s) g in
    calc
      coset_loop G s rg (refl s)
      = concat B s s s rg (refl s) by refl (concat B s s s rg) (inverse_refl B s)
      = rg by concat_p1 B s s rg
      = g by concat_1p B s s g ∎

def closed_subset_coset_act_point (G : Group) (P : ClosedBoolSubsets (abstr G)) (g : USym G)
  : Id (gset_underlying G (closed_subset_coset_gset G P))
      (closed_subset_coset_class G P (shape G) (usym_mul G g (usym_unit G)))
      (gset_usym_act G (closed_subset_coset_gset G P) g (closed_subset_subgroup G P .point))
  ≔ gset_hom_equivariant G (principal_gset G) (closed_subset_coset_gset G P) (closed_subset_coset_class G P) g
      (usym_unit G)

def closed_subset_coset_fixes_member (G : Group) (P : ClosedBoolSubsets (abstr G)) (g : USym G)
  (r : SubgroupPointFixed G (closed_subset_subgroup G P) g) : Id Bool (P .fst g) true.
  ≔ let X ≔ closed_subset_coset_gset G P in
    let Xu ≔ gset_underlying G X in
    let R ≔ closed_subset_coset_relation G P (shape G) in
    let gp ≔ usym_mul G g (usym_unit G) in
    let pt ≔ closed_subset_subgroup G P .point in
    closed_subset_member_path G P (coset_loop G (shape G) gp (usym_unit G)) g (coset_loop_act_refl G g)
      (quotient_effective (USym G) R gp (usym_unit G) .map
        (concat Xu (quotient_class (USym G) R gp) (gset_usym_act G X g pt) pt
          (closed_subset_coset_act_point G P g) r))

def closed_subset_coset_member_fixes (G : Group) (P : ClosedBoolSubsets (abstr G)) (g : USym G)
  (h : Id Bool (P .fst g) true.) : SubgroupPointFixed G (closed_subset_subgroup G P) g
  ≔ let X ≔ closed_subset_coset_gset G P in
    let Xu ≔ gset_underlying G X in
    let R ≔ closed_subset_coset_relation G P (shape G) in
    let gp ≔ usym_mul G g (usym_unit G) in
    let pt ≔ closed_subset_subgroup G P .point in
    concat Xu (gset_usym_act G X g pt) (quotient_class (USym G) R gp) pt
      (inverse Xu (quotient_class (USym G) R gp) (gset_usym_act G X g pt) (closed_subset_coset_act_point G P g))
      (quotient_encode (USym G) R gp (usym_unit G)
        (closed_subset_member_path G P g (coset_loop G (shape G) gp (usym_unit G))
          (inverse (USym G) (coset_loop G (shape G) gp (usym_unit G)) g (coset_loop_act_refl G g)) h))

def closed_subset_coset_fixes_iff (G : Group) (P : ClosedBoolSubsets (abstr G)) (g : USym G)
  : Product (SubgroupPointFixed G (closed_subset_subgroup G P) g → Id Bool (P .fst g) true.)
      (Id Bool (P .fst g) true. → SubgroupPointFixed G (closed_subset_subgroup G P) g)
  ≔ (closed_subset_coset_fixes_member G P g, closed_subset_coset_member_fixes G P g)
