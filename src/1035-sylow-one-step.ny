export "1033-sylow-subgroups"
export "59-quotient-presentations"
export "1010-usym-powers"
export "1027-cyclic-groups-simple"

{` Chapter 10, thm:sylow1 (fingp.tex 229-260), the induction step. Let
   K = (X, x) be a finite subgroup of the finite group G and let
   W = W_G K = Aut(X) (subgroup_weyl_group, module 1031). The book takes a
   subgroup L of W of order p (Cauchy) and the preimage of L under
   N_G K → W_G K. Here the same subgroup is built directly as a G-set:
   for φ : W with φ^p = e and φ ≠ e (p = b + 1 prime), the powers of φ act
   on every X(z) (W acts on z ↦ X(z) by evaluation), and
   Y(z) ≔ X(z)/⟨φ⟩ is a transitive G-set (a family of quotient sets over
   BG) with point [x]. The action of W on X(z) is free (a G-set
   automorphism of a transitive G-set fixing a point is the identity), so
   every class has exactly p elements, |X(sh_G)| = |Y(sh_G)| · p, and the
   subgroup H = (Y, [x]) has |H| = p · |K| by lem:Lagrangeascounting. The
   quotient map X → Y shows K ⊆ H. In the book's terms Y = G/H and H is
   the preimage of ⟨φ⟩ ⊆ W_G K in N_G K. `}

{` W acts on X(z) for every z : BG: the W-set u ↦ u.1(z) on the component
   of X in the groupoid of G-sets. `}
def weyl_eval_gset (G : Group) (K : Subgroups G) (z : BG G .carrier) : GSet (subgroup_weyl_group G K)
  ≔ u ↦ u .fst z

def weyl_act (G : Group) (K : Subgroups G) (z : BG G .carrier) (w : USym (subgroup_weyl_group G K))
  (x : K .gset z .fst) : K .gset z .fst
  ≔ gset_usym_act (subgroup_weyl_group G K) (weyl_eval_gset G K z) w x

def weyl_act_eval (G : Group) (K : Subgroups G) (z : BG G .carrier) (w : USym (subgroup_weyl_group G K))
  (x : K .gset z .fst)
  : Id (K .gset z .fst) (weyl_act G K z w x) (gset_path_eval G (K .gset) (K .gset) z x (w .fst))
  ≔ refl (weyl_act G K z w x)

def weyl_usym_fst (G : Group) (K : Subgroups G) (w : USym (subgroup_weyl_group G K)) : Id (GSet G) (K .gset) (K .gset)
  ≔ w .fst

{` The action of W on X(z) is free: w · x = w' · x implies w = w'. `}
def weyl_act_injective (G : Group) (K : Subgroups G) (z : BG G .carrier) (x : K .gset z .fst)
  (w w' : USym (subgroup_weyl_group G K)) (e : Id (K .gset z .fst) (weyl_act G K z w x) (weyl_act G K z w' x))
  : Id (USym (subgroup_weyl_group G K)) w w'
  ≔ let X ≔ K .gset in
    let W ≔ subgroup_weyl_group G K in
    let A ≔ Id (GSet G) X X in
    let ev ≔ gset_path_eval G X X z x in
    let b ≔ ev (w' .fst) in
    let F ≔ BookFiber A (X z .fst) ev b in
    let q : Id A (weyl_usym_fst G K w) (weyl_usym_fst G K w')
      ≔ map_path F A (t ↦ t .fst) (w .fst, inverse (X z .fst) (ev (w .fst)) b e) (w' .fst, refl b)
          (gset_path_eval_injective G X X z x (K .transitive) b
            (w .fst, inverse (X z .fst) (ev (w .fst)) b e) (w' .fst, refl b)) in
    let E ≔ automorphism_group_usym_equiv (GSet G) (gset_groupoid G) X in
    calc
      w = equiv_inverse_map (USym W) A E (E .map w)
        by inverse (USym W) (equiv_inverse_map (USym W) A E (E .map w)) w (equiv_retraction (USym W) A E w)
      = equiv_inverse_map (USym W) A E (E .map w')
        by map_path A (USym W) (equiv_inverse_map (USym W) A E) (E .map w) (E .map w') q
      = w' by equiv_retraction (USym W) A E w' ∎

{` φ^m · (φ^n · x) = φ^(m+n) · x. `}
def weyl_act_power_add (G : Group) (K : Subgroups G) (z : BG G .carrier) (phi : USym (subgroup_weyl_group G K))
  (m n : Nat) (x : K .gset z .fst)
  : Id (K .gset z .fst) (weyl_act G K z (usym_power (subgroup_weyl_group G K) phi m)
        (weyl_act G K z (usym_power (subgroup_weyl_group G K) phi n) x))
      (weyl_act G K z (usym_power (subgroup_weyl_group G K) phi (add m n)) x)
  ≔ let W ≔ subgroup_weyl_group G K in
    let E ≔ weyl_eval_gset G K z in
    let Xz ≔ K .gset z .fst in
    concat Xz (weyl_act G K z (usym_power W phi m) (weyl_act G K z (usym_power W phi n) x))
      (weyl_act G K z (usym_mul W (usym_power W phi m) (usym_power W phi n)) x)
      (weyl_act G K z (usym_power W phi (add m n)) x)
      (inverse Xz (weyl_act G K z (usym_mul W (usym_power W phi m) (usym_power W phi n)) x)
        (weyl_act G K z (usym_power W phi m) (weyl_act G K z (usym_power W phi n) x))
        (gset_act_mul W E (usym_power W phi m) (usym_power W phi n) x))
      (map_path (USym W) Xz (w ↦ weyl_act G K z w x) (usym_mul W (usym_power W phi m) (usym_power W phi n))
        (usym_power W phi (add m n))
        (inverse (USym W) (usym_power W phi (add m n)) (usym_mul W (usym_power W phi m) (usym_power W phi n))
          (usym_power_add_left W phi m n)))

def weyl_act_unit_power (G : Group) (K : Subgroups G) (z : BG G .carrier) (phi : USym (subgroup_weyl_group G K))
  (x : K .gset z .fst) (k : Nat)
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi k) (usym_unit (subgroup_weyl_group G K)))
  : Id (K .gset z .fst) (weyl_act G K z (usym_power (subgroup_weyl_group G K) phi k) x) x
  ≔ let W ≔ subgroup_weyl_group G K in
    concat (K .gset z .fst) (weyl_act G K z (usym_power W phi k) x) (weyl_act G K z (usym_unit W) x) x
      (map_path (USym W) (K .gset z .fst) (w ↦ weyl_act G K z w x) (usym_power W phi k) (usym_unit W) h)
      (gset_act_unit W (weyl_eval_gset G K z) x)

{` The relation x ~ x' ⇔ ∃ k, x' = φ^k · x on X(z), for φ^(b+1) = e. `}
def WeylOrbitRel (G : Group) (K : Subgroups G) (phi : USym (subgroup_weyl_group G K)) (z : BG G .carrier)
  (x x' : K .gset z .fst) : Type
  ≔ Mere (Σ Nat (k ↦ Id (K .gset z .fst) x' (weyl_act G K z (usym_power (subgroup_weyl_group G K) phi k) x)))

def weyl_orbit_equivalence (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (z : BG G .carrier) : EquivalenceRelation (K .gset z .fst)
  ≔ let W ≔ subgroup_weyl_group G K in
    let Xz ≔ K .gset z .fst in
    let P : Xz → Xz → Type ≔ x x' ↦ Σ Nat (k ↦ Id Xz x' (weyl_act G K z (usym_power W phi k) x)) in
    (x x' ↦ (WeylOrbitRel G K phi z x x', mere_isprop (P x x')),
     x ↦ mere (P x x) (zero., inverse Xz (weyl_act G K z (usym_power W phi zero.) x) x
       (weyl_act_unit_power G K z phi x zero. (usym_power_zero W phi))),
     x x' r ↦ mere_rec (P x x') (Mere (P x' x)) (mere_isprop (P x' x))
       (w ↦ mere (P x' x) (mul (w .fst) b,
         calc
           x
           = weyl_act G K z (usym_power W phi (mul (w .fst) (suc. b))) x
             by inverse Xz (weyl_act G K z (usym_power W phi (mul (w .fst) (suc. b))) x) x
               (weyl_act_unit_power G K z phi x (mul (w .fst) (suc. b))
                 (usym_power_multiple_unit W phi (suc. b) h (w .fst)))
           = weyl_act G K z (usym_power W phi (mul (w .fst) b)) (weyl_act G K z (usym_power W phi (w .fst)) x)
             by inverse Xz (weyl_act G K z (usym_power W phi (mul (w .fst) b)) (weyl_act G K z (usym_power W phi (w .fst)) x))
               (weyl_act G K z (usym_power W phi (mul (w .fst) (suc. b))) x)
               (weyl_act_power_add G K z phi (mul (w .fst) b) (w .fst) x)
           = weyl_act G K z (usym_power W phi (mul (w .fst) b)) x'
             by map_path Xz Xz (weyl_act G K z (usym_power W phi (mul (w .fst) b)))
               (weyl_act G K z (usym_power W phi (w .fst)) x) x'
               (inverse Xz x' (weyl_act G K z (usym_power W phi (w .fst)) x) (w .snd)) ∎))
       r,
     x x' x'' r s ↦ mere_rec (P x x') (Mere (P x x'')) (mere_isprop (P x x''))
       (u ↦ mere_rec (P x' x'') (Mere (P x x'')) (mere_isprop (P x x''))
         (v ↦ mere (P x x'') (add (v .fst) (u .fst),
           calc
             x''
             = weyl_act G K z (usym_power W phi (v .fst)) x' by v .snd
             = weyl_act G K z (usym_power W phi (v .fst)) (weyl_act G K z (usym_power W phi (u .fst)) x)
               by map_path Xz Xz (weyl_act G K z (usym_power W phi (v .fst))) x'
                 (weyl_act G K z (usym_power W phi (u .fst)) x) (u .snd)
             = weyl_act G K z (usym_power W phi (add (v .fst) (u .fst))) x
               by weyl_act_power_add G K z phi (v .fst) (u .fst) x ∎))
         s)
       r)

{` The quotient G-set Y(z) = X(z)/⟨φ⟩ and the class map X → Y. `}
def weyl_quotient_gset (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K))) : GSet G
  ≔ z ↦ (Quotient (K .gset z .fst) (weyl_orbit_equivalence G K b phi h z),
      quotient_set (K .gset z .fst) (weyl_orbit_equivalence G K b phi h z))

def weyl_quotient_class (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  : GSetHom G (K .gset) (weyl_quotient_gset G K b phi h)
  ≔ z x ↦ quotient_class (K .gset z .fst) (weyl_orbit_equivalence G K b phi h z) x

def weyl_quotient_total (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (u : ActionType G (K .gset)) : ActionType G (weyl_quotient_gset G K b phi h)
  ≔ (u .fst, weyl_quotient_class G K b phi h (u .fst) (u .snd))

{` A surjection from a connected type has a connected codomain (as in module 1024). `}
def sylow_connected_surjection (A B : Type) (f : A → B) (hA : Connected A) (hf : Surjective A B f) : Connected B
  ≔ (mere_rec A (Mere B) (mere_isprop B) (a ↦ mere B (f a)) (hA .fst),
     x y ↦ mere_rec (BookFiber A B f x) (Mere (Id B x y)) (mere_isprop (Id B x y))
       (u ↦ mere_rec (BookFiber A B f y) (Mere (Id B x y)) (mere_isprop (Id B x y))
         (v ↦ mere_rec (Id A (u .fst) (v .fst)) (Mere (Id B x y)) (mere_isprop (Id B x y))
           (r ↦ mere (Id B x y) (concat B x (f (u .fst)) y (u .snd)
             (concat B (f (u .fst)) (f (v .fst)) y (refl f r) (inverse B y (f (v .fst)) (v .snd)))))
           (hA .snd (u .fst) (v .fst)))
         (hf y))
       (hf x))

def weyl_quotient_transitive (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  : IsTransitive G (weyl_quotient_gset G K b phi h)
  ≔ let Y ≔ weyl_quotient_gset G K b phi h in
    let T ≔ ActionType G (K .gset) in
    let TY ≔ ActionType G Y in
    connected_action_type_transitive G Y
      (sylow_connected_surjection T TY (weyl_quotient_total G K b phi h)
        (transitive_action_type_connected G (K .gset) (K .transitive))
        (v ↦ mere_rec (BookFiber (K .gset (v .fst) .fst) (Y (v .fst) .fst)
            (quotient_class (K .gset (v .fst) .fst) (weyl_orbit_equivalence G K b phi h (v .fst))) (v .snd))
          (Mere (BookFiber T TY (weyl_quotient_total G K b phi h) v))
          (mere_isprop (BookFiber T TY (weyl_quotient_total G K b phi h) v))
          (w ↦ mere (BookFiber T TY (weyl_quotient_total G K b phi h) v)
            ((v .fst, w .fst),
             action_type_path G Y (v .fst) (v .fst) (v .snd)
               (weyl_quotient_class G K b phi h (v .fst) (w .fst)) (refl (v .fst))
               (concat (Y (v .fst) .fst) (gset_act G Y (v .fst) (v .fst) (refl (v .fst)) (v .snd)) (v .snd)
                 (weyl_quotient_class G K b phi h (v .fst) (w .fst))
                 (gset_act_refl G Y (v .fst) (v .snd)) (w .snd))))
          (quotient_surjective (K .gset (v .fst) .fst) (weyl_orbit_equivalence G K b phi h (v .fst)) (v .snd))))

{` The subgroup H = (Y, [x]); K ⊆ H. `}
def weyl_quotient_subgroup (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K))) : Subgroups G
  ≔ (weyl_quotient_gset G K b phi h, weyl_quotient_class G K b phi h (shape G) (K .point),
     weyl_quotient_transitive G K b phi h)

def weyl_quotient_subgroup_le (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  : SubgroupLe G K (weyl_quotient_subgroup G K b phi h)
  ≔ gset_hom_subgroup_fixes G K (weyl_quotient_gset G K b phi h)
      (weyl_quotient_class G K b phi h (shape G) (K .point)) (weyl_quotient_class G K b phi h)
      (refl (weyl_quotient_class G K b phi h (shape G) (K .point)))

{` Finiteness of Y(sh_G): the relation is decidable (k may be taken < b+1). `}
{` φ^k · x = φ^r · x for k = q·(b+1) + r. `}
def weyl_act_reduce (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (z : BG G .carrier) (x : K .gset z .fst) (k : Nat)
  : Σ (Remainder (suc. b)) (r ↦ Id (K .gset z .fst)
      (weyl_act G K z (usym_power (subgroup_weyl_group G K) phi k) x)
      (weyl_act G K z (usym_power (subgroup_weyl_group G K) phi (r .fst)) x))
  ≔ let W ≔ subgroup_weyl_group G K in
    let d ≔ euclidean_division k (suc. b) (nat_positive_book b) in
    let q ≔ d .fst .fst in
    let r ≔ d .fst .snd in
    ((r, d .snd .fst),
     map_path (USym W) (K .gset z .fst) (w ↦ weyl_act G K z w x) (usym_power W phi k) (usym_power W phi r)
       (concat (USym W) (usym_power W phi k) (usym_power W phi (add (mul q (suc. b)) r)) (usym_power W phi r)
         (map_path Nat (USym W) (usym_power W phi) k (add (mul q (suc. b)) r) (d .snd .snd))
         (usym_power_period_left W phi (suc. b) h q r)))

def weyl_orbit_decidable (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (z : BG G .carrier) (dX : DecidableEquality (K .gset z .fst))
  : DecidableRelation (K .gset z .fst) (weyl_orbit_equivalence G K b phi h z)
  ≔ x x' ↦
    let W ≔ subgroup_weyl_group G K in
    let Xz ≔ K .gset z .fst in
    let Q : Remainder (suc. b) → Type ≔ r ↦ Id Xz x' (weyl_act G K z (usym_power W phi (r .fst)) x) in
    let P ≔ Σ Nat (k ↦ Id Xz x' (weyl_act G K z (usym_power W phi k) x)) in
    match finite_quantifiers (Remainder (suc. b)) (fingp_remainder_finite (suc. b)) Q
      (r ↦ hedberg Xz dX x' (weyl_act G K z (usym_power W phi (r .fst)) x) .fst)
      (r ↦ dX x' (weyl_act G K z (usym_power W phi (r .fst)) x)) .snd [
    | inl. m ↦ inl. (mere_rec (Σ (Remainder (suc. b)) Q) (Mere P) (mere_isprop P)
        (w ↦ mere P (w .fst .fst, w .snd)) m)
    | inr. no ↦ inr. (m ↦ mere_rec P Empty empty_prop
        (w ↦ let red ≔ weyl_act_reduce G K b phi h z x (w .fst) in
          no (mere (Σ (Remainder (suc. b)) Q) (red .fst,
            concat Xz x' (weyl_act G K z (usym_power W phi (w .fst)) x)
              (weyl_act G K z (usym_power W phi (red .fst .fst)) x) (w .snd) (red .snd))))
        m) ]

{` Each class has exactly b+1 elements. `}
def weyl_class_point (G : Group) (K : Subgroups G) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (x : gset_underlying G (K .gset)) (r : Remainder (suc. b))
  : BookFiber (gset_underlying G (K .gset)) (gset_underlying G (weyl_quotient_gset G K b phi h))
      (weyl_quotient_class G K b phi h (shape G)) (weyl_quotient_class G K b phi h (shape G) x)
  ≔ let W ≔ subgroup_weyl_group G K in
    let Xs ≔ gset_underlying G (K .gset) in
    let R ≔ weyl_orbit_equivalence G K b phi h (shape G) in
    let x' ≔ weyl_act G K (shape G) (usym_power W phi (r .fst)) x in
    (x', equiv_inverse_map (Id (Quotient Xs R) (quotient_class Xs R x) (quotient_class Xs R x')) (Rel Xs R x x')
      (quotient_effective Xs R x x')
      (mere (Σ Nat (k ↦ Id Xs x' (weyl_act G K (shape G) (usym_power W phi k) x))) (r .fst, refl x')))

def weyl_class_equiv (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (K : Subgroups G)
  (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (ne : Id (USym (subgroup_weyl_group G K)) phi (usym_unit (subgroup_weyl_group G K)) → Empty)
  (x : gset_underlying G (K .gset))
  : Equiv (Remainder (suc. b))
      (BookFiber (gset_underlying G (K .gset)) (gset_underlying G (weyl_quotient_gset G K b phi h))
        (weyl_quotient_class G K b phi h (shape G)) (weyl_quotient_class G K b phi h (shape G) x))
  ≔ let W ≔ subgroup_weyl_group G K in
    let Xs ≔ gset_underlying G (K .gset) in
    let Ys ≔ gset_underlying G (weyl_quotient_gset G K b phi h) in
    let R ≔ weyl_orbit_equivalence G K b phi h (shape G) in
    let cl ≔ weyl_quotient_class G K b phi h (shape G) in
    let Fb ≔ BookFiber Xs Ys cl (cl x) in
    let f ≔ weyl_class_point G K b phi h x in
    let hF : isSet Fb
      ≔ sigma_set Xs (x' ↦ Id Ys (cl x) (cl x')) (gset_underlying_set G (K .gset))
          (x' ↦ prop_is_set (Id Ys (cl x) (cl x')) (quotient_set Xs R (cl x) (cl x'))) in
    let hyp ≔ prime_order_powers_nontrivial (suc. b) hp W phi h ne in
    set_bijection_equiv (Remainder (suc. b)) Fb hF f
      (r r' e ↦ subtype_equal Nat (k ↦ BookLt k (suc. b)) (k ↦ book_lt_prop k (suc. b)) r r'
        (usym_power_injective_below W phi (suc. b) hyp (r .fst) (r' .fst) (r .snd) (r' .snd)
          (weyl_act_injective G K (shape G) x (usym_power W phi (r .fst)) (usym_power W phi (r' .fst))
            (map_path Fb Xs (t ↦ t .fst) (f r) (f r') e))))
      (t ↦ mere_rec (Σ Nat (k ↦ Id Xs (t .fst) (weyl_act G K (shape G) (usym_power W phi k) x)))
        (Mere (BookFiber (Remainder (suc. b)) Fb f t)) (mere_isprop (BookFiber (Remainder (suc. b)) Fb f t))
        (w ↦ let red ≔ weyl_act_reduce G K b phi h (shape G) x (w .fst) in
          mere (BookFiber (Remainder (suc. b)) Fb f t) (red .fst,
            subtype_equal Xs (x' ↦ Id Ys (cl x) (cl x')) (x' ↦ quotient_set Xs R (cl x) (cl x')) t (f (red .fst))
              (concat Xs (t .fst) (weyl_act G K (shape G) (usym_power W phi (w .fst)) x)
                (weyl_act G K (shape G) (usym_power W phi (red .fst .fst)) x) (w .snd) (red .snd))))
        (quotient_effective Xs R x (t .fst) .map (t .snd)))

{` |X(sh_G)| = |Y(sh_G)| · (b+1). `}
def weyl_quotient_finite (G : Group) (hG : IsFiniteGroup G) (K : Subgroups G) (hK : IsFiniteGroup (subgroup_group G K))
  (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  : IsFiniteGSet G (weyl_quotient_gset G K b phi h)
  ≔ finite_quotient (gset_underlying G (K .gset)) (subgroup_gset_finite G hG K hK)
      (weyl_orbit_equivalence G K b phi h (shape G))
      (weyl_orbit_decidable G K b phi h (shape G) (subgroup_gset_decidable_equality G hG K hK))

def weyl_quotient_card (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G) (K : Subgroups G)
  (hK : IsFiniteGroup (subgroup_group G K)) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (ne : Id (USym (subgroup_weyl_group G K)) phi (usym_unit (subgroup_weyl_group G K)) → Empty)
  : Id Nat (gset_card G (K .gset) (subgroup_gset_finite G hG K hK))
      (mul (gset_card G (weyl_quotient_gset G K b phi h) (weyl_quotient_finite G hG K hK b phi h)) (suc. b))
  ≔ let Xs ≔ gset_underlying G (K .gset) in
    let hX ≔ subgroup_gset_finite G hG K hK in
    let Ys ≔ gset_underlying G (weyl_quotient_gset G K b phi h) in
    let hY ≔ weyl_quotient_finite G hG K hK b phi h in
    let cl ≔ weyl_quotient_class G K b phi h (shape G) in
    let R ≔ weyl_orbit_equivalence G K b phi h (shape G) in
    let F : Ys → Type ≔ c ↦ BookFiber Xs Ys cl c in
    let dY ≔ finite_decidable_equality Ys hY in
    let hF : (c : Ys) → IsFinite (F c)
      ≔ c ↦ finite_decidable_subset Xs hX (x' ↦ Id Ys c (cl x')) (x' ↦ quotient_set Xs R c (cl x'))
          (x' ↦ dY c (cl x')) in
    let E ≔ sum_of_fibers_equiv Xs Ys cl in
    let hT ≔ finite_of_equiv (Σ Ys F) Xs E hX in
    let Goal : Ys → Type ≔ c ↦ Id Nat (cardinality (F c) (hF c)) (suc. b) in
    concat Nat (gset_card G (K .gset) hX) (cardinality (Σ Ys F) hT) (mul (gset_card G (weyl_quotient_gset G K b phi h) hY) (suc. b))
      (cardinality_equiv Xs (Σ Ys F) (canonical_inverse_equiv (Σ Ys F) Xs E) hX hT)
      (cardinality_sigma_constant Ys hY F hF hT (suc. b)
        (c ↦ mere_rec (BookFiber Xs Ys cl c) (Goal c) (nat_set (cardinality (F c) (hF c)) (suc. b))
          (w ↦ transport Ys Goal (cl (w .fst)) c (inverse Ys c (cl (w .fst)) (w .snd))
            (concat Nat (cardinality (F (cl (w .fst))) (hF (cl (w .fst))))
              (cardinality (Remainder (suc. b)) (fingp_remainder_finite (suc. b))) (suc. b)
              (inverse Nat (cardinality (Remainder (suc. b)) (fingp_remainder_finite (suc. b)))
                (cardinality (F (cl (w .fst))) (hF (cl (w .fst))))
                (cardinality_equiv (Remainder (suc. b)) (F (cl (w .fst))) (weyl_class_equiv b hp G K phi h ne (w .fst))
                  (fingp_remainder_finite (suc. b)) (hF (cl (w .fst)))))
              (fingp_remainder_card (suc. b))))
          (quotient_surjective Xs R c)))

{` The induction step of thm:sylow1: H = (Y, [x]) is finite with
   |H| = (b+1) · |K|, and K ⊆ H. `}
def weyl_quotient_subgroup_finite (G : Group) (hG : IsFiniteGroup G) (K : Subgroups G)
  (hK : IsFiniteGroup (subgroup_group G K)) (b : Nat) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  : IsFiniteGroup (subgroup_group G (weyl_quotient_subgroup G K b phi h))
  ≔ subgroup_group_finite G hG (weyl_quotient_subgroup G K b phi h)
      (finite_decidable_equality (gset_underlying G (weyl_quotient_gset G K b phi h)) (weyl_quotient_finite G hG K hK b phi h))

def weyl_quotient_subgroup_card (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (K : Subgroups G) (hK : IsFiniteGroup (subgroup_group G K)) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (ne : Id (USym (subgroup_weyl_group G K)) phi (usym_unit (subgroup_weyl_group G K)) → Empty)
  : Id Nat (group_card (subgroup_group G (weyl_quotient_subgroup G K b phi h)) (weyl_quotient_subgroup_finite G hG K hK b phi h))
      (mul (suc. b) (group_card (subgroup_group G K) hK))
  ≔ let H ≔ weyl_quotient_subgroup G K b phi h in
    let hH ≔ weyl_quotient_subgroup_finite G hG K hK b phi h in
    let hY ≔ subgroup_gset_finite G hG H hH in
    let y ≔ gset_card G (H .gset) hY in
    let y' ≔ gset_card G (H .gset) (weyl_quotient_finite G hG K hK b phi h) in
    let x ≔ gset_card G (K .gset) (subgroup_gset_finite G hG K hK) in
    let p : Nat ≔ suc. b in
    let k ≔ group_card (subgroup_group G K) hK in
    let yy : Id Nat y y' ≔ fingp_card_irrel (gset_underlying G (H .gset)) hY (weyl_quotient_finite G hG K hK b phi h) in
    fingp_mul_cancel_left y (group_card (subgroup_group G H) hH) (mul p k)
      (finite_inhabited_card_positive (gset_underlying G (H .gset)) hY (H .point))
      (calc
        mul y (group_card (subgroup_group G H) hH)
        = group_card G hG by inverse Nat (group_card G hG) (mul y (group_card (subgroup_group G H) hH)) (lagrange_counting G hG H hH)
        = mul x k by lagrange_counting G hG K hK
        = mul (mul y' p) k by map_path Nat Nat (n ↦ mul n k) x (mul y' p) (weyl_quotient_card b hp G hG K hK phi h ne)
        = mul (mul y p) k by map_path Nat Nat (n ↦ mul (mul n p) k) y' y (inverse Nat y y' yy)
        = mul y (mul p k) by mul_assoc y p k ∎)

{` The step packaged abstractly (later modules use only this form). `}
def WeylStepResult (b : Nat) (G : Group) (K : Subgroups G) (hK : IsFiniteGroup (subgroup_group G K)) : Type
  ≔ Σ (Subgroups G) (H ↦ Σ (IsFiniteGroup (subgroup_group G H))
      (hH ↦ Product (Id Nat (group_card (subgroup_group G H) hH) (mul (suc. b) (group_card (subgroup_group G K) hK))) (SubgroupLe G K H)))

def weyl_quotient_step (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (K : Subgroups G) (hK : IsFiniteGroup (subgroup_group G K)) (phi : USym (subgroup_weyl_group G K))
  (h : Id (USym (subgroup_weyl_group G K)) (usym_power (subgroup_weyl_group G K) phi (suc. b))
    (usym_unit (subgroup_weyl_group G K)))
  (ne : Id (USym (subgroup_weyl_group G K)) phi (usym_unit (subgroup_weyl_group G K)) → Empty)
  : WeylStepResult b G K hK
  ≔ (weyl_quotient_subgroup G K b phi h, (weyl_quotient_subgroup_finite G hG K hK b phi h,
      (weyl_quotient_subgroup_card b hp G hG K hK phi h ne, weyl_quotient_subgroup_le G K b phi h)))
