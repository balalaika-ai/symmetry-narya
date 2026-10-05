export "508-stabilizer-subgroups"
export "1115-howson"

{` thm:howson-neumann (fggroups.tex:855), the statement; see module 1115 for the
   decidability of orbits.  subgroup_intersection G H1 H2 is the orbit subgroup of
   (x1, x2) in X1 × X2 (module 508); howson_neumann: for F_S with S finite of
   cardinality k and subgroups of indices h1, h2, the intersection merely has an
   index c ≤ h1·h2 (c is unique, so Mere is harmless). `}

def gset_product (G : Group) (X1 X2 : GSet G) : GSet G
  ≔ z ↦ (Product (X1 z .fst) (X2 z .fst), product_set (X1 z .fst) (X2 z .fst) (X1 z .snd) (X2 z .snd))

def subgroup_intersection (G : Group) (H1 H2 : Subgroups G) : Subgroups G
  ≔ orbit_subgroup G (gset_product G (H1 .gset) (H2 .gset)) (H1 .point, H2 .point)

{` Enumerations of finite types. `}
def fin_list (N : Nat) : List (Fin N)
  ≔ match N [ zero. ↦ nil. | suc. n ↦ cons. (inr. star.) (fgauto_list_map (Fin n) (Fin (suc. n)) (j ↦ inl. j) (fin_list n)) ]

def fin_list_complete (N : Nat) (i : Fin N) : FgautoMem (Fin N) i (fin_list N)
  ≔ match N [
  | zero. ↦ match i []
  | suc. n ↦ match i [
    | inl. j ↦ inr. (fgauto_mem_map (Fin n) (Fin (suc. n)) (j' ↦ inl. j') j (fin_list n) (fin_list_complete n j))
    | inr. u ↦ inl. (match u [ star. ↦ refl (inr. star. : Fin (suc. n)) ]) ] ]

def equiv_list (A : Type) (N : Nat) (e : Equiv (Fin N) A) : List A ≔ fgauto_list_map (Fin N) A (e .map) (fin_list N)

def equiv_list_complete (A : Type) (N : Nat) (e : Equiv (Fin N) A) (a : A) : FgautoMem A a (equiv_list A N e)
  ≔ fgauto_mem_transport A (e .map (equiv_inverse_map (Fin N) A e a)) a (equiv_list A N e) (equiv_counit (Fin N) A e a)
      (fgauto_mem_map (Fin N) A (e .map) (equiv_inverse_map (Fin N) A e a) (fin_list N)
        (fin_list_complete N (equiv_inverse_map (Fin N) A e a)))

{` Decidable subsets of an N-element type have at most N elements. `}
def fin_decidable_subset_card_bound (N : Nat) (Q : Fin N → Type) (hQ : (i : Fin N) → isProp (Q i))
  (d : (i : Fin N) → Decidable (Q i)) : CardBound N (Σ (Fin N) Q)
  ≔ let D : Fin N → Bool ≔ i ↦ decision_bool (Q i) (d i) in
    (true_count N D, (bsix_true_count_le N D,
      mere (Id Type (Fin (true_count N D)) (Σ (Fin N) Q))
        (ua (Fin (true_count N D)) (Σ (Fin N) Q)
          (compose_equiv (Fin (true_count N D)) (BoolCarrier N D) (Σ (Fin N) Q)
            (canonical_inverse_equiv (BoolCarrier N D) (Fin (true_count N D)) (bool_carrier_fin N D))
            (family_equiv (Fin N) (i ↦ Id Bool (D i) true.) Q
              (i ↦ iff_equiv (Id Bool (D i) true.) (Q i) (bool_set (D i) true.) (hQ i)
                (decision_bool_reflect (Q i) (d i)) (decision_bool_true (Q i) (d i))))))))

def DecidableSubsetBound (N : Nat) (A : Type) : Type
  ≔ (Q : A → Type) → ((a : A) → isProp (Q a)) → ((a : A) → Decidable (Q a)) → CardBound N (Σ A Q)

def decidable_subset_card_bound (N : Nat) (A : Type) (p : Id Type A (Fin N)) : DecidableSubsetBound N A
  ≔ transport Type (DecidableSubsetBound N) (Fin N) A (inverse Type A (Fin N) p) (fin_decidable_subset_card_bound N)

{` thm:howson-neumann. `}
def howson_neumann (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (k : Nat) (hS : Mere (Id Type S (Fin k)))
  (H1 H2 : Subgroups (free_group S dec F)) (h1 h2 : Nat)
  (i1 : SubgroupHasIndex (free_group S dec F) H1 h1) (i2 : SubgroupHasIndex (free_group S dec F) H2 h2)
  : Mere (Σ Nat (c ↦ Product (Le c (mul h1 h2)) (SubgroupHasIndex (free_group S dec F) (subgroup_intersection (free_group S dec F) H1 H2) c)))
  ≔ let G ≔ free_group S dec F in
    let X ≔ gset_product G (H1 .gset) (H2 .gset) in
    let Y ≔ (z : F .carrier) ↦ X z .fst in
    let V ≔ Y (F .base) in
    let x0 : V ≔ (H1 .point, H2 .point) in
    let Goal ≔ Σ Nat (c ↦ Product (Le c (mul h1 h2)) (SubgroupHasIndex G (subgroup_intersection G H1 H2) c)) in
    mere_rec (Id Type S (Fin k)) (Mere Goal) (mere_isprop Goal) (pS ↦
    mere_rec (Id Type (H1 .gset (F .base) .fst) (Fin h1)) (Mere Goal) (mere_isprop Goal) (p1 ↦
    mere_rec (Id Type (H2 .gset (F .base) .fst) (Fin h2)) (Mere Goal) (mere_isprop Goal) (p2 ↦
      let pV : Id Type V (Fin (mul h1 h2))
        ≔ concat Type V (Product (Fin h1) (Fin h2)) (Fin (mul h1 h2))
            (refl Product p1 p2) (ua (Product (Fin h1) (Fin h2)) (Fin (mul h1 h2)) (fin_product_equiv h1 h2)) in
      let eV : Equiv (Fin (mul h1 h2)) V ≔ id_to_equiv (Fin (mul h1 h2)) V (inverse Type V (Fin (mul h1 h2)) pV) in
      let eS : Equiv (Fin k) S ≔ id_to_equiv (Fin k) S (inverse Type S (Fin k) pS) in
      let dV ≔ finite_decidable_equality V (mere (Σ Nat (m ↦ Id Type V (Fin m))) (mul h1 h2, pV)) in
      let Q ≔ (y : V) ↦ Mere (Id (Σ (F .carrier) Y) (F .base, x0) (F .base, y)) in
      let b ≔ decidable_subset_card_bound (mul h1 h2) V pV Q (y ↦ mere_isprop (Id (Σ (F .carrier) Y) (F .base, x0) (F .base, y)))
          (y ↦ schreier_orbit_decidable S F Y dV (equiv_list V (mul h1 h2) eV) (equiv_list_complete V (mul h1 h2) eV)
                 (equiv_list S k eS) (equiv_list_complete S k eS) x0 y) in
      mere Goal (b .fst, (b .snd .fst,
        gset_index_iff_shape G (subgroup_intersection G H1 H2 .gset) (b .fst) .snd
          (mere_rec (Id Type (Fin (b .fst)) (Σ V Q)) (Mere (Id Type (Σ V Q) (Fin (b .fst)))) (mere_isprop (Id Type (Σ V Q) (Fin (b .fst))))
            (q ↦ mere (Id Type (Σ V Q) (Fin (b .fst))) (inverse Type (Fin (b .fst)) (Σ V Q) q)) (b .snd .snd))))
    ) (i2 (F .base))) (i1 (F .base))) hS
