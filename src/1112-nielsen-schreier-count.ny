export "1111-nielsen-schreier"

{` thm:nielsen-schreier (fggroups.tex:800), second claim: if S is a finite set of
   cardinality n and the subgroup has index m, then T can be taken to be a finite
   set of cardinality m(n-1)+1.

   The cardinality is stated as c + m = m·n + 1 (NielsenSchreierBasisCount):
   with natural-number subtraction "m(n-1)+1" would be wrong for n = 0 (then
   m = 1 and T is empty, but 1·(0-1)+1 = 1 in N); for n ≥ 1 the two agree.

   Proof as in the book: the graph (V, E) has m·n edges (flat_total_equiv: n
   outgoing edges at each of the m vertices), the spanning tree has m - 1 of them
   (lem:spanning-tree), and T is the complement (tree_count_split). `}

{` (a) the graph has V × S edges. `}
def flat_out_contractible (S : Type) (F : FreeGroupSignature S) (X : F .carrier → Type) (x : X (F .base)) (s : S)
  : isContr (Σ (X (F .base)) (y ↦ Id X (F .loop s) x y))
  ≔ let t ≔ transport (F .carrier) X (F .base) (F .base) (F .loop s) x in
    hlevel_equiv zero. (Σ (X (F .base)) (y ↦ Id (X (F .base)) t y)) (Σ (X (F .base)) (y ↦ Id X (F .loop s) x y))
      (family_equiv (X (F .base)) (y ↦ Id (X (F .base)) t y) (y ↦ Id X (F .loop s) x y)
        (y ↦ canonical_inverse_equiv (Id X (F .loop s) x y) (Id (X (F .base)) t y)
          (pathover_transport_equiv (F .carrier) X (F .base) (F .base) (F .loop s) x y)))
      (iscontr_idfrom (X (F .base)) t)

def flat_total_equiv (S : Type) (F : FreeGroupSignature S) (X : F .carrier → Type)
  : Equiv (Σ (X (F .base)) (x ↦ Σ (X (F .base)) (y ↦ FreeFlatEdges S F X x y))) (Product (X (F .base)) S)
  ≔ let V ≔ X (F .base) in
    compose_equiv (Σ V (x ↦ Σ V (y ↦ FreeFlatEdges S F X x y)))
      (Σ V (x ↦ Σ S (s ↦ Σ V (y ↦ Id X (F .loop s) x y)))) (Product V S)
      (quasi_inverse_equiv (Σ V (x ↦ Σ V (y ↦ FreeFlatEdges S F X x y)))
        (Σ V (x ↦ Σ S (s ↦ Σ V (y ↦ Id X (F .loop s) x y))))
        (t ↦ (t .fst, (t .snd .snd .fst, (t .snd .fst, t .snd .snd .snd))))
        (t ↦ (t .fst, (t .snd .snd .fst, (t .snd .fst, t .snd .snd .snd))))
        (t ↦ refl t) (t ↦ refl t))
      (family_equiv V (x ↦ Σ S (s ↦ Σ V (y ↦ Id X (F .loop s) x y))) (_ ↦ S)
        (x ↦ contractible_fiber_projection S (s ↦ Σ V (y ↦ Id X (F .loop s) x y)) (s ↦ flat_out_contractible S F X x s)))

{` (b) all edges = tree edges ⊔ complement. `}
def tree_edges_total_equiv (V : Type) (E : V → V → Type) (T : SpanningTree V E)
  : Equiv (Σ V (x ↦ Σ V (y ↦ TreeEdges V E T x y))) (SubgraphEdgeTotal V E (T .fst))
  ≔ let H ≔ T .fst in
    let U ≔ H .vertices in
    let D ≔ subgraph_edges V E H in
    let hinv ≔ canonical_inverse_equiv U V (tree_equiv V E T) in
    let tinv ≔ tree_inv V E T in
    (u ↦ (tinv (u .fst), (tinv (u .snd .fst), u .snd .snd)),
     sigma_total_isequiv V (x ↦ Σ V (y ↦ D (tinv x) (tinv y))) U hinv (u ↦ Σ U (w ↦ D u w))
       (x ↦ (u' ↦ (tinv (u' .fst), u' .snd),
             sigma_total_isequiv V (y ↦ D (tinv x) (tinv y)) U hinv (w ↦ D (tinv x) w)
               (y ↦ identity_equiv (D (tinv x) (tinv y))))))

def tree_count_split (V : Type) (E : V → V → Type) (T : SpanningTree V E) (hdecE : DecidableSubgraphEdges V E (T .fst))
  : Equiv (Σ V (x ↦ Σ V (y ↦ E x y))) (Sum (SubgraphEdgeTotal V E (T .fst)) (ComplementTotal V E T))
  ≔ let E0 ≔ TreeEdges V E T in
    let E1 ≔ ComplementEdges V E T in
    compose_equiv (Σ V (x ↦ Σ V (y ↦ E x y))) (Σ V (x ↦ Σ V (y ↦ SumEdges V E0 E1 x y)))
      (Sum (SubgraphEdgeTotal V E (T .fst)) (ComplementTotal V E T))
      (family_equiv V (x ↦ Σ V (y ↦ E x y)) (x ↦ Σ V (y ↦ SumEdges V E0 E1 x y))
        (x ↦ family_equiv V (y ↦ E x y) (y ↦ SumEdges V E0 E1 x y) (y ↦ tree_edge_split V E T hdecE x y)))
      (compose_equiv (Σ V (x ↦ Σ V (y ↦ SumEdges V E0 E1 x y)))
        (Sum (Σ V (x ↦ Σ V (y ↦ E0 x y))) (ComplementTotal V E T))
        (Sum (SubgraphEdgeTotal V E (T .fst)) (ComplementTotal V E T))
        (sigma2_sum_distribute V E0 E1)
        (sum_equiv (Σ V (x ↦ Σ V (y ↦ E0 x y))) (ComplementTotal V E T) (SubgraphEdgeTotal V E (T .fst))
          (ComplementTotal V E T) (tree_edges_total_equiv V E T) (identity_equiv (ComplementTotal V E T))))

{` (c) the right summand of a finite sum is finite. `}
def IsRightSummand (A B : Type) (s : Sum A B) : Type ≔ match s [ inl. _ ↦ Empty | inr. _ ↦ Unit ]

def right_summand_to (A B : Type) (s : Sum A B) (p : IsRightSummand A B s) : B
  ≔ match s [ inl. _ ↦ match p [] | inr. b ↦ b ]

def right_summand_eta (A B : Type) (s : Sum A B) (p : IsRightSummand A B s)
  : Id (Σ (Sum A B) (IsRightSummand A B)) (inr. (right_summand_to A B s p), star.) (s, p)
  ≔ match s [
  | inl. _ ↦ match p []
  | inr. b ↦ match p [ star. ↦ refl ((inr. b, star.) : Σ (Sum A B) (IsRightSummand A B)) ] ]

def right_summand_equiv (A B : Type) : Equiv (Σ (Sum A B) (IsRightSummand A B)) B
  ≔ quasi_inverse_equiv (Σ (Sum A B) (IsRightSummand A B)) B
      (t ↦ right_summand_to A B (t .fst) (t .snd)) (b ↦ (inr. b, star.))
      (t ↦ right_summand_eta A B (t .fst) (t .snd)) (b ↦ refl b)

def right_summand_finite (A B : Type) (h : IsFinite (Sum A B)) : IsFinite B
  ≔ finite_of_equiv B (Σ (Sum A B) (IsRightSummand A B)) (canonical_inverse_equiv (Σ (Sum A B) (IsRightSummand A B)) B (right_summand_equiv A B))
      (finite_decidable_subset (Sum A B) h (IsRightSummand A B)
        (s ↦ match s [ inl. _ ↦ empty_prop | inr. _ ↦ unit_prop ])
        (s ↦ match s [ inl. _ ↦ inr. (z ↦ z) | inr. _ ↦ inl. star. ]))

{` ---------- The theorem ---------- `}

def NielsenSchreierBasisCount (S : Type) (F : FreeGroupSignature S) (X : F .carrier → SetTypes) (m n : Nat) : Type
  ≔ Σ Type (T ↦ Σ (DecidableEquality T) (dT ↦
      Product (Equiv (Σ (F .carrier) (z ↦ X z .fst)) (constructed_free_group_signature T dT .carrier))
        (Σ Nat (c ↦ Product (Mere (Id Type T (Fin c))) (Id Nat (add c m) (add (mul m n) (suc. zero.)))))))

def ns_count_arith (k c m n : Nat) (hk : Id Nat (suc. k) m) (h : Id Nat (add k c) (mul m n))
  : Id Nat (add c m) (add (mul m n) (suc. zero.))
  ≔ transport Nat (m' ↦ Id Nat (add k c) (mul m' n) → Id Nat (add c m') (add (mul m' n) (suc. zero.))) (suc. k) m hk
      (h' ↦ concat Nat (suc. (add c k)) (suc. (add k c)) (suc. (mul (suc. k) n))
        (refl ((z : Nat) ↦ (suc. z : Nat)) (add_comm c k)) (refl ((z : Nat) ↦ (suc. z : Nat)) h')) h

def nielsen_schreier_finite (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S)
  (X : GSet (free_group S dec F)) (ht : IsTransitive (free_group S dec F) X)
  (m : Nat) (hm : GSetHasIndex (free_group S dec F) X m) (n : Nat) (hS : Mere (Id Type S (Fin n)))
  : Mere (NielsenSchreierBasisCount S F X m n)
  ≔ let X' ≔ (z : F .carrier) ↦ X z .fst in
    let V ≔ X' (F .base) in
    let E ≔ FreeFlatEdges S F X' in
    let R ≔ free_flattening_signature S F X' in
    let hmV ≔ hm (F .base) in
    let decV ≔ finite_decidable_equality V (finite_of_card V m hmV) in
    let decE ≔ free_flat_edges_decidable S dec F X' (z ↦ X z .snd) in
    let hc ≔ transitive_connected_equiv (free_group S dec F) X .map ht in
    let Goal ≔ NielsenSchreierBasisCount S F X m n in
    mere_rec (SpanningTreeWithEdges V E m) (Mere Goal) (mere_isprop Goal)
      (r ↦
        let T ≔ r .fst in
        let hdecE ≔ r .snd .fst in
        let k ≔ r .snd .snd .fst in
        let hk ≔ r .snd .snd .snd .fst in
        let eD ≔ r .snd .snd .snd .snd in
        let Tc ≔ ComplementTotal V E T in
        let dTc ≔ complement_total_decidable V E T decV decE in
        let eq ≔ graph_quotient_equiv V E R (tree_complement_signature V E decV decE T hdecE) in
        mere_rec (Id Type V (Fin m)) (Mere Goal) (mere_isprop Goal) (pV ↦
          mere_rec (Id Type S (Fin n)) (Mere Goal) (mere_isprop Goal) (pS ↦
            let eAll : Equiv (Fin (mul m n)) (Sum (Fin k) Tc)
              ≔ compose_equiv (Fin (mul m n)) (Product (Fin m) (Fin n)) (Sum (Fin k) Tc)
                  (canonical_inverse_equiv (Product (Fin m) (Fin n)) (Fin (mul m n)) (fin_product_equiv m n))
                  (compose_equiv (Product (Fin m) (Fin n)) (Product V S) (Sum (Fin k) Tc)
                    (product_equiv (Fin m) (Fin n) V S
                      (canonical_inverse_equiv V (Fin m) (id_to_equiv V (Fin m) pV))
                      (canonical_inverse_equiv S (Fin n) (id_to_equiv S (Fin n) pS)))
                    (compose_equiv (Product V S) (Σ V (x ↦ Σ V (y ↦ E x y))) (Sum (Fin k) Tc)
                      (canonical_inverse_equiv (Σ V (x ↦ Σ V (y ↦ E x y))) (Product V S) (flat_total_equiv S F X'))
                      (compose_equiv (Σ V (x ↦ Σ V (y ↦ E x y))) (Sum (SubgraphEdgeTotal V E (T .fst)) Tc) (Sum (Fin k) Tc)
                        (tree_count_split V E T hdecE)
                        (sum_equiv (SubgraphEdgeTotal V E (T .fst)) Tc (Fin k) Tc eD (identity_equiv Tc))))) in
            let finTc ≔ right_summand_finite (Fin k) Tc
                (finite_of_equiv (Sum (Fin k) Tc) (Fin (mul m n))
                  (canonical_inverse_equiv (Fin (mul m n)) (Sum (Fin k) Tc) eAll) (fin_is_finite (mul m n))) in
            let c ≔ cardinality Tc finTc in
            mere_rec (Id Type Tc (Fin c)) (Mere Goal) (mere_isprop Goal) (pc ↦
              mere Goal (Tc, (dTc, (eq, (c, (cardinality_spec Tc finTc,
                ns_count_arith k c m n hk
                  (fin_equiv_cardinality (add k c) (mul m n)
                    (compose_equiv (Fin (add k c)) (Sum (Fin k) Tc) (Fin (mul m n))
                      (compose_equiv (Fin (add k c)) (Sum (Fin k) (Fin c)) (Sum (Fin k) Tc)
                        (canonical_inverse_equiv (Sum (Fin k) (Fin c)) (Fin (add k c)) (fin_sum_equiv k c))
                        (sum_equiv (Fin k) (Fin c) (Fin k) Tc (identity_equiv (Fin k))
                          (canonical_inverse_equiv Tc (Fin c) (id_to_equiv Tc (Fin c) pc))))
                      (canonical_inverse_equiv (Fin (mul m n)) (Sum (Fin k) Tc) eAll)))))))))
              (cardinality_spec Tc finTc))
            hS)
          hmV)
      (spanning_tree V E R hc m hmV decE)
