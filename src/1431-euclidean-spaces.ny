export "1430-orthogonal-group"
export "707-abstract-torsors"

{` Chapter 14, section "Euclidean spaces" (geometry.tex 73-166).

   def:EuclideanSpace: a Euclidean space is an inner product space V with a
   torsor A for the additive group underlying V (abstract torsors,
   def:abstrGtorsors, module 707: AbstractTorsors G = Σ_{X : G-set} ‖P_G = X‖).
   ES_n ≔ Σ_{V : OS_n} Torsor_V and ES ≔ Σ_{V : OS} Torsor_V; ES ≃ Σ_n ES_n uses
   uniqueness of dimension (module 1413). Points E is the torsor's set,
   Vectors E the vector space; v + P is the torsor action, and Q - P is the
   unique v with v + P = Q. The standard space 𝔼ⁿ is (𝕍ⁿ, principal torsor
   of Kⁿ). Torsor_V is literally B(concr V) (module 707), which is the book's
   B V (lem:BGbytorsor). `}

{` The additive group underlying an inner product space. `}
def ip_additive_group (K : EuclideanField) (V : InnerProductSpace K) : AbstractGroup
  ≔ module_group (K .field .fst) (V .space)

{` def:EuclideanSpace; ES. `}
def EuclideanSpace (K : EuclideanField) : Type
  ≔ Σ (InnerProductSpace K) (V ↦ AbstractTorsors (ip_additive_group K V))

{` ES_n. `}
def EuclideanSpaceDim (K : EuclideanField) (n : Nat) : Type
  ≔ Σ (InnerProductSpaceDim K n) (V ↦ AbstractTorsors (ip_additive_group K (V .fst)))

def euclidean_space_dim_forget (K : EuclideanField) (n : Nat) (E : EuclideanSpaceDim K n) : EuclideanSpace K
  ≔ (E .fst .fst, E .snd)

def euclidean_vectors (K : EuclideanField) (E : EuclideanSpace K) : Type ≔ ip_carrier K (E .fst)

def euclidean_points (K : EuclideanField) (E : EuclideanSpace K) : Type
  ≔ agset_carrier (ip_additive_group K (E .fst)) (E .snd .fst)

def euclidean_points_set (K : EuclideanField) (E : EuclideanSpace K) : isSet (euclidean_points K E)
  ≔ agset_carrier_set (ip_additive_group K (E .fst)) (E .snd .fst)

{` v + P. `}
def euclidean_translate (K : EuclideanField) (E : EuclideanSpace K) (v : euclidean_vectors K E)
  (P : euclidean_points K E) : euclidean_points K E
  ≔ agset_act (ip_additive_group K (E .fst)) (E .snd .fst) v P

{` v + (w + P) = (v + w) + P. `}
def euclidean_translate_assoc (K : EuclideanField) (E : EuclideanSpace K) (v w : euclidean_vectors K E)
  (P : euclidean_points K E)
  : Id (euclidean_points K E) (euclidean_translate K E v (euclidean_translate K E w P))
      (euclidean_translate K E (E .fst .space .add v w) P)
  ≔ inverse (euclidean_points K E) (euclidean_translate K E (E .fst .space .add v w) P)
      (euclidean_translate K E v (euclidean_translate K E w P))
      (agset_act_mul (ip_additive_group K (E .fst)) (E .snd .fst) v w P)

{` Points E is non-empty. `}
def euclidean_points_nonempty (K : EuclideanField) (E : EuclideanSpace K) : Mere (euclidean_points K E)
  ≔ let G ≔ ip_additive_group K (E .fst) in let X ≔ E .snd .fst in
    mere_rec (Id (AbstractGSet G) (agset_principal G) X) (Mere (euclidean_points K E)) (mere_isprop (euclidean_points K E))
      (p ↦ mere (euclidean_points K E) (agset_path_to_iso G (agset_principal G) X p .fst .map (G .unit)))
      (E .snd .snd)

{` Torsors are free and transitive: for points P, Q of an abstract
   G-torsor X there is a unique s with s · P = Q. `}
def abstract_torsor_difference_contractible (G : AbstractGroup) (X : AbstractGSet G)
  (hX : Mere (Id (AbstractGSet G) (agset_principal G) X)) (P Q : agset_carrier G X)
  : BookIsContr (Σ (G .carrier) (v ↦ Id (agset_carrier G X) (agset_act G X v P) Q))
  ≔ let Pt ≔ agset_carrier G X in let S ≔ G .carrier in
    let act ≔ agset_act G X in
    let D ≔ Σ S (v ↦ Id Pt (act v P) Q) in
    mere_rec (Id (AbstractGSet G) (agset_principal G) X) (BookIsContr D) (book_iscontr_isprop D)
      (p ↦
        let f ≔ agset_path_to_iso G (agset_principal G) X p in
        let fm ≔ f .fst .map in
        let fi ≔ equiv_inverse_map S Pt (f .fst) in
        let g0 ≔ fi P in let g1 ≔ fi Q in
        let solvev : (v : S) → Id Pt (act v P) Q → Id S v (G .mul g1 (G .inv g0))
          ≔ v h ↦
            let e : Id S (G .mul v g0) g1
              ≔ calc
                  G .mul v g0 = fi (fm (G .mul v g0)) by equiv_unit S Pt (f .fst) (G .mul v g0)
                  = fi (act v (fm g0)) by refl fi (f .snd v g0)
                  = fi (act v P) by refl ((x ↦ fi (act v x)) : Pt → S) (equiv_counit S Pt (f .fst) P)
                  = g1 by refl fi h ∎ in
            calc
              v = G .mul (G .mul v g0) (G .inv g0)
                by inverse S (G .mul (G .mul v g0) (G .inv g0)) v (ag_mul_inv_cancel_right G v g0)
              = G .mul g1 (G .inv g0) by refl ((x ↦ G .mul x (G .inv g0)) : S → S) e ∎ in
        let v0 ≔ G .mul g1 (G .inv g0) in
        let h0 : Id Pt (act v0 P) Q
          ≔ calc
              act v0 P = act v0 (fm g0)
                by refl (act v0) (inverse Pt (fm g0) P (equiv_counit S Pt (f .fst) P))
              = fm (G .mul v0 g0) by inverse Pt (fm (G .mul v0 g0)) (act v0 (fm g0)) (f .snd v0 g0)
              = fm g1 by refl fm (ag_mul_cancel_inv_right G g1 g0)
              = Q by equiv_counit S Pt (f .fst) Q ∎ in
        let hD : (v : S) → isProp (Id Pt (act v P) Q) ≔ v ↦ agset_carrier_set G X (act v P) Q in
        (center ≔ (v0, h0),
         contract ≔ u ↦ subtype_equal S (v ↦ Id Pt (act v P) Q) hD (v0, h0) u
           (inverse S (u .fst) v0 (solvev (u .fst) (u .snd)))))
      hX

{` "Given P, Q there is a unique v with v + P = Q" (Q - P). `}
def euclidean_difference_contractible (K : EuclideanField) (E : EuclideanSpace K) (P Q : euclidean_points K E)
  : BookIsContr (Σ (euclidean_vectors K E) (v ↦ Id (euclidean_points K E) (euclidean_translate K E v P) Q))
  ≔ abstract_torsor_difference_contractible (ip_additive_group K (E .fst)) (E .snd .fst) (E .snd .snd) P Q

{` Q - P. `}
def euclidean_difference (K : EuclideanField) (E : EuclideanSpace K) (Q P : euclidean_points K E)
  : euclidean_vectors K E
  ≔ euclidean_difference_contractible K E P Q .center .fst

def euclidean_difference_law (K : EuclideanField) (E : EuclideanSpace K) (Q P : euclidean_points K E)
  : Id (euclidean_points K E) (euclidean_translate K E (euclidean_difference K E Q P) P) Q
  ≔ euclidean_difference_contractible K E P Q .center .snd

{` The standard Euclidean space 𝔼ⁿ = (𝕍ⁿ, principal torsor of Kⁿ). `}
def euclidean_standard (K : EuclideanField) (n : Nat) : EuclideanSpaceDim K n
  ≔ (standard_inner_product_space_dim K n, abstract_principal_torsor (ip_additive_group K (standard_inner_product_space K n)))

def euclidean_standard_points (K : EuclideanField) (n : Nat)
  : Id Type (euclidean_points K (euclidean_space_dim_forget K n (euclidean_standard K n))) (Fin n → ef_carrier K)
  ≔ refl (Fin n → ef_carrier K)

{` Litmus: in 𝔼ⁿ, v + P is the sum of coordinate vectors (by computation). `}
def euclidean_standard_translate (K : EuclideanField) (n : Nat) (v P : Fin n → ef_carrier K) (i : Fin n)
  : Id (ef_carrier K) (euclidean_translate K (euclidean_space_dim_forget K n (euclidean_standard K n)) v P i)
      (K .field .fst .add (v i) (P i))
  ≔ refl (K .field .fst .add (v i) (P i))

{` thm:EuclideanNormalization: every E : ES_n is merely equal to 𝔼ⁿ. By
   thm:GramSchmidt we may assume Vectors E = 𝕍ⁿ (transport the torsor), and
   any torsor is merely the principal one. `}
def euclidean_normalization (K : EuclideanField) (n : Nat) (E : EuclideanSpaceDim K n)
  : Mere (Id (EuclideanSpaceDim K n) E (euclidean_standard K n))
  ≔ let ES ≔ EuclideanSpaceDim K n in let OSn ≔ InnerProductSpaceDim K n in
    let std ≔ standard_inner_product_space_dim K n in let E0 ≔ euclidean_standard K n in
    let Tor ≔ (V : OSn) ↦ AbstractTorsors (ip_additive_group K (V .fst)) in
    mere_rec (Id OSn (E .fst) std) (Mere (Id ES E E0)) (mere_isprop (Id ES E E0))
      (p ↦
        let T' ≔ transport OSn Tor (E .fst) std p (E .snd) in
        let e1 : Id ES E (std, T')
          ≔ (p, pathover_of_eq OSn Tor (E .fst) std p (E .snd) T' (refl T')) in
        mere_rec (Id (Tor std) T' (E0 .snd)) (Mere (Id ES E E0)) (mere_isprop (Id ES E E0))
          (q ↦ mere (Id ES E E0) (concat ES E (std, T') E0 e1 (refl std, q)))
          (abstract_torsors_connected (ip_additive_group K (std .fst)) .snd T' (E0 .snd)))
      (gram_schmidt_theorem K n (E .fst))

{` lem:EuclideanSpace1Type: ES_n is a 1-type (a Σ of groupoids; the book
   phrases ES_n as Σ_{V : B O(n)} B V by lem:BGbytorsor). ES is a 1-type too. `}
def euclidean_space_dim_groupoid (K : EuclideanField) (n : Nat) : isGroupoid (EuclideanSpaceDim K n)
  ≔ hlevel_to_groupoid (EuclideanSpaceDim K n)
      (hlevel_sigma (suc. (suc. (suc. zero.)))
        (InnerProductSpaceDim K n) (V ↦ AbstractTorsors (ip_additive_group K (V .fst)))
        (groupoid_to_hlevel (InnerProductSpaceDim K n) (inner_product_space_dim_groupoid K n))
        (V ↦ groupoid_to_hlevel (AbstractTorsors (ip_additive_group K (V .fst)))
          (abstract_torsors_groupoid (ip_additive_group K (V .fst)))))

def euclidean_space_groupoid (K : EuclideanField) : isGroupoid (EuclideanSpace K)
  ≔ hlevel_to_groupoid (EuclideanSpace K)
      (hlevel_sigma (suc. (suc. (suc. zero.)))
        (InnerProductSpace K) (V ↦ AbstractTorsors (ip_additive_group K V))
        (groupoid_to_hlevel (InnerProductSpace K) (inner_product_space_groupoid K))
        (V ↦ groupoid_to_hlevel (AbstractTorsors (ip_additive_group K V)) (abstract_torsors_groupoid (ip_additive_group K V))))

{` ES ≃ Σ_n ES_n (map: forget n), by uniqueness of dimension. `}
def euclidean_space_dim_sum_equiv (K : EuclideanField)
  : Equiv (Σ Nat (n ↦ EuclideanSpaceDim K n)) (EuclideanSpace K)
  ≔ let ES ≔ EuclideanSpace K in
    let A ≔ Σ Nat (n ↦ EuclideanSpaceDim K n) in
    let back : ES → A
      ≔ E ↦ let d ≔ vector_space_dimension_data K (E .fst .space) (E .fst .finite) in (d .fst, ((E .fst, d .snd), E .snd)) in
    quasi_inverse_equiv A ES (x ↦ euclidean_space_dim_forget K (x .fst) (x .snd)) back
      (x ↦
        let V ≔ x .snd .fst .fst in let T ≔ x .snd .snd in
        let D ≔ Σ Nat (n ↦ HasDimension (K .field) n (V .space)) in
        refl ((e ↦ (e .fst, ((V, e .snd), T))) : D → A)
          (finite_dimension_prop K (V .space) (vector_space_dimension_data K (V .space) (V .finite))
            (x .fst, x .snd .fst .snd)))
      (E ↦ refl E)

{` Normalization for ES: a Euclidean space of dimension n is merely 𝔼ⁿ. `}
def euclidean_normalization_es (K : EuclideanField) (n : Nat) (E : EuclideanSpace K)
  (h : HasDimension (K .field) n (E .fst .space))
  : Mere (Id (EuclideanSpace K) E (euclidean_space_dim_forget K n (euclidean_standard K n)))
  ≔ let ES ≔ EuclideanSpace K in let E0 ≔ euclidean_space_dim_forget K n (euclidean_standard K n) in
    let En : EuclideanSpaceDim K n ≔ ((E .fst, h), E .snd) in
    mere_rec (Id (EuclideanSpaceDim K n) En (euclidean_standard K n)) (Mere (Id ES E E0)) (mere_isprop (Id ES E E0))
      (p ↦ mere (Id ES E E0)
        (refl ((F ↦ euclidean_space_dim_forget K n F) : EuclideanSpaceDim K n → ES) p))
      (euclidean_normalization K n En)
