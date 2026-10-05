export "975-sigma3-symmetries"

{` Chapter 9 (subgroups.tex), xca:Sub(Sigma3) (line 1311), the
   classification: every DECIDABLE subgroup of Σ_3 (IsDecidableSubgroup,
   chapter 5: the underlying set of its G-set has decidable equality, so
   membership of each symmetry is decidable) is one of 1, A_3, Σ_3, T_0,
   T_1, T_2. Proof by cases on the membership of (0 1), (0 2), (1 2) and
   (0 1 2), using closure under products, and sigma3_same_members.
   Consequently the orbits of decidable subgroups are {1}, {A_3}, {Σ_3}
   (the normal ones) and {T_0, T_1, T_2}; the six are pairwise different.
   Without decidability the classification is not provable constructively:
   it implies excluded middle (module 977). `}

def Sigma3SixSubgroups (S : Subgroups (symmetric_group three)) : Type
  ≔ Sum (Id (Subgroups (symmetric_group three)) S (principal_subgroup (symmetric_group three)))
      (Sum (Id (Subgroups (symmetric_group three)) S (alternating_subgroup (suc. zero.)))
        (Sum (Id (Subgroups (symmetric_group three)) S (group_full_subgroup (symmetric_group three)))
          (Sum (Id (Subgroups (symmetric_group three)) S (sigma3_point_subgroup fin3_zero))
            (Sum (Id (Subgroups (symmetric_group three)) S (sigma3_point_subgroup fin3_one))
              (Id (Subgroups (symmetric_group three)) S (sigma3_point_subgroup fin3_two))))))

def sigma3_leaf_ONE (S : Subgroups (symmetric_group three)) (n01 : Not (Sigma3Mem S t01.)) (n02 : Not (Sigma3Mem S t02.)) (n12 : Not (Sigma3Mem S t12.)) (ncyc : Not (Sigma3Mem S cyc.))
  : Id (Subgroups (symmetric_group three)) S (principal_subgroup (symmetric_group three))
  ≔ let ncin : Not (Sigma3Mem S cin.) ≔ r ↦ ncyc (sigma3_mem_prod S cin. cin. cyc. sigma3_prod_cin_cin r r) in
    sigma3_same_members S (principal_subgroup (symmetric_group three)) (n ↦ match n [
    | ide. ↦ (_ ↦ sigma3_mem_ide (principal_subgroup (symmetric_group three)), _ ↦ sigma3_mem_ide S)
    | t01. ↦ (r ↦ match n01 r [], r ↦ match sigma3_not_trivial_mem t01. (inr. star. : Fin three) (fin3_differ (inl. (inr. star.) : Fin three) (inr. star. : Fin three) (refl (false. : Bool))) r [])
    | t02. ↦ (r ↦ match n02 r [], r ↦ match sigma3_not_trivial_mem t02. (inr. star. : Fin three) (fin3_differ (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (refl (false. : Bool))) r [])
    | t12. ↦ (r ↦ match n12 r [], r ↦ match sigma3_not_trivial_mem t12. (inl. (inr. star.) : Fin three) (fin3_differ (inl. (inl. (inr. star.)) : Fin three) (inl. (inr. star.) : Fin three) (refl (false. : Bool))) r [])
    | cyc. ↦ (r ↦ match ncyc r [], r ↦ match sigma3_not_trivial_mem cyc. (inr. star. : Fin three) (fin3_differ (inl. (inr. star.) : Fin three) (inr. star. : Fin three) (refl (false. : Bool))) r [])
    | cin. ↦ (r ↦ match ncin r [], r ↦ match sigma3_not_trivial_mem cin. (inr. star. : Fin three) (fin3_differ (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (refl (false. : Bool))) r [])
    ])

def sigma3_leaf_T0 (S : Subgroups (symmetric_group three)) (n01 : Not (Sigma3Mem S t01.)) (n02 : Not (Sigma3Mem S t02.)) (r12 : Sigma3Mem S t12.) (ncyc : Not (Sigma3Mem S cyc.))
  : Id (Subgroups (symmetric_group three)) S (sigma3_point_subgroup fin3_zero)
  ≔ let ncin : Not (Sigma3Mem S cin.) ≔ r ↦ ncyc (sigma3_mem_prod S cin. cin. cyc. sigma3_prod_cin_cin r r) in
    sigma3_same_members S (sigma3_point_subgroup fin3_zero) (n ↦ match n [
    | ide. ↦ (_ ↦ refl (inr. star. : Fin three), _ ↦ sigma3_mem_ide S)
    | t01. ↦ (r ↦ match n01 r [], r ↦ match fin3_differ (inl. (inr. star.) : Fin three) (inr. star. : Fin three) (refl (false. : Bool)) r [])
    | t02. ↦ (r ↦ match n02 r [], r ↦ match fin3_differ (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (refl (false. : Bool)) r [])
    | t12. ↦ (_ ↦ refl (inr. star. : Fin three), _ ↦ r12)
    | cyc. ↦ (r ↦ match ncyc r [], r ↦ match fin3_differ (inl. (inr. star.) : Fin three) (inr. star. : Fin three) (refl (false. : Bool)) r [])
    | cin. ↦ (r ↦ match ncin r [], r ↦ match fin3_differ (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (refl (false. : Bool)) r [])
    ])

def sigma3_leaf_T1 (S : Subgroups (symmetric_group three)) (n01 : Not (Sigma3Mem S t01.)) (r02 : Sigma3Mem S t02.) (n12 : Not (Sigma3Mem S t12.)) (ncyc : Not (Sigma3Mem S cyc.))
  : Id (Subgroups (symmetric_group three)) S (sigma3_point_subgroup fin3_one)
  ≔ let ncin : Not (Sigma3Mem S cin.) ≔ r ↦ ncyc (sigma3_mem_prod S cin. cin. cyc. sigma3_prod_cin_cin r r) in
    sigma3_same_members S (sigma3_point_subgroup fin3_one) (n ↦ match n [
    | ide. ↦ (_ ↦ refl (inl. (inr. star.) : Fin three), _ ↦ sigma3_mem_ide S)
    | t01. ↦ (r ↦ match n01 r [], r ↦ match fin3_differ (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (refl (false. : Bool)) r [])
    | t02. ↦ (_ ↦ refl (inl. (inr. star.) : Fin three), _ ↦ r02)
    | t12. ↦ (r ↦ match n12 r [], r ↦ match fin3_differ (inl. (inl. (inr. star.)) : Fin three) (inl. (inr. star.) : Fin three) (refl (false. : Bool)) r [])
    | cyc. ↦ (r ↦ match ncyc r [], r ↦ match fin3_differ (inl. (inl. (inr. star.)) : Fin three) (inl. (inr. star.) : Fin three) (refl (false. : Bool)) r [])
    | cin. ↦ (r ↦ match ncin r [], r ↦ match fin3_differ (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (refl (false. : Bool)) r [])
    ])

def sigma3_leaf_T2 (S : Subgroups (symmetric_group three)) (r01 : Sigma3Mem S t01.) (n02 : Not (Sigma3Mem S t02.)) (n12 : Not (Sigma3Mem S t12.)) (ncyc : Not (Sigma3Mem S cyc.))
  : Id (Subgroups (symmetric_group three)) S (sigma3_point_subgroup fin3_two)
  ≔ let ncin : Not (Sigma3Mem S cin.) ≔ r ↦ ncyc (sigma3_mem_prod S cin. cin. cyc. sigma3_prod_cin_cin r r) in
    sigma3_same_members S (sigma3_point_subgroup fin3_two) (n ↦ match n [
    | ide. ↦ (_ ↦ refl (inl. (inl. (inr. star.)) : Fin three), _ ↦ sigma3_mem_ide S)
    | t01. ↦ (_ ↦ refl (inl. (inl. (inr. star.)) : Fin three), _ ↦ r01)
    | t02. ↦ (r ↦ match n02 r [], r ↦ match fin3_differ (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (refl (false. : Bool)) r [])
    | t12. ↦ (r ↦ match n12 r [], r ↦ match fin3_differ (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (refl (false. : Bool)) r [])
    | cyc. ↦ (r ↦ match ncyc r [], r ↦ match fin3_differ (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (refl (false. : Bool)) r [])
    | cin. ↦ (r ↦ match ncin r [], r ↦ match fin3_differ (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (refl (false. : Bool)) r [])
    ])

def sigma3_leaf_A3 (S : Subgroups (symmetric_group three)) (n01 : Not (Sigma3Mem S t01.)) (n02 : Not (Sigma3Mem S t02.)) (n12 : Not (Sigma3Mem S t12.)) (rc : Sigma3Mem S cyc.)
  : Id (Subgroups (symmetric_group three)) S (alternating_subgroup (suc. zero.))
  ≔ let rin : Sigma3Mem S cin. ≔ sigma3_mem_prod S cyc. cyc. cin. sigma3_prod_cyc_cyc rc rc in
    sigma3_same_members S (alternating_subgroup (suc. zero.)) (n ↦ match n [
    | ide. ↦ (_ ↦ sigma3_mem_ide (alternating_subgroup (suc. zero.)), _ ↦ sigma3_mem_ide S)
    | t01. ↦ (r ↦ match n01 r [], r ↦ match sigma3_a3_not_mem_of_minus (sigma3_sym t01.) sigma3_sign_t01 r [])
    | t02. ↦ (r ↦ match n02 r [], r ↦ match sigma3_a3_not_mem_of_minus (sigma3_sym t02.) sigma3_sign_t02 r [])
    | t12. ↦ (r ↦ match n12 r [], r ↦ match sigma3_a3_not_mem_of_minus (sigma3_sym t12.) sigma3_sign_t12 r [])
    | cyc. ↦ (_ ↦ sigma3_a3_mem_of_plus (sigma3_sym cyc.) sigma3_sign_cyc, _ ↦ rc)
    | cin. ↦ (_ ↦ sigma3_a3_mem_of_plus (sigma3_sym cin.) sigma3_sign_cin, _ ↦ rin)
    ])

def sigma3_leaf_FULL (S : Subgroups (symmetric_group three)) (r01 : Sigma3Mem S t01.) (r02 : Sigma3Mem S t02.) (r12 : Sigma3Mem S t12.) (rc : Sigma3Mem S cyc.)
  : Id (Subgroups (symmetric_group three)) S (group_full_subgroup (symmetric_group three))
  ≔ let rin : Sigma3Mem S cin. ≔ sigma3_mem_prod S cyc. cyc. cin. sigma3_prod_cyc_cyc rc rc in
    sigma3_same_members S (group_full_subgroup (symmetric_group three)) (n ↦ match n [
    | ide. ↦ (_ ↦ full_subgroup_has_symmetry (symmetric_group three) (sigma3_sym ide.), _ ↦ sigma3_mem_ide S)
    | t01. ↦ (_ ↦ full_subgroup_has_symmetry (symmetric_group three) (sigma3_sym t01.), _ ↦ r01)
    | t02. ↦ (_ ↦ full_subgroup_has_symmetry (symmetric_group three) (sigma3_sym t02.), _ ↦ r02)
    | t12. ↦ (_ ↦ full_subgroup_has_symmetry (symmetric_group three) (sigma3_sym t12.), _ ↦ r12)
    | cyc. ↦ (_ ↦ full_subgroup_has_symmetry (symmetric_group three) (sigma3_sym cyc.), _ ↦ rc)
    | cin. ↦ (_ ↦ full_subgroup_has_symmetry (symmetric_group three) (sigma3_sym cin.), _ ↦ rin)
    ])

def sigma3_classify (S : Subgroups (symmetric_group three)) (dec : (n : Sigma3Name) → Decidable (Sigma3Mem S n))
  : Sigma3SixSubgroups S
  ≔ match dec cyc. [
  | inl. rc ↦ match dec t01. [
    | inl. r01 ↦ match dec t02. [
      | inl. r02 ↦ match dec t12. [
        | inl. r12 ↦ inr. (inr. (inl. (sigma3_leaf_FULL S r01 r02 r12 rc)))
        | inr. n12 ↦ match n12 (sigma3_mem_prod S t01. cyc. t12. sigma3_prod_t01_cyc r01 rc) []
        ]
      | inr. n02 ↦ match dec t12. [
        | inl. r12 ↦ match n02 (sigma3_mem_prod S t12. cyc. t02. sigma3_prod_t12_cyc r12 rc) []
        | inr. n12 ↦ match n12 (sigma3_mem_prod S t01. cyc. t12. sigma3_prod_t01_cyc r01 rc) []
        ]
      ]
    | inr. n01 ↦ match dec t02. [
      | inl. r02 ↦ match dec t12. [
        | inl. r12 ↦ match n01 (sigma3_mem_prod S t02. cyc. t01. sigma3_prod_t02_cyc r02 rc) []
        | inr. n12 ↦ match n01 (sigma3_mem_prod S t02. cyc. t01. sigma3_prod_t02_cyc r02 rc) []
        ]
      | inr. n02 ↦ match dec t12. [
        | inl. r12 ↦ match n02 (sigma3_mem_prod S t12. cyc. t02. sigma3_prod_t12_cyc r12 rc) []
        | inr. n12 ↦ inr. (inl. (sigma3_leaf_A3 S n01 n02 n12 rc))
        ]
      ]
    ]
  | inr. ncyc ↦ match dec t01. [
    | inl. r01 ↦ match dec t02. [
      | inl. r02 ↦ match dec t12. [
        | inl. r12 ↦ match (r ↦ ncyc (sigma3_mem_prod S cin. cin. cyc. sigma3_prod_cin_cin r r)) (sigma3_mem_prod S t01. t02. cin. sigma3_prod_t01_t02 r01 r02) []
        | inr. n12 ↦ match (r ↦ ncyc (sigma3_mem_prod S cin. cin. cyc. sigma3_prod_cin_cin r r)) (sigma3_mem_prod S t01. t02. cin. sigma3_prod_t01_t02 r01 r02) []
        ]
      | inr. n02 ↦ match dec t12. [
        | inl. r12 ↦ match ncyc (sigma3_mem_prod S t01. t12. cyc. sigma3_prod_t01_t12 r01 r12) []
        | inr. n12 ↦ inr. (inr. (inr. (inr. (inr. (sigma3_leaf_T2 S r01 n02 n12 ncyc)))))
        ]
      ]
    | inr. n01 ↦ match dec t02. [
      | inl. r02 ↦ match dec t12. [
        | inl. r12 ↦ match (r ↦ ncyc (sigma3_mem_prod S cin. cin. cyc. sigma3_prod_cin_cin r r)) (sigma3_mem_prod S t02. t12. cin. sigma3_prod_t02_t12 r02 r12) []
        | inr. n12 ↦ inr. (inr. (inr. (inr. (inl. (sigma3_leaf_T1 S n01 r02 n12 ncyc)))))
        ]
      | inr. n02 ↦ match dec t12. [
        | inl. r12 ↦ inr. (inr. (inr. (inl. (sigma3_leaf_T0 S n01 n02 r12 ncyc))))
        | inr. n12 ↦ inl. (sigma3_leaf_ONE S n01 n02 n12 ncyc)
        ]
      ]
    ]
  ]

{` xca:Sub(Sigma3), classification: every decidable subgroup of Σ_3 is one
   of the six. `}
def sigma3_decidable_subgroup_classification (S : Subgroups (symmetric_group three))
  (d : IsDecidableSubgroup (symmetric_group three) S) : Sigma3SixSubgroups S
  ≔ sigma3_classify S
      (n ↦ d (gset_usym_act (symmetric_group three) (S .gset) (sigma3_sym n) (S .point)) (S .point))

{` The six are pairwise different: T_0, T_1, T_2 are not normal while 1,
   A_3, Σ_3 are; 1 ≠ Σ_3 (module 972); A_3 ≠ 1 ((0 1 2) ∈ A_3) and
   A_3 ≠ Σ_3 ((0 1) ∉ A_3). `}
def sigma3_a3_ne_trivial
  (e : Id (Subgroups (symmetric_group three)) (alternating_subgroup (suc. zero.)) (principal_subgroup (symmetric_group three)))
  : Empty
  ≔ let G ≔ symmetric_group three in
    sigma3_not_trivial_mem cyc. fin3_zero (fin3_differ fin3_one fin3_zero (refl (false. : Bool)))
      (subgroup_symmetry_transport G (alternating_subgroup (suc. zero.)) (principal_subgroup G) e (sigma3_sym cyc.)
        (sigma3_a3_mem_of_plus (sigma3_sym cyc.) sigma3_sign_cyc))

def sigma3_a3_ne_full
  (e : Id (Subgroups (symmetric_group three)) (alternating_subgroup (suc. zero.)) (group_full_subgroup (symmetric_group three)))
  : Empty
  ≔ let G ≔ symmetric_group three in
    sigma3_a3_not_mem_of_minus (sigma3_sym t01.) sigma3_sign_t01
      (subgroup_symmetry_transport G (group_full_subgroup G) (alternating_subgroup (suc. zero.))
        (inverse (Subgroups G) (alternating_subgroup (suc. zero.)) (group_full_subgroup G) e) (sigma3_sym t01.)
        (full_subgroup_has_symmetry G (sigma3_sym t01.)))

def sigma3_normal_ne_point_subgroup (S : Subgroups (symmetric_group three)) (n : IsNormalSubgroup (symmetric_group three) S)
  (k : Fin three) (e : Id (Subgroups (symmetric_group three)) S (sigma3_point_subgroup k)) : Empty
  ≔ sigma3_point_subgroup_not_normal k
      (transport (Subgroups (symmetric_group three)) (IsNormalSubgroup (symmetric_group three)) S (sigma3_point_subgroup k) e n)

{` Orbit structure of the decidable subgroups: either S is normal (a fixed
   point, its orbit is {S}) and then S is 1, A_3 or Σ_3, or S is one of
   T_0, T_1, T_2, whose orbit is {T_0, T_1, T_2} (sigma3_order_two_orbit,
   sigma3_T0_conjugate_T1, sigma3_T0_conjugate_T2 of module 972). `}
def sigma3_decidable_orbit_structure (S : Subgroups (symmetric_group three))
  (d : IsDecidableSubgroup (symmetric_group three) S)
  : Sum (Product (IsNormalSubgroup (symmetric_group three) S)
          (Sum (Id (Subgroups (symmetric_group three)) S (principal_subgroup (symmetric_group three)))
            (Sum (Id (Subgroups (symmetric_group three)) S (alternating_subgroup (suc. zero.)))
              (Id (Subgroups (symmetric_group three)) S (group_full_subgroup (symmetric_group three))))))
      (Product (Not (IsNormalSubgroup (symmetric_group three) S))
        (Σ (Fin three) (k ↦ Id (Subgroups (symmetric_group three)) S (sigma3_point_subgroup k))))
  ≔ let G ≔ symmetric_group three in
    let SG ≔ Subgroups G in
    let tr : (T : SG) → Id SG S T → IsNormalSubgroup G T → IsNormalSubgroup G S
      ≔ T e n ↦ transport SG (IsNormalSubgroup G) T S (inverse SG S T e) n in
    match sigma3_decidable_subgroup_classification S d [
    | inl. e ↦ inl. (tr (principal_subgroup G) e (principal_subgroup_normal G), inl. e)
    | inr. (inl. e) ↦ inl. (tr (alternating_subgroup (suc. zero.)) e sigma3_alternating_normal, inr. (inl. e))
    | inr. (inr. (inl. e)) ↦ inl. (tr (group_full_subgroup G) e (full_subgroup_normal G), inr. (inr. e))
    | inr. (inr. (inr. (inl. e))) ↦ inr. (n ↦ sigma3_normal_ne_point_subgroup S n fin3_zero e, (fin3_zero, e))
    | inr. (inr. (inr. (inr. (inl. e)))) ↦ inr. (n ↦ sigma3_normal_ne_point_subgroup S n fin3_one e, (fin3_one, e))
    | inr. (inr. (inr. (inr. (inr. e)))) ↦ inr. (n ↦ sigma3_normal_ne_point_subgroup S n fin3_two e, (fin3_two, e)) ]
