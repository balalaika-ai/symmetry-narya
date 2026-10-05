export "592-c6-half-subgroup-group"
export "419-cyclic-two-and-generated"
export "261-circle-flip-conjugation"
export "507-subgroups-monos-equiv"

{` xca:C3subSG3: monomorphisms j, j' : C_3 → Σ_3 with USym j ≠ USym j' but
   (C_3, j) = (C_3, j') in Mono(Σ_3).

   j is the forgetful homomorphism Bj((X, t), !) = (X, !) (cyclic_forget_hom 2,
   module 418), a monomorphism since USym j is injective (forget_hom_injective).
   j' = j ∘ α where α : C_3 → C_3 is inversion, Bα(X, t) = (X, t⁻¹), pointed by
   the identification (Fin 3, s) = (Fin 3, s⁻¹) given by the transposition
   (1 2). α maps a symmetry g with g(0) = k to one with value (1 2)(k)
   (c3inv_alpha_index), so USym j' sends the generator to s⁻¹ ≠ s
   (c3inv_usym_differ), while Bα is a pointed equivalence with Bj ∘ Bα = Bj',
   which identifies (C_3, j') with (C_3, j) (c3inv_monos_path). `}

def c3inv_group : Group ≔ cyclic_group_fin two

def c3inv_cycle : Cycles ≔ finite_fin_cycle two

def c3inv_s : Equiv (Fin three) (Fin three) ≔ finite_fin_successor two

def c3inv_flip_step (x : Fin three) : Id (Fin three) (c3inv_s .map (fin3_swap12 (c3inv_s .map x))) (fin3_swap12 x)
  ≔ match x [
  | inr. star. ↦ refl fin3_zero
  | inl. (inr. star.) ↦ refl fin3_two
  | inl. (inl. (inr. star.)) ↦ refl fin3_one
  | inl. (inl. (inl. e)) ↦ match e [] ]

{` (1 2) ∘ s = s⁻¹ ∘ (1 2). `}
def c3inv_flip_comm (x : Fin three)
  : Id (Fin three) (fin3_swap12 (c3inv_s .map x)) (equiv_inverse_map (Fin three) (Fin three) c3inv_s (fin3_swap12 x))
  ≔ inverse (Fin three) (equiv_inverse_map (Fin three) (Fin three) c3inv_s (fin3_swap12 x)) (fin3_swap12 (c3inv_s .map x))
      (inverse_at_known_point (Fin three) (Fin three) c3inv_s (fin3_swap12 (c3inv_s .map x)) (fin3_swap12 x) (c3inv_flip_step x))

def c3inv_iso : PermutationIsomorphisms (c3inv_cycle .fst) (cycle_inverse c3inv_cycle .fst)
  ≔ (fin3_swap12_equiv, c3inv_flip_comm)

{` (Fin 3, s) = (Fin 3, s⁻¹) via (1 2). `}
def c3inv_path : Id Cycles c3inv_cycle (cycle_inverse c3inv_cycle)
  ≔ equiv_inverse_map (Id Cycles c3inv_cycle (cycle_inverse c3inv_cycle))
      (PermutationIsomorphisms (c3inv_cycle .fst) (cycle_inverse c3inv_cycle .fst))
      (cycle_paths_equiv c3inv_cycle (cycle_inverse c3inv_cycle)) c3inv_iso

def c3inv_path_eval (x : Fin three)
  : Id (Fin three) (cycle_path_evaluate c3inv_cycle (cycle_inverse c3inv_cycle) c3inv_path x) (fin3_swap12 x)
  ≔ c6half_iso_eval_path (c3inv_cycle .fst) (cycle_inverse c3inv_cycle .fst)
      (cycle_paths_equiv c3inv_cycle (cycle_inverse c3inv_cycle) .map c3inv_path) c3inv_iso
      (equiv_counit (Id Cycles c3inv_cycle (cycle_inverse c3inv_cycle))
        (PermutationIsomorphisms (c3inv_cycle .fst) (cycle_inverse c3inv_cycle .fst))
        (cycle_paths_equiv c3inv_cycle (cycle_inverse c3inv_cycle)) c3inv_iso) x

{` (X, (t⁻¹)⁻¹) = (X, t). `}
def c3inv_double_iso (c : Cycles) : PermutationIsomorphisms (cycle_inverse (cycle_inverse c) .fst) (c .fst)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    (identity_equiv X, x ↦ inverse_at_known_point X X (canonical_inverse_equiv X X t) (t .map x) x
      (equiv_retraction X X t x))

def c3inv_double_path (c : Cycles) : Id Cycles (cycle_inverse (cycle_inverse c)) c
  ≔ equiv_inverse_map (Id Cycles (cycle_inverse (cycle_inverse c)) c)
      (PermutationIsomorphisms (cycle_inverse (cycle_inverse c) .fst) (c .fst))
      (cycle_paths_equiv (cycle_inverse (cycle_inverse c)) c) (c3inv_double_iso c)

{` Bα : BC_3 → BC_3, (X, t) ↦ (X, t⁻¹). `}
def c3inv_alpha_fun (u : CycFin two) : CycFin two
  ≔ (cycle_inverse (u .fst),
     mere_rec (Id Cycles c3inv_cycle (u .fst)) (Mere (Id Cycles c3inv_cycle (cycle_inverse (u .fst))))
       (mere_isprop (Id Cycles c3inv_cycle (cycle_inverse (u .fst))))
       (p ↦ mere (Id Cycles c3inv_cycle (cycle_inverse (u .fst)))
         (concat Cycles c3inv_cycle (cycle_inverse c3inv_cycle) (cycle_inverse (u .fst)) c3inv_path (refl cycle_inverse p)))
       (u .snd))

def c3inv_alpha_invol (u : CycFin two) : Id (CycFin two) (c3inv_alpha_fun (c3inv_alpha_fun u)) u
  ≔ component_path Cycles c3inv_cycle (c3inv_alpha_fun (c3inv_alpha_fun u)) u (c3inv_double_path (u .fst))

def c3inv_alpha_pointed : BookPointedMap (BG c3inv_group) (BG c3inv_group)
  ≔ (c3inv_alpha_fun, component_path Cycles c3inv_cycle (cycfin_point two) (c3inv_alpha_fun (cycfin_point two)) c3inv_path)

def c3inv_alpha_equiv : BookPointedEquiv (BG c3inv_group) (BG c3inv_group)
  ≔ (c3inv_alpha_pointed,
     book_quasi_inverse_equiv (CycFin two) (CycFin two) c3inv_alpha_fun c3inv_alpha_fun c3inv_alpha_invol c3inv_alpha_invol
       .equiv)

{` α : C_3 → C_3 (inversion), an automorphism. `}
def c3inv_alpha : GroupHom c3inv_group c3inv_group ≔ mkhom c3inv_group c3inv_group c3inv_alpha_pointed

{` j, j' = j ∘ α : C_3 → Σ_3. `}
def c3inv_j : GroupHom c3inv_group (symmetric_group three) ≔ cyclic_forget_hom two

def c3inv_j_prime : GroupHom c3inv_group (symmetric_group three)
  ≔ group_hom_compose c3inv_group c3inv_group (symmetric_group three) c3inv_alpha c3inv_j

{` Evaluation g ↦ g(0) via the carrier G-set. `}
def c3inv_carrier_gset : GSet c3inv_group ≔ u ↦ u .fst .fst .fst

def c3inv_index (g : USym c3inv_group) : Fin three ≔ cyclic_group_fin_usym_equiv two .map g

{` α(g)(0) = (1 2)(g(0)). `}
def c3inv_alpha_index (g : USym c3inv_group)
  : Id (Fin three) (c3inv_index (usym_hom c3inv_group c3inv_group c3inv_alpha g)) (fin3_swap12 (c3inv_index g))
  ≔ let G ≔ c3inv_group in
    let X ≔ c3inv_carrier_gset in
    let B ≔ BG G .carrier in
    let pt ≔ cycfin_point two in
    let apt ≔ c3inv_alpha_fun pt in
    let cp : Id B pt apt ≔ c3inv_alpha_pointed .snd in
    let ag : Id B apt apt ≔ refl c3inv_alpha_fun g in
    let act ≔ gset_act G X in
    let k ≔ c3inv_index g in
    let inv_cp : Id B apt pt ≔ inverse B pt apt cp in
    let cp0 : Id (Fin three) (act pt apt cp fin3_zero) fin3_zero ≔ c3inv_path_eval fin3_zero in
    let cpk : Id (Fin three) (act pt apt cp (fin3_swap12 k)) k
      ≔ concat (Fin three) (act pt apt cp (fin3_swap12 k)) (fin3_swap12 (fin3_swap12 k)) k
          (c3inv_path_eval (fin3_swap12 k)) (fin3_swap12_involutive k) in
    calc
      c3inv_index (usym_hom G G c3inv_alpha g)
      = act apt pt (concat B apt apt pt ag inv_cp) (act pt apt cp fin3_zero)
        by gset_act_concat G X pt apt pt cp (concat B apt apt pt ag inv_cp) fin3_zero
      = act apt pt inv_cp (act apt apt ag (act pt apt cp fin3_zero))
        by gset_act_concat G X apt apt pt ag inv_cp (act pt apt cp fin3_zero)
      = act apt pt inv_cp (act apt apt ag fin3_zero)
        by refl ((y ↦ act apt pt inv_cp (act apt apt ag y)) : Fin three → Fin three) cp0
      = act apt pt inv_cp k by refl (act apt pt inv_cp k)
      = act apt pt inv_cp (act pt apt cp (fin3_swap12 k))
        by refl (act apt pt inv_cp) (inverse (Fin three) (act pt apt cp (fin3_swap12 k)) k cpk)
      = fin3_swap12 k by gset_act_inverse_left G X pt apt cp (fin3_swap12 k) ∎

def c3inv_usym_j_injective : PathReflecting (USym c3inv_group) (USym (symmetric_group three))
    (usym_hom c3inv_group (symmetric_group three) c3inv_j)
  ≔ g h e ↦ forget_hom_injective two g h e

def c3inv_j_mono : IsGroupMono c3inv_group (symmetric_group three) c3inv_j
  ≔ path_reflecting_set_embedding (USym c3inv_group) (USym (symmetric_group three)) (usym_set (symmetric_group three))
      (usym_hom c3inv_group (symmetric_group three) c3inv_j) c3inv_usym_j_injective

{` USym j' = USym j ∘ USym α, pointwise. `}
def c3inv_j_prime_usym (g : USym c3inv_group)
  : Id (USym (symmetric_group three)) (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime g)
      (usym_hom c3inv_group (symmetric_group three) c3inv_j (usym_hom c3inv_group c3inv_group c3inv_alpha g))
  ≔ usym_hom_compose c3inv_group c3inv_group (symmetric_group three) c3inv_alpha c3inv_j (refl g)

def c3inv_usym_j_prime_injective : PathReflecting (USym c3inv_group) (USym (symmetric_group three))
    (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime)
  ≔ g h e ↦
    let a ≔ usym_hom c3inv_group c3inv_group c3inv_alpha in
    let jj ≔ usym_hom c3inv_group (symmetric_group three) c3inv_j in
    let ea : Id (USym c3inv_group) (a g) (a h)
      ≔ forget_hom_injective two (a g) (a h)
          (concat (USym (symmetric_group three)) (jj (a g)) (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime g) (jj (a h))
            (inverse (USym (symmetric_group three)) (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime g) (jj (a g))
              (c3inv_j_prime_usym g))
            (concat (USym (symmetric_group three)) (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime g)
              (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime h) (jj (a h)) e (c3inv_j_prime_usym h))) in
    let ei : Id (Fin three) (fin3_swap12 (c3inv_index g)) (fin3_swap12 (c3inv_index h))
      ≔ concat (Fin three) (fin3_swap12 (c3inv_index g)) (c3inv_index (a g)) (fin3_swap12 (c3inv_index h))
          (inverse (Fin three) (c3inv_index (a g)) (fin3_swap12 (c3inv_index g)) (c3inv_alpha_index g))
          (concat (Fin three) (c3inv_index (a g)) (c3inv_index (a h)) (fin3_swap12 (c3inv_index h))
            (refl c3inv_index ea) (c3inv_alpha_index h)) in
    equivalence_injective (USym c3inv_group) (Fin three) (cyclic_group_fin_usym_equiv two) g h
      (calc
        c3inv_index g = fin3_swap12 (fin3_swap12 (c3inv_index g))
          by inverse (Fin three) (fin3_swap12 (fin3_swap12 (c3inv_index g))) (c3inv_index g) (fin3_swap12_involutive (c3inv_index g))
        = fin3_swap12 (fin3_swap12 (c3inv_index h)) by refl fin3_swap12 ei
        = c3inv_index h by fin3_swap12_involutive (c3inv_index h) ∎)

def c3inv_j_prime_mono : IsGroupMono c3inv_group (symmetric_group three) c3inv_j_prime
  ≔ path_reflecting_set_embedding (USym c3inv_group) (USym (symmetric_group three)) (usym_set (symmetric_group three))
      (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime) c3inv_usym_j_prime_injective

{` The generator r_1 (r_1(0) = 1). `}
def c3inv_generator : USym c3inv_group
  ≔ equiv_inverse_map (USym c3inv_group) (Fin three) (cyclic_group_fin_usym_equiv two) fin3_one

{` xca:C3subSG3: USym j ≠ USym j'. `}
def c3inv_usym_differ
  (E : Id (USym c3inv_group → USym (symmetric_group three))
    (usym_hom c3inv_group (symmetric_group three) c3inv_j) (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime))
  : Empty
  ≔ let g ≔ c3inv_generator in
    let a ≔ usym_hom c3inv_group c3inv_group c3inv_alpha in
    let jj ≔ usym_hom c3inv_group (symmetric_group three) c3inv_j in
    let e2 : Id (USym c3inv_group) g (a g)
      ≔ forget_hom_injective two g (a g)
          (concat (USym (symmetric_group three)) (jj g) (usym_hom c3inv_group (symmetric_group three) c3inv_j_prime g) (jj (a g))
            (E (refl g)) (c3inv_j_prime_usym g)) in
    let gi : Id (Fin three) (c3inv_index g) fin3_one ≔ equiv_counit (USym c3inv_group) (Fin three) (cyclic_group_fin_usym_equiv two) fin3_one in
    fin3_two_not_one (calc
      fin3_two = fin3_swap12 fin3_one by refl fin3_two
      = fin3_swap12 (c3inv_index g) by refl fin3_swap12 (inverse (Fin three) (c3inv_index g) fin3_one gi)
      = c3inv_index (a g) by inverse (Fin three) (c3inv_index (a g)) (fin3_swap12 (c3inv_index g)) (c3inv_alpha_index g)
      = c3inv_index g by refl c3inv_index (inverse (USym c3inv_group) g (a g) e2)
      = fin3_one by gi ∎)

def c3inv_j_monomorphism : GroupMonos (symmetric_group three) ≔ (c3inv_group, (c3inv_j, c3inv_j_mono))

def c3inv_j_prime_monomorphism : GroupMonos (symmetric_group three) ≔ (c3inv_group, (c3inv_j_prime, c3inv_j_prime_mono))

def c3inv_homotopy
  : PointedHomotopy (BG c3inv_group) (BG (symmetric_group three))
      (book_pointed_compose (BG c3inv_group) (BG c3inv_group) (BG (symmetric_group three)) (c3inv_alpha_equiv .fst)
        (hom_B c3inv_group (symmetric_group three) c3inv_j))
      (hom_B c3inv_group (symmetric_group three) c3inv_j_prime)
  ≔ let f ≔ hom_B c3inv_group (symmetric_group three) c3inv_j_prime in
    let B ≔ BG (symmetric_group three) in
    (u ↦ refl (f .fst u),
     concat_p1 (B .carrier) (B .point) (f .fst (BG c3inv_group .point)) (f .snd))

{` xca:C3subSG3: (C_3, j') = (C_3, j) in Mono(Σ_3). `}
def c3inv_monos_path : Id (GroupMonos (symmetric_group three)) c3inv_j_prime_monomorphism c3inv_j_monomorphism
  ≔ let K ≔ symmetric_group three in
    let B ≔ BG K in
    map_path (MonoData K) (GroupMonos K) (mono_data_to_mono K)
      (mono_to_mono_data K c3inv_j_prime_monomorphism) (mono_to_mono_data K c3inv_j_monomorphism)
      (subtype_equal (PointedMapsOver B)
        (w ↦ Product (Product (Connected (w .fst .carrier)) (isGroupoid (w .fst .carrier)))
          (IsEmbedding (Loop (w .fst)) (USym K) (loops_map (w .fst) B (w .snd))))
        (mono_data_prop K)
        (mono_to_mono_data K c3inv_j_prime_monomorphism) (mono_to_mono_data K c3inv_j_monomorphism)
        (pointed_over_path B (BG c3inv_group) (BG c3inv_group)
          (hom_B c3inv_group K c3inv_j_prime) (hom_B c3inv_group K c3inv_j) c3inv_alpha_equiv c3inv_homotopy))
