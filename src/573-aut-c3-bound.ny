export "1011-cyclic-group-homs"
export "709-groups-are-abstract-groups"
export "412-symmetric-group-two"

{` Chapter 5 (actions.tex), xca:AutC3, first step: Aut(C_3) has at most two
   symmetries. Its symmetries are the identifications C_3 = C_3
   (group_aut_usym_paths, module 423); we give an injection of
   Id Group C C into Fin 2 for C = cyclic_group 3 (≡ cyclic_group (suc. two),
   module 404; it is identified with the literal C_3 = cyclic_group_fin two by
   cyclic_group_fin_path).

   Method: Id Group C C ≃ AbstractIso (abstr C) (abstr C) (thm:Groupsareidentitytypes,
   modules 702/709). An abstract automorphism φ is determined by φ(gen), since
   every symmetry is gen^k (cyclic_symmetry_power_index, module 1011) and
   φ(gen^k) = φ(gen)^k; φ(gen) ≠ e because φ is injective and gen ≠ e. So
   φ(gen) = gen^k with k ∈ {1, 2}, and k determines φ. Imports chapter 7
   (709) and chapter 10 (1011) modules. `}

def autc3 : Group ≔ cyclic_group three

def autc3_gen : USym autc3 ≔ cyclic_group_generator two

def AutC3Iso : Type ≔ AbstractIso (abstr autc3) (abstr autc3)

{` Id Group C C ≃ AbstractIso (abstr C) (abstr C). `}
def autc3_abstract_iso_equiv : Equiv (Id Group autc3 autc3) AutC3Iso
  ≔ compose_equiv (Id Group autc3 autc3) (Id AbstractGroup (abstr autc3) (abstr autc3)) AutC3Iso
      (equivalence_on_paths Group AbstractGroup group_abstract_group_equiv autc3 autc3)
      (abstract_group_path_iso_equiv (abstr autc3) (abstr autc3))

def autc3_iso_unit (φ : AutC3Iso) : Id (USym autc3) (φ .fst .map (usym_unit autc3)) (usym_unit autc3)
  ≔ abstract_hom_preserves_unit (abstr autc3) (abstr autc3) (φ .fst .map) (φ .snd)

{` φ(g^n) = φ(g)^n. `}
def autc3_iso_power (φ : AutC3Iso) (g : USym autc3) (n : Nat)
  : Id (USym autc3) (φ .fst .map (usym_power autc3 g n)) (usym_power autc3 (φ .fst .map g) n)
  ≔ match n [
  | zero. ↦ autc3_iso_unit φ
  | suc. n ↦ concat (USym autc3) (φ .fst .map (usym_mul autc3 g (usym_power autc3 g n)))
      (usym_mul autc3 (φ .fst .map g) (φ .fst .map (usym_power autc3 g n)))
      (usym_mul autc3 (φ .fst .map g) (usym_power autc3 (φ .fst .map g) n))
      (φ .snd g (usym_power autc3 g n))
      (refl (usym_mul autc3 (φ .fst .map g)) (autc3_iso_power φ g n)) ]

{` An automorphism is determined by the image of the generator. `}
def autc3_iso_pointwise (φ ψ : AutC3Iso)
  (e : Id (USym autc3) (φ .fst .map autc3_gen) (ψ .fst .map autc3_gen)) (t : USym autc3)
  : Id (USym autc3) (φ .fst .map t) (ψ .fst .map t)
  ≔ let w ≔ cyclic_symmetry_power_index two t in
    let gk ≔ usym_power autc3 autc3_gen (w .fst) in
    calc
      φ .fst .map t = φ .fst .map gk by refl (φ .fst .map) (inverse (USym autc3) gk t (w .snd .snd))
      = usym_power autc3 (φ .fst .map autc3_gen) (w .fst) by autc3_iso_power φ autc3_gen (w .fst)
      = usym_power autc3 (ψ .fst .map autc3_gen) (w .fst)
        by refl ((x ↦ usym_power autc3 x (w .fst)) : USym autc3 → USym autc3) e
      = ψ .fst .map gk
        by inverse (USym autc3) (ψ .fst .map gk) (usym_power autc3 (ψ .fst .map autc3_gen) (w .fst))
          (autc3_iso_power ψ autc3_gen (w .fst))
      = ψ .fst .map t by refl (ψ .fst .map) (w .snd .snd) ∎

def autc3_iso_determined (φ ψ : AutC3Iso)
  (e : Id (USym autc3) (φ .fst .map autc3_gen) (ψ .fst .map autc3_gen)) : Id AutC3Iso φ ψ
  ≔ subtype_equal (Equiv (USym autc3) (USym autc3)) (f ↦ IsAbstractHom (abstr autc3) (abstr autc3) (f .map))
      (f ↦ is_abstract_hom_prop (abstr autc3) (abstr autc3) (f .map)) φ ψ
      (equiv_path (USym autc3) (USym autc3) (φ .fst) (ψ .fst)
        (funext (USym autc3) (_ ↦ USym autc3) (φ .fst .map) (ψ .fst .map) (autc3_iso_pointwise φ ψ e)))

{` gen ≠ e, hence φ(gen) ≠ e. `}
def autc3_gen_nontrivial (p : Id (USym autc3) autc3_gen (usym_unit autc3)) : Empty
  ≔ cyclic_group_generator_powers_nontrivial two (suc. zero.) (lt_to_book zero. (suc. zero.) star.)
      (lt_to_book (suc. zero.) three star.)
      (concat (USym autc3) (usym_power autc3 autc3_gen (suc. zero.)) autc3_gen (usym_unit autc3)
        (usym_power_one autc3 autc3_gen) p)

def autc3_iso_gen_nontrivial (φ : AutC3Iso) (p : Id (USym autc3) (φ .fst .map autc3_gen) (usym_unit autc3)) : Empty
  ≔ autc3_gen_nontrivial
      (equivalence_injective (USym autc3) (USym autc3) (φ .fst) autc3_gen (usym_unit autc3)
        (concat (USym autc3) (φ .fst .map autc3_gen) (usym_unit autc3) (φ .fst .map (usym_unit autc3)) p
          (inverse (USym autc3) (φ .fst .map (usym_unit autc3)) (usym_unit autc3) (autc3_iso_unit φ))))

{` φ(gen) = gen^k with 0 < k < 3. `}
def autc3_iso_index (φ : AutC3Iso)
  : Σ Nat (k ↦ Product (BookLt k three) (Id (USym autc3) (usym_power autc3 autc3_gen k) (φ .fst .map autc3_gen)))
  ≔ cyclic_symmetry_power_index two (φ .fst .map autc3_gen)

def autc3_iso_index_nonzero (φ : AutC3Iso) (p : Id Nat (autc3_iso_index φ .fst) zero.) : Empty
  ≔ let w ≔ autc3_iso_index φ in
    autc3_iso_gen_nontrivial φ
      (concat (USym autc3) (φ .fst .map autc3_gen) (usym_power autc3 autc3_gen (w .fst)) (usym_unit autc3)
        (inverse (USym autc3) (usym_power autc3 autc3_gen (w .fst)) (φ .fst .map autc3_gen) (w .snd .snd))
        (refl ((k ↦ usym_power autc3 autc3_gen k) : Nat → USym autc3) p))

{` 1 ↦ 0, 2 ↦ 1 (other values do not occur). `}
def autc3_index_class (k : Nat) : Fin two
  ≔ match k [ zero. ↦ fin2_one | suc. zero. ↦ fin2_zero | suc. (suc. _) ↦ fin2_one ]

def autc3_one_ne_two (k : Nat) (hk : Lt k three)
  (e : Id (Fin two) fin2_zero (autc3_index_class k)) (h : Id Nat k zero. → Empty)
  : Id Nat (suc. zero.) k
  ≔ match k [
  | zero. ↦ match h (refl (zero. : Nat)) []
  | suc. zero. ↦ refl (suc. zero. : Nat)
  | suc. (suc. zero.) ↦ match fin2_zero_ne_one e []
  | suc. (suc. (suc. _)) ↦ match hk [] ]

def autc3_two_ne_one (k : Nat) (hk : Lt k three)
  (e : Id (Fin two) fin2_one (autc3_index_class k)) (h : Id Nat k zero. → Empty)
  : Id Nat (suc. (suc. zero.)) k
  ≔ match k [
  | zero. ↦ match h (refl (zero. : Nat)) []
  | suc. zero. ↦ match fin2_zero_ne_one (inverse (Fin two) fin2_one fin2_zero e) []
  | suc. (suc. zero.) ↦ refl (suc. (suc. zero.) : Nat)
  | suc. (suc. (suc. _)) ↦ match hk [] ]

def autc3_index_class_injective (k k' : Nat) (hk : Lt k three) (h : Id Nat k zero. → Empty)
  (hk' : Lt k' three) (h' : Id Nat k' zero. → Empty)
  (e : Id (Fin two) (autc3_index_class k) (autc3_index_class k')) : Id Nat k k'
  ≔ match k [
  | zero. ↦ match h (refl (zero. : Nat)) []
  | suc. zero. ↦ autc3_one_ne_two k' hk' e h'
  | suc. (suc. zero.) ↦ autc3_two_ne_one k' hk' e h'
  | suc. (suc. (suc. _)) ↦ match hk [] ]

{` The injection Id Group C C → Fin 2. `}
def autc3_path_class (p : Id Group autc3 autc3) : Fin two
  ≔ autc3_index_class (autc3_iso_index (autc3_abstract_iso_equiv .map p) .fst)

def autc3_path_class_injective : PathReflecting (Id Group autc3 autc3) (Fin two) autc3_path_class
  ≔ p p' e ↦
    let φ ≔ autc3_abstract_iso_equiv .map p in
    let ψ ≔ autc3_abstract_iso_equiv .map p' in
    let w ≔ autc3_iso_index φ in
    let w' ≔ autc3_iso_index ψ in
    let kk : Id Nat (w .fst) (w' .fst)
      ≔ autc3_index_class_injective (w .fst) (w' .fst) (lt_from_book (w .fst) three (w .snd .fst))
          (autc3_iso_index_nonzero φ) (lt_from_book (w' .fst) three (w' .snd .fst)) (autc3_iso_index_nonzero ψ) e in
    equivalence_injective (Id Group autc3 autc3) AutC3Iso autc3_abstract_iso_equiv p p'
      (autc3_iso_determined φ ψ
        (calc
          φ .fst .map autc3_gen = usym_power autc3 autc3_gen (w .fst)
            by inverse (USym autc3) (usym_power autc3 autc3_gen (w .fst)) (φ .fst .map autc3_gen) (w .snd .snd)
          = usym_power autc3 autc3_gen (w' .fst) by refl (usym_power autc3 autc3_gen) kk
          = ψ .fst .map autc3_gen by w' .snd .snd ∎))

{` H = H injects into Fin 2 ("Aut(H) has at most two symmetries"). `}
def GroupAutAtMostTwo (H : Group) : Type
  ≔ Σ (Id Group H H → Fin two) (ι ↦ PathReflecting (Id Group H H) (Fin two) ι)

def cyclic_three_aut_at_most_two : GroupAutAtMostTwo (cyclic_group three)
  ≔ (autc3_path_class, autc3_path_class_injective)

def group_aut_at_most_two_transfer (H K : Group) (p : Id Group H K) (h : GroupAutAtMostTwo K) : GroupAutAtMostTwo H
  ≔ transport Group GroupAutAtMostTwo K H (inverse Group H K p) h

{` For the literal C_3 = Aut_Cyc(Fin 3, s). `}
def cyclic_fin_three_aut_at_most_two : GroupAutAtMostTwo (cyclic_group_fin two)
  ≔ group_aut_at_most_two_transfer (cyclic_group_fin two) (cyclic_group three) (cyclic_group_fin_path two)
      cyclic_three_aut_at_most_two
