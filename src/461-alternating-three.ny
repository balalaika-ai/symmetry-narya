export "460-sign-counting"

{` Chapter 4, sec:sign-homomorphism: xca:isos_A3_C3. Two isomorphisms
   A_3 → C_3, where C_3 = cyclic_group_fin 2 = Aut_Cyc(Fin 3, s) and A_3 is
   def:alternating-groups (alternating_group_printed 1), and a proof that they
   differ. We construct homomorphisms ψ, ψ' : C_3 → A_3 sending a 3-cycle
   (X, t) to X with the sign ordering of the local ordering that chooses, in
   each pair {x, t(x)}, the target t(x) (ψ) or the source x (ψ'). Their loop
   maps are bijections onto the even permutations (a permutation of Fin 3 is
   even iff it commutes with s), so both are isomorphisms; the requested
   isomorphisms A_3 → C_3 are their inverses. They differ because the
   symmetries ψ(s) and ψ'(s) act on Fin 3 as s and s⁻¹. `}

def c3_cycle : Cycles ≔ finite_fin_cycle two

def c3_succ : Equiv (Fin three) (Fin three) ≔ finite_fin_successor two

def c3_group : Group ≔ cyclic_group_fin two

def a3_group : Group ≔ alternating_group_printed (suc. zero.)

{` Values of the successor of the standard 3-cycle (litmus). `}
def c3_succ_zero : Id (Fin three) (c3_succ .map (inr. star.)) (inl. (inr. star.)) ≔ refl (inl. (inr. star.) : Fin three)

def c3_succ_one : Id (Fin three) (c3_succ .map (inl. (inr. star.))) (inl. (inl. (inr. star.)))
  ≔ refl (inl. (inl. (inr. star.)) : Fin three)

def c3_succ_two : Id (Fin three) (c3_succ .map (inl. (inl. (inr. star.)))) (inr. star.) ≔ refl (inr. star. : Fin three)

{` Distinct elements of Fin 3. `}
def fin3_index (x : Fin three) : Nat
  ≔ match x [
  | inr. _ ↦ zero.
  | inl. (inr. _) ↦ suc. zero.
  | inl. (inl. (inr. _)) ↦ suc. (suc. zero.)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_apart (x y : Fin three) (p : Id (Fin three) x y) : NatCode (fin3_index x) (fin3_index y)
  ≔ nat_encode (fin3_index x) (fin3_index y) (refl fin3_index p)

{` A permutation of Fin 3 is determined by its values (a, b, c) at 0, 1, 2. `}
def fin3_table (a b c : Fin three) : Fin three → Fin three
  ≔ [ inr. _ ↦ a | inl. (inr. _) ↦ b | inl. (inl. (inr. _)) ↦ c | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_table_homotopy (s : Equiv (Fin three) (Fin three)) (a b c : Fin three)
  (qa : Id (Fin three) (s .map (inr. star.)) a) (qb : Id (Fin three) (s .map (inl. (inr. star.))) b)
  (qc : Id (Fin three) (s .map (inl. (inl. (inr. star.)))) c) (x : Fin three)
  : Id (Fin three) (s .map x) (fin3_table a b c x)
  ≔ match x [
  | inr. u ↦ concat (Fin three) (s .map (inr. u)) (s .map (inr. star.)) a (refl (s .map) (inr. (unit_prop u star.) : Id (Fin three) (inr. u) (inr. star.))) qa
  | inl. (inr. u) ↦ concat (Fin three) (s .map (inl. (inr. u))) (s .map (inl. (inr. star.))) b
      (refl (s .map) (inl. (inr. (unit_prop u star.)) : Id (Fin three) (inl. (inr. u)) (inl. (inr. star.)))) qb
  | inl. (inl. (inr. u)) ↦ concat (Fin three) (s .map (inl. (inl. (inr. u)))) (s .map (inl. (inl. (inr. star.)))) c
      (refl (s .map) (inl. (inl. (inr. (unit_prop u star.))) : Id (Fin three) (inl. (inl. (inr. u))) (inl. (inl. (inr. star.))))) qc
  | inl. (inl. (inl. e)) ↦ match e [] ]

def c3_sign_table (s : Equiv (Fin three) (Fin three)) (a b c : Fin three)
  (qa : Id (Fin three) (s .map (inr. star.)) a) (qb : Id (Fin three) (s .map (inl. (inr. star.))) b)
  (qc : Id (Fin three) (s .map (inl. (inl. (inr. star.)))) c)
  : Id Sign (permutation_sign_at three (standard_shape three) s) (bool_sign (nat_odd (inversion_number_fun three (fin3_table a b c))))
  ≔ calc permutation_sign_at three (standard_shape three) s
      = bool_sign (nat_odd (inversion_count three s)) by permutation_sign_at_inversions three s
      = bool_sign (nat_odd (inversion_number three s))
        by refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign) (inversion_count_number three s)
      = bool_sign (nat_odd (inversion_number_fun three (fin3_table a b c)))
        by refl ((f ↦ bool_sign (nat_odd (inversion_number_fun three f))) : (Fin three → Fin three) → Sign)
          (funext (Fin three) (_ ↦ Fin three) (s .map) (fin3_table a b c) (fin3_table_homotopy s a b c qa qb qc)) ∎

def c3_commutes_table (s : Equiv (Fin three) (Fin three)) (a b c : Fin three)
  (qa : Id (Fin three) (s .map (inr. star.)) a) (qb : Id (Fin three) (s .map (inl. (inr. star.))) b)
  (qc : Id (Fin three) (s .map (inl. (inl. (inr. star.)))) c)
  (tc : (x : Fin three) → Id (Fin three) (fin3_table a b c (c3_succ .map x)) (c3_succ .map (fin3_table a b c x)))
  : Commutes (Fin three) (Fin three) c3_succ c3_succ (s .map)
  ≔ x ↦ calc s .map (c3_succ .map x)
      = fin3_table a b c (c3_succ .map x) by fin3_table_homotopy s a b c qa qb qc (c3_succ .map x)
      = c3_succ .map (fin3_table a b c x) by tc x
      = c3_succ .map (s .map x)
        by refl (c3_succ .map) (inverse (Fin three) (s .map x) (fin3_table a b c x) (fin3_table_homotopy s a b c qa qb qc x)) ∎

def c3_table_commutes_OTZ (x : Fin three) : Id (Fin three) (fin3_table (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (c3_succ .map x)) (c3_succ .map (fin3_table (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) x))
  ≔ match x [
  | inr. star. ↦ refl (fin3_table (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (c3_succ .map (inr. star. : Fin three)))
  | inl. (inr. star.) ↦ refl (fin3_table (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (c3_succ .map (inl. (inr. star.) : Fin three)))
  | inl. (inl. (inr. star.)) ↦ refl (fin3_table (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (c3_succ .map (inl. (inl. (inr. star.)) : Fin three)))
  | inl. (inl. (inl. e)) ↦ match e [] ]

def c3_table_commutes_TZO (x : Fin three) : Id (Fin three) (fin3_table (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (c3_succ .map x)) (c3_succ .map (fin3_table (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (inl. (inr. star.) : Fin three) x))
  ≔ match x [
  | inr. star. ↦ refl (fin3_table (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (c3_succ .map (inr. star. : Fin three)))
  | inl. (inr. star.) ↦ refl (fin3_table (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (c3_succ .map (inl. (inr. star.) : Fin three)))
  | inl. (inl. (inr. star.)) ↦ refl (fin3_table (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (c3_succ .map (inl. (inl. (inr. star.)) : Fin three)))
  | inl. (inl. (inl. e)) ↦ match e [] ]

def c3_table_commutes_ZOT (x : Fin three) : Id (Fin three) (fin3_table (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (c3_succ .map x)) (c3_succ .map (fin3_table (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) x))
  ≔ match x [
  | inr. star. ↦ refl (fin3_table (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (c3_succ .map (inr. star. : Fin three)))
  | inl. (inr. star.) ↦ refl (fin3_table (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (c3_succ .map (inl. (inr. star.) : Fin three)))
  | inl. (inl. (inr. star.)) ↦ refl (fin3_table (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (c3_succ .map (inl. (inl. (inr. star.)) : Fin three)))
  | inl. (inl. (inl. e)) ↦ match e [] ]


def c3_classify (s : Equiv (Fin three) (Fin three)) (a b c : Fin three)
  (qa : Id (Fin three) (s .map (inr. star.)) a) (qb : Id (Fin three) (s .map (inl. (inr. star.))) b)
  (qc : Id (Fin three) (s .map (inl. (inl. (inr. star.)))) c)
  : Product (Commutes (Fin three) (Fin three) c3_succ c3_succ (s .map) → Id Sign (permutation_sign_at three (standard_shape three) s) plus.)
      (Id Sign (permutation_sign_at three (standard_shape three) s) plus. → Commutes (Fin three) (Fin three) c3_succ c3_succ (s .map))
  ≔ match a [
  | inr. star. ↦ match b [
    | inr. star. ↦ match c [
      | inr. star. ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inr. star. : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inr. star. : Fin three) qb))) []
      | inl. (inr. star.) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inr. star. : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inr. star. : Fin three) qb))) []
      | inl. (inl. (inr. star.)) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inr. star. : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inr. star. : Fin three) qb))) []
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inr. star.) ↦ match c [
      | inr. star. ↦ match fin3_apart (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inr. star. : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inr. star. : Fin three) qc))) []
      | inl. (inr. star.) ↦ match fin3_apart (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inr. star.) : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qb (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inr. star.) : Fin three) qc))) []
      | inl. (inl. (inr. star.)) ↦ (_ ↦ c3_sign_table s (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) qa qb qc,
           _ ↦ c3_commutes_table s (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) qa qb qc (c3_table_commutes_ZOT))
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inl. (inr. star.)) ↦ match c [
      | inr. star. ↦ match fin3_apart (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inr. star. : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inr. star. : Fin three) qc))) []
      | inl. (inr. star.) ↦ (cm ↦ match fin3_apart (inl. (inl. (inr. star.)) : Fin three) (inl. (inr. star.) : Fin three)
              (calc (inl. (inl. (inr. star.)) : Fin three) = s .map (inl. (inr. star.) : Fin three) by inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) qb
                = c3_succ .map (s .map (inr. star. : Fin three)) by cm (inr. star. : Fin three)
                = c3_succ .map (inr. star. : Fin three) by refl (c3_succ .map) qa ∎) [],
           q ↦ match plus_ne_minus (concat Sign plus. (permutation_sign_at three (standard_shape three) s) minus.
              (inverse Sign (permutation_sign_at three (standard_shape three) s) plus. q) (c3_sign_table s (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (inl. (inr. star.) : Fin three) qa qb qc)) [])
      | inl. (inl. (inr. star.)) ↦ match fin3_apart (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qb (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) qc))) []
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inl. (inl. e)) ↦ match e [] ]
  | inl. (inr. star.) ↦ match b [
    | inr. star. ↦ match c [
      | inr. star. ↦ match fin3_apart (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inr. star. : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qb (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inr. star. : Fin three) qc))) []
      | inl. (inr. star.) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inr. star.) : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inr. star.) : Fin three) qc))) []
      | inl. (inl. (inr. star.)) ↦ (cm ↦ match fin3_apart (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three)
              (calc (inr. star. : Fin three) = s .map (inl. (inr. star.) : Fin three) by inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inr. star. : Fin three) qb
                = c3_succ .map (s .map (inr. star. : Fin three)) by cm (inr. star. : Fin three)
                = c3_succ .map (inl. (inr. star.) : Fin three) by refl (c3_succ .map) qa ∎) [],
           q ↦ match plus_ne_minus (concat Sign plus. (permutation_sign_at three (standard_shape three) s) minus.
              (inverse Sign (permutation_sign_at three (standard_shape three) s) plus. q) (c3_sign_table s (inl. (inr. star.) : Fin three) (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) qa qb qc)) [])
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inr. star.) ↦ match c [
      | inr. star. ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inr. star.) : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inr. star.) : Fin three) qb))) []
      | inl. (inr. star.) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inr. star.) : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inr. star.) : Fin three) qb))) []
      | inl. (inl. (inr. star.)) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inr. star.) : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inr. star.) : Fin three) qb))) []
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inl. (inr. star.)) ↦ match c [
      | inr. star. ↦ (_ ↦ c3_sign_table s (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) qa qb qc,
           _ ↦ c3_commutes_table s (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) qa qb qc (c3_table_commutes_OTZ))
      | inl. (inr. star.) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inr. star.) : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inr. star.) : Fin three) qc))) []
      | inl. (inl. (inr. star.)) ↦ match fin3_apart (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qb (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) qc))) []
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inl. (inl. e)) ↦ match e [] ]
  | inl. (inl. (inr. star.)) ↦ match b [
    | inr. star. ↦ match c [
      | inr. star. ↦ match fin3_apart (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inr. star. : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qb (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inr. star. : Fin three) qc))) []
      | inl. (inr. star.) ↦ (_ ↦ c3_sign_table s (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (inl. (inr. star.) : Fin three) qa qb qc,
           _ ↦ c3_commutes_table s (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) (inl. (inr. star.) : Fin three) qa qb qc (c3_table_commutes_TZO))
      | inl. (inl. (inr. star.)) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inl. (inr. star.)) : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) qc))) []
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inr. star.) ↦ match c [
      | inr. star. ↦ (cm ↦ match fin3_apart (inl. (inr. star.) : Fin three) (inr. star. : Fin three)
              (calc (inl. (inr. star.) : Fin three) = s .map (inl. (inr. star.) : Fin three) by inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inr. star.) : Fin three) qb
                = c3_succ .map (s .map (inr. star. : Fin three)) by cm (inr. star. : Fin three)
                = c3_succ .map (inl. (inl. (inr. star.)) : Fin three) by refl (c3_succ .map) qa ∎) [],
           q ↦ match plus_ne_minus (concat Sign plus. (permutation_sign_at three (standard_shape three) s) minus.
              (inverse Sign (permutation_sign_at three (standard_shape three) s) plus. q) (c3_sign_table s (inl. (inl. (inr. star.)) : Fin three) (inl. (inr. star.) : Fin three) (inr. star. : Fin three) qa qb qc)) [])
      | inl. (inr. star.) ↦ match fin3_apart (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inr. star.) : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qb (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inr. star.) : Fin three) qc))) []
      | inl. (inl. (inr. star.)) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inl. (inr. star.)) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inl. (inr. star.)) : Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) qc))) []
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inl. (inr. star.)) ↦ match c [
      | inr. star. ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inl. (inr. star.)) : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) qb))) []
      | inl. (inr. star.) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inl. (inr. star.)) : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) qb))) []
      | inl. (inl. (inr. star.)) ↦ match fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) (equiv_injective_path (Fin three) (Fin three) s (inr. star. : Fin three) (inl. (inr. star.) : Fin three)
            (concat (Fin three) (s .map (inr. star. : Fin three)) (inl. (inl. (inr. star.)) : Fin three) (s .map (inl. (inr. star.) : Fin three)) qa (inverse (Fin three) (s .map (inl. (inr. star.) : Fin three)) (inl. (inl. (inr. star.)) : Fin three) qb))) []
      | inl. (inl. (inl. e)) ↦ match e [] ]
    | inl. (inl. (inl. e)) ↦ match e [] ]
  | inl. (inl. (inl. e)) ↦ match e [] ]


{` The key fact: a permutation of Fin 3 commutes with the 3-cycle s iff it is even. `}
def c3_commutes_prop (s : Equiv (Fin three) (Fin three)) : isProp (Commutes (Fin three) (Fin three) c3_succ c3_succ (s .map))
  ≔ pi_prop (Fin three) (x ↦ Id (Fin three) (s .map (c3_succ .map x)) (c3_succ .map (s .map x)))
      (x ↦ fin_set three (s .map (c3_succ .map x)) (c3_succ .map (s .map x)))

def c3_commutes_iff_even (s : Equiv (Fin three) (Fin three))
  : Equiv (Commutes (Fin three) (Fin three) c3_succ c3_succ (s .map)) (Id Sign (permutation_sign_at three (standard_shape three) s) plus.)
  ≔ let cl ≔ c3_classify s (s .map (inr. star.)) (s .map (inl. (inr. star.))) (s .map (inl. (inl. (inr. star.))))
      (refl (s .map (inr. star.))) (refl (s .map (inl. (inr. star.)))) (refl (s .map (inl. (inl. (inr. star.))))) in
    iff_equiv (Commutes (Fin three) (Fin three) c3_succ c3_succ (s .map)) (Id Sign (permutation_sign_at three (standard_shape three) s) plus.)
      (c3_commutes_prop s) (sign_set (permutation_sign_at three (standard_shape three) s) plus.) (cl .fst) (cl .snd)

{` A 3-cycle has no points of period two, and of two distinct points one is
   the successor of the other. These properties are propositions and hold
   for the standard 3-cycle, hence for every shape of C_3. `}
def NoTwoPeriodic (X : Type) (t : Equiv X X) : Type ≔ (x : X) → Not (Id X (t .map (t .map x)) x)

def AdjacentPairs (X : Type) (t : Equiv X X) : Type
  ≔ (x y : X) → Not (Id X x y) → Mere (Sum (Id X (t .map x) y) (Id X (t .map y) x))

def TriCycle (X : Type) (t : Equiv X X) : Type ≔ Product (NoTwoPeriodic X t) (AdjacentPairs X t)

def tri_cycle_prop (X : Type) (t : Equiv X X) : isProp (TriCycle X t)
  ≔ product_prop (NoTwoPeriodic X t) (AdjacentPairs X t)
      (pi_prop X (x ↦ Not (Id X (t .map (t .map x)) x)) (x ↦ negation_prop (Id X (t .map (t .map x)) x)))
      (pi_prop X (x ↦ (y : X) → Not (Id X x y) → Mere (Sum (Id X (t .map x) y) (Id X (t .map y) x)))
        (x ↦ pi_prop X (y ↦ Not (Id X x y) → Mere (Sum (Id X (t .map x) y) (Id X (t .map y) x)))
          (y ↦ pi_prop (Not (Id X x y)) (_ ↦ Mere (Sum (Id X (t .map x) y) (Id X (t .map y) x)))
            (_ ↦ mere_isprop (Sum (Id X (t .map x) y) (Id X (t .map y) x))))))
def c3_no_two_periodic : NoTwoPeriodic (Fin three) c3_succ
  ≔ x ↦ match x [
  | inr. star. ↦ p ↦ fin3_apart (inl. (inl. (inr. star.)) : Fin three) (inr. star. : Fin three) p
  | inl. (inr. star.) ↦ p ↦ fin3_apart (inr. star. : Fin three) (inl. (inr. star.) : Fin three) p
  | inl. (inl. (inr. star.)) ↦ p ↦ fin3_apart (inl. (inr. star.) : Fin three) (inl. (inl. (inr. star.)) : Fin three) p
  | inl. (inl. (inl. e)) ↦ match e [] ]

def c3_adjacent : AdjacentPairs (Fin three) c3_succ
  ≔ x y ↦ match x, y [
  | inr. star., inr. star. ↦ n ↦ match n (refl (inr. star. : Fin three)) []
  | inr. star., inl. (inr. star.) ↦ _ ↦ mere (Sum (Id (Fin three) (c3_succ .map (inr. star. : Fin three)) (inl. (inr. star.) : Fin three)) (Id (Fin three) (c3_succ .map (inl. (inr. star.) : Fin three)) (inr. star. : Fin three))) (inl. (refl (inl. (inr. star.) : Fin three)))
  | inr. star., inl. (inl. (inr. star.)) ↦ _ ↦ mere (Sum (Id (Fin three) (c3_succ .map (inr. star. : Fin three)) (inl. (inl. (inr. star.)) : Fin three)) (Id (Fin three) (c3_succ .map (inl. (inl. (inr. star.)) : Fin three)) (inr. star. : Fin three))) (inr. (refl (inr. star. : Fin three)))
  | inl. (inr. star.), inr. star. ↦ _ ↦ mere (Sum (Id (Fin three) (c3_succ .map (inl. (inr. star.) : Fin three)) (inr. star. : Fin three)) (Id (Fin three) (c3_succ .map (inr. star. : Fin three)) (inl. (inr. star.) : Fin three))) (inr. (refl (inl. (inr. star.) : Fin three)))
  | inl. (inr. star.), inl. (inr. star.) ↦ n ↦ match n (refl (inl. (inr. star.) : Fin three)) []
  | inl. (inr. star.), inl. (inl. (inr. star.)) ↦ _ ↦ mere (Sum (Id (Fin three) (c3_succ .map (inl. (inr. star.) : Fin three)) (inl. (inl. (inr. star.)) : Fin three)) (Id (Fin three) (c3_succ .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inr. star.) : Fin three))) (inl. (refl (inl. (inl. (inr. star.)) : Fin three)))
  | inl. (inl. (inr. star.)), inr. star. ↦ _ ↦ mere (Sum (Id (Fin three) (c3_succ .map (inl. (inl. (inr. star.)) : Fin three)) (inr. star. : Fin three)) (Id (Fin three) (c3_succ .map (inr. star. : Fin three)) (inl. (inl. (inr. star.)) : Fin three))) (inl. (refl (inr. star. : Fin three)))
  | inl. (inl. (inr. star.)), inl. (inr. star.) ↦ _ ↦ mere (Sum (Id (Fin three) (c3_succ .map (inl. (inl. (inr. star.)) : Fin three)) (inl. (inr. star.) : Fin three)) (Id (Fin three) (c3_succ .map (inl. (inr. star.) : Fin three)) (inl. (inl. (inr. star.)) : Fin three))) (inr. (refl (inl. (inl. (inr. star.)) : Fin three)))
  | inl. (inl. (inr. star.)), inl. (inl. (inr. star.)) ↦ n ↦ match n (refl (inl. (inl. (inr. star.)) : Fin three)) []
  | inr. star., inl. (inl. (inl. e)) ↦ match e []
  | inl. (inr. star.), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. star.)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. e)), _ ↦ match e [] ]

def c3_tri : TriCycle (Fin three) c3_succ ≔ (c3_no_two_periodic, c3_adjacent)

def bc3_tri (u : NativeComponent Cycles c3_cycle) : TriCycle (u .fst .fst .fst .fst) (u .fst .fst .snd)
  ≔ mere_rec (Id Cycles c3_cycle (u .fst)) (TriCycle (u .fst .fst .fst .fst) (u .fst .fst .snd))
      (tri_cycle_prop (u .fst .fst .fst .fst) (u .fst .fst .snd))
      (p ↦ transport Cycles (c ↦ TriCycle (c .fst .fst .fst) (c .fst .snd)) c3_cycle (u .fst) p c3_tri) (u .snd)

{` The local orderings of a 3-cycle choosing the target, resp. the source, of
   the unique arrow x ↦ t(x) inside each two-element subset. `}
def pair_other (X : Type) (e : TwoSubsets X) (w : SubtypeCarrier X (e .fst)) : SubtypeCarrier X (e .fst)
  ≔ two_element_other (SubtypeCarrier X (e .fst)) (two_subset_two_element X e) w

def TargetChoice (X : Type) (t : Equiv X X) (e : TwoSubsets X) : Type
  ≔ Σ (SubtypeCarrier X (e .fst)) (w ↦ Id X (t .map (pair_other X e w .fst)) (w .fst))

def SourceChoice (X : Type) (t : Equiv X X) (e : TwoSubsets X) : Type
  ≔ Σ (SubtypeCarrier X (e .fst)) (w ↦ Id X (t .map (w .fst)) (pair_other X e w .fst))

def pair_other_fst_ne (X : Type) (e : TwoSubsets X) (w : SubtypeCarrier X (e .fst))
  : Not (Id X (w .fst) (pair_other X e w .fst))
  ≔ p ↦ two_element_other_ne (SubtypeCarrier X (e .fst)) (two_subset_two_element X e) w
      (inverse (SubtypeCarrier X (e .fst)) w (pair_other X e w)
        (subtype_equal X (x ↦ e .fst x .fst) (x ↦ e .fst x .snd) w (pair_other X e w) p))

def pair_choice_fst (X : Type) (t : Equiv X X) (np : NoTwoPeriodic X t) (e : TwoSubsets X)
  (u v : SubtypeCarrier X (e .fst))
  (tu : Id X (t .map (v .fst)) (u .fst)) (tv : Id X (t .map (u .fst)) (v .fst))
  (d : Decidable (Id (SubtypeCarrier X (e .fst)) u v)) : Id (SubtypeCarrier X (e .fst)) u v
  ≔ match d [
  | inl. p ↦ p
  | inr. _ ↦ match np (u .fst) (concat X (t .map (t .map (u .fst))) (t .map (v .fst)) (u .fst) (refl (t .map) tv) tu) [] ]

def target_choice_fst (X : Type) (t : Equiv X X) (np : NoTwoPeriodic X t) (e : TwoSubsets X) (u v : TargetChoice X t e)
  (d : Decidable (Id (SubtypeCarrier X (e .fst)) (u .fst) (v .fst))) : Id (SubtypeCarrier X (e .fst)) (u .fst) (v .fst)
  ≔ match d [
  | inl. p ↦ p
  | inr. n ↦
      let C ≔ SubtypeCarrier X (e .fst) in let h ≔ two_subset_two_element X e in
      let vo : Id C (v .fst) (pair_other X e (u .fst)) ≔ two_element_other_unique C h (u .fst) (v .fst) (r ↦ n (inverse C (v .fst) (u .fst) r)) in
      let uo : Id C (u .fst) (pair_other X e (v .fst)) ≔ two_element_other_unique C h (v .fst) (u .fst) n in
      pair_choice_fst X t np e (u .fst) (v .fst)
        (concat X (t .map (v .fst .fst)) (t .map (pair_other X e (u .fst) .fst)) (u .fst .fst)
          (refl ((c ↦ t .map (c .fst)) : C → X) vo) (u .snd))
        (concat X (t .map (u .fst .fst)) (t .map (pair_other X e (v .fst) .fst)) (v .fst .fst)
          (refl ((c ↦ t .map (c .fst)) : C → X) uo) (v .snd))
        (inr. n) ]

def target_choice_prop (X : Type) (hX : isSet X) (t : Equiv X X) (np : NoTwoPeriodic X t) (e : TwoSubsets X)
  : isProp (TargetChoice X t e)
  ≔ u v ↦ subtype_equal (SubtypeCarrier X (e .fst)) (w ↦ Id X (t .map (pair_other X e w .fst)) (w .fst))
      (w ↦ hX (t .map (pair_other X e w .fst)) (w .fst)) u v
      (target_choice_fst X t np e u v
        (two_element_decidable_equality (SubtypeCarrier X (e .fst)) (two_subset_two_element X e) (u .fst) (v .fst)))

def source_choice_fst (X : Type) (t : Equiv X X) (np : NoTwoPeriodic X t) (e : TwoSubsets X) (u v : SourceChoice X t e)
  (d : Decidable (Id (SubtypeCarrier X (e .fst)) (u .fst) (v .fst))) : Id (SubtypeCarrier X (e .fst)) (u .fst) (v .fst)
  ≔ match d [
  | inl. p ↦ p
  | inr. n ↦
      let C ≔ SubtypeCarrier X (e .fst) in let h ≔ two_subset_two_element X e in
      let vo : Id C (v .fst) (pair_other X e (u .fst)) ≔ two_element_other_unique C h (u .fst) (v .fst) (r ↦ n (inverse C (v .fst) (u .fst) r)) in
      let uo : Id C (u .fst) (pair_other X e (v .fst)) ≔ two_element_other_unique C h (v .fst) (u .fst) n in
      pair_choice_fst X t np e (u .fst) (v .fst)
        (concat X (t .map (v .fst .fst)) (pair_other X e (v .fst) .fst) (u .fst .fst) (v .snd)
          (refl ((c ↦ c .fst) : C → X) (inverse C (u .fst) (pair_other X e (v .fst)) uo)))
        (concat X (t .map (u .fst .fst)) (pair_other X e (u .fst) .fst) (v .fst .fst) (u .snd)
          (refl ((c ↦ c .fst) : C → X) (inverse C (v .fst) (pair_other X e (u .fst)) vo)))
        (inr. n) ]

def source_choice_prop (X : Type) (hX : isSet X) (t : Equiv X X) (np : NoTwoPeriodic X t) (e : TwoSubsets X)
  : isProp (SourceChoice X t e)
  ≔ u v ↦ subtype_equal (SubtypeCarrier X (e .fst)) (w ↦ Id X (t .map (w .fst)) (pair_other X e w .fst))
      (w ↦ hX (t .map (w .fst)) (pair_other X e w .fst)) u v
      (source_choice_fst X t np e u v
        (two_element_decidable_equality (SubtypeCarrier X (e .fst)) (two_subset_two_element X e) (u .fst) (v .fst)))

def target_choice_mere (X : Type) (t : Equiv X X) (adj : AdjacentPairs X t) (e : TwoSubsets X) : Mere (TargetChoice X t e)
  ≔ let C ≔ SubtypeCarrier X (e .fst) in let h ≔ two_subset_two_element X e in
    two_element_point_elim C h (Mere (TargetChoice X t e)) (mere_isprop (TargetChoice X t e))
      (w ↦ let v ≔ pair_other X e w in
        mere_rec (Sum (Id X (t .map (w .fst)) (v .fst)) (Id X (t .map (v .fst)) (w .fst))) (Mere (TargetChoice X t e))
          (mere_isprop (TargetChoice X t e))
          [ inl. q ↦ mere (TargetChoice X t e)
              (v, concat X (t .map (pair_other X e v .fst)) (t .map (w .fst)) (v .fst)
                (refl ((c ↦ t .map (c .fst)) : C → X) (two_element_other_other C h w)) q)
          | inr. q ↦ mere (TargetChoice X t e) (w, q) ]
          (adj (w .fst) (v .fst) (pair_other_fst_ne X e w)))

def source_choice_mere (X : Type) (t : Equiv X X) (adj : AdjacentPairs X t) (e : TwoSubsets X) : Mere (SourceChoice X t e)
  ≔ let C ≔ SubtypeCarrier X (e .fst) in let h ≔ two_subset_two_element X e in
    two_element_point_elim C h (Mere (SourceChoice X t e)) (mere_isprop (SourceChoice X t e))
      (w ↦ let v ≔ pair_other X e w in
        mere_rec (Sum (Id X (t .map (w .fst)) (v .fst)) (Id X (t .map (v .fst)) (w .fst))) (Mere (SourceChoice X t e))
          (mere_isprop (SourceChoice X t e))
          [ inl. q ↦ mere (SourceChoice X t e) (w, q)
          | inr. q ↦ mere (SourceChoice X t e)
              (v, concat X (t .map (v .fst)) (w .fst) (pair_other X e v .fst) q
                (refl ((c ↦ c .fst) : C → X) (inverse C (pair_other X e v) w (two_element_other_other C h w)))) ]
          (adj (w .fst) (v .fst) (pair_other_fst_ne X e w)))

def target_ordering (X : Type) (hX : isSet X) (t : Equiv X X) (tri : TriCycle X t) : LocalOrderingType X
  ≔ e ↦ mere_rec (TargetChoice X t e) (TargetChoice X t e) (target_choice_prop X hX t (tri .fst) e) (w ↦ w)
      (target_choice_mere X t (tri .snd) e) .fst

def source_ordering (X : Type) (hX : isSet X) (t : Equiv X X) (tri : TriCycle X t) : LocalOrderingType X
  ≔ e ↦ mere_rec (SourceChoice X t e) (SourceChoice X t e) (source_choice_prop X hX t (tri .fst) e) (w ↦ w)
      (source_choice_mere X t (tri .snd) e) .fst

{` Shapes of C_3 as 3-element sets, and the classifying maps of ψ and ψ'. `}
def bc3_shape (u : NativeComponent Cycles c3_cycle) : BookFiniteSetsAt three
  ≔ (u .fst .fst .fst,
      mere_rec (Id Cycles c3_cycle (u .fst)) (Mere (Id SetTypes (Fin three, fin_set three) (u .fst .fst .fst)))
        (mere_isprop (Id SetTypes (Fin three, fin_set three) (u .fst .fst .fst)))
        (p ↦ mere (Id SetTypes (Fin three, fin_set three) (u .fst .fst .fst)) (p .fst .fst)) (u .snd))

def bc3_shape_base : Id (BookFiniteSetsAt three) (bc3_shape (component_point Cycles c3_cycle)) (standard_shape three)
  ≔ refl (standard_shape three)

def bsgn_three_transport (A : BookFiniteSetsAt three)
  : Equiv (bsgn three A .fst .fst) (bsgn_quotient (suc. zero.) A .fst .fst)
  ≔ bsigma_two_transport (bsgn three A) (bsgn_quotient (suc. zero.) A) (bsgn_quotient_path (suc. zero.) A)

def bc3_class (u : NativeComponent Cycles c3_cycle) (w : LocalOrderingType (u .fst .fst .fst .fst))
  : bsgn three (bc3_shape u) .fst .fst
  ≔ equiv_inverse_map (bsgn three (bc3_shape u) .fst .fst) (bsgn_quotient (suc. zero.) (bc3_shape u) .fst .fst)
      (bsgn_three_transport (bc3_shape u))
      (parity_class (TwoSubsets (u .fst .fst .fst .fst)) (sign_subsets_finite three (bc3_shape u)) (sign_family three (bc3_shape u)) w)

def bc3_target (u : NativeComponent Cycles c3_cycle) : LocalOrderingType (u .fst .fst .fst .fst)
  ≔ target_ordering (u .fst .fst .fst .fst) (u .fst .fst .fst .snd) (u .fst .fst .snd) (bc3_tri u)

def bc3_source (u : NativeComponent Cycles c3_cycle) : LocalOrderingType (u .fst .fst .fst .fst)
  ≔ source_ordering (u .fst .fst .fst .fst) (u .fst .fst .fst .snd) (u .fst .fst .snd) (bc3_tri u)

def psi_target_map (u : NativeComponent Cycles c3_cycle) : AlternatingShapes three ≔ (bc3_shape u, bc3_class u (bc3_target u))

def psi_source_map (u : NativeComponent Cycles c3_cycle) : AlternatingShapes three ≔ (bc3_shape u, bc3_class u (bc3_source u))

{` Fixed points of the transport along a loop of BΣ_n in the fibers of Bsgn:
   the transport fixes a point iff the loop has sign +1. `}
def bsgn_fixed_sign (n : Nat) (A : BookFiniteSetsAt n) (s : bsgn n A .fst .fst) (p : Id (BookFiniteSetsAt n) A A)
  : Equiv (Id (bsgn n A .fst .fst) (transport (BookFiniteSetsAt n) (B ↦ bsgn n B .fst .fst) A A p s) s)
      (Id Sign (two_loop_sign (bsgn n A) (refl (bsgn n) p)) plus.)
  ≔ let T ≔ bsgn n A in let hT ≔ two_set_two_element T in
    let tt ≔ bsigma_two_transport T T (refl (bsgn n) p) in
    let mv ≔ two_loop_moves T (refl (bsgn n) p) in
    iff_equiv (Id (T .fst .fst) (tt .map s) s) (Id Sign (bool_sign mv) plus.)
      (T .fst .snd (tt .map s) s) (sign_set (bool_sign mv) plus.)
      (r ↦ refl bool_sign
        (concat Bool mv (two_differ (T .fst .fst) hT s (tt .map s)) false.
          (two_moves_value (T .fst .fst) hT tt s)
          (two_differ_eq (T .fst .fst) hT s (tt .map s) (inverse (T .fst .fst) (tt .map s) s r))))
      (q ↦ two_moves_false_fixed (T .fst .fst) hT tt (bool_sign_injective mv false. q) s)

def bc3_point : NativeComponent Cycles c3_cycle ≔ component_point Cycles c3_cycle

def c3_perm_of_loop (p : Id (BookFiniteSetsAt three) (standard_shape three) (standard_shape three)) : Equiv (Fin three) (Fin three)
  ≔ transport_equiv (Fin three) (Fin three) (p .fst .fst)

def c3_loop_is_perm (p : Id (BookFiniteSetsAt three) (standard_shape three) (standard_shape three))
  : Id (Id (BookFiniteSetsAt three) (standard_shape three) (standard_shape three)) p
      (permutation_loop three (standard_shape three) (c3_perm_of_loop p))
  ≔ bsigma_path_ext three (standard_shape three) (standard_shape three) p
      (permutation_loop three (standard_shape three) (c3_perm_of_loop p)) (x ↦ refl (p .fst .fst .trr x))

def c3_cycle_loop (s : Equiv (Fin three) (Fin three)) (comm : Commutes (Fin three) (Fin three) c3_succ c3_succ (s .map))
  : Id (NativeComponent Cycles c3_cycle) bc3_point bc3_point
  ≔ component_path Cycles c3_cycle bc3_point bc3_point
      (equiv_inverse_map (Id Cycles c3_cycle c3_cycle) (PermutationIsomorphisms (c3_cycle .fst) (c3_cycle .fst))
        (cycle_paths_equiv c3_cycle c3_cycle) (s, comm))

{` The underlying permutation of a loop of C_3 (the bridge with cycle_paths_equiv is definitional). `}
def c3_cycle_loop_action (s : Equiv (Fin three) (Fin three)) (comm : Commutes (Fin three) (Fin three) c3_succ c3_succ (s .map))
  (x : Fin three) : Id (Fin three) (c3_cycle_loop s comm .fst .fst .fst .fst .trr x) (s .map x)
  ≔ refl ((r ↦ r .fst .map x) : PermutationIsomorphisms (c3_cycle .fst) (c3_cycle .fst) → Fin three)
      (equiv_counit (Id Cycles c3_cycle c3_cycle) (PermutationIsomorphisms (c3_cycle .fst) (c3_cycle .fst))
        (cycle_paths_equiv c3_cycle c3_cycle) (s, comm))

{` Paths in a Σ-type over a family of sets are determined by their first components. `}
def sigma_set_paths_ext (X : Type) (F : X → Type) (hF : (x : X) → isSet (F x)) (u v : Σ X F) (p q : Id (Σ X F) u v)
  (e : Id (Id X (u .fst) (v .fst)) (p .fst) (q .fst)) : Id (Id (Σ X F) u v) p q
  ≔ refl (sigma_path_pair X F u v)
      (subtype_equal (Id X (u .fst) (v .fst)) (a ↦ Id F a (u .snd) (v .snd))
        (a ↦ retract_prop (Id (F (v .fst)) (transport X F (u .fst) (v .fst) a (u .snd)) (v .snd)) (Id F a (u .snd) (v .snd))
          (hF (v .fst) (transport X F (u .fst) (v .fst) a (u .snd)) (v .snd))
          (equiv_inverse_map (Id F a (u .snd) (v .snd)) (Id (F (v .fst)) (transport X F (u .fst) (v .fst) a (u .snd)) (v .snd))
            (pathover_transport_equiv X F (u .fst) (v .fst) a (u .snd) (v .snd)))
          (pathover_transport_equiv X F (u .fst) (v .fst) a (u .snd) (v .snd) .map)
          (equiv_retraction (Id F a (u .snd) (v .snd)) (Id (F (v .fst)) (transport X F (u .fst) (v .fst) a (u .snd)) (v .snd))
            (pathover_transport_equiv X F (u .fst) (v .fst) a (u .snd) (v .snd))))
        (sigma_path_split X F u v p) (sigma_path_split X F u v q) e)

{` For any choice g of a point of Bsgn over each shape of C_3, the map
   u ↦ (bc3_shape u, g u) is a bijection on loops at the designated shape. `}
def c3_shape_map (g : (u : NativeComponent Cycles c3_cycle) → bsgn three (bc3_shape u) .fst .fst)
  (u : NativeComponent Cycles c3_cycle) : AlternatingShapes three
  ≔ (bc3_shape u, g u)

def c3_loop_even (g : (u : NativeComponent Cycles c3_cycle) → bsgn three (bc3_shape u) .fst .fst)
  (v : Id (AlternatingShapes three) (c3_shape_map g bc3_point) (c3_shape_map g bc3_point))
  : Id Sign (permutation_sign_at three (standard_shape three) (c3_perm_of_loop (v .fst))) plus.
  ≔ let X ≔ BookFiniteSetsAt three in let A0 ≔ standard_shape three in
    let F : X → Type ≔ A ↦ bsgn three A .fst .fst in
    concat Sign (permutation_sign_at three A0 (c3_perm_of_loop (v .fst))) (two_loop_sign (bsgn three A0) (refl (bsgn three) (v .fst))) plus.
      (refl ((q ↦ two_loop_sign (bsgn three A0) (refl (bsgn three) q)) : Id X A0 A0 → Sign)
        (inverse (Id X A0 A0) (v .fst) (permutation_loop three A0 (c3_perm_of_loop (v .fst))) (c3_loop_is_perm (v .fst))))
      (bsgn_fixed_sign three A0 (g bc3_point) (v .fst) .map
        (pathover_transport_equiv X F A0 A0 (v .fst) (g bc3_point) (g bc3_point) .map (v .snd)))

def c3_loop_section (g : (u : NativeComponent Cycles c3_cycle) → bsgn three (bc3_shape u) .fst .fst)
  (v : Id (AlternatingShapes three) (c3_shape_map g bc3_point) (c3_shape_map g bc3_point))
  : Id (NativeComponent Cycles c3_cycle) bc3_point bc3_point
  ≔ c3_cycle_loop (c3_perm_of_loop (v .fst))
      (equiv_inverse_map (Commutes (Fin three) (Fin three) c3_succ c3_succ (c3_perm_of_loop (v .fst) .map))
        (Id Sign (permutation_sign_at three (standard_shape three) (c3_perm_of_loop (v .fst))) plus.)
        (c3_commutes_iff_even (c3_perm_of_loop (v .fst))) (c3_loop_even g v))

def c3_shape_loops_equiv (g : (u : NativeComponent Cycles c3_cycle) → bsgn three (bc3_shape u) .fst .fst)
  : Equiv (Id (NativeComponent Cycles c3_cycle) bc3_point bc3_point)
      (Id (AlternatingShapes three) (c3_shape_map g bc3_point) (c3_shape_map g bc3_point))
  ≔ let X ≔ BookFiniteSetsAt three in let A0 ≔ standard_shape three in
    let F : X → Type ≔ A ↦ bsgn three A .fst .fst in
    let f ≔ c3_shape_map g in
    let BC ≔ NativeComponent Cycles c3_cycle in
    quasi_inverse_equiv (Id BC bc3_point bc3_point) (Id (AlternatingShapes three) (f bc3_point) (f bc3_point))
      (l ↦ refl f l) (c3_loop_section g)
      (l ↦ equiv_injective_path (Id BC bc3_point bc3_point) (Id Cycles c3_cycle c3_cycle)
        (component_path_equiv Cycles c3_cycle bc3_point bc3_point) (c3_loop_section g (refl f l)) l
        (equiv_injective_path (Id Cycles c3_cycle c3_cycle) (PermutationIsomorphisms (c3_cycle .fst) (c3_cycle .fst))
          (cycle_paths_equiv c3_cycle c3_cycle) (c3_loop_section g (refl f l) .fst) (l .fst)
          (subtype_equal (Equiv (Fin three) (Fin three)) (h ↦ Commutes (Fin three) (Fin three) c3_succ c3_succ (h .map))
            (h ↦ c3_commutes_prop h)
            (cycle_paths_equiv c3_cycle c3_cycle .map (c3_loop_section g (refl f l) .fst))
            (cycle_paths_equiv c3_cycle c3_cycle .map (l .fst))
            (equiv_homotopy (Fin three) (Fin three)
              (cycle_paths_equiv c3_cycle c3_cycle .map (c3_loop_section g (refl f l) .fst) .fst)
              (cycle_paths_equiv c3_cycle c3_cycle .map (l .fst) .fst)
              (x ↦ c3_cycle_loop_action (c3_perm_of_loop (refl f l .fst))
                (equiv_inverse_map (Commutes (Fin three) (Fin three) c3_succ c3_succ (c3_perm_of_loop (refl f l .fst) .map))
                  (Id Sign (permutation_sign_at three A0 (c3_perm_of_loop (refl f l .fst))) plus.)
                  (c3_commutes_iff_even (c3_perm_of_loop (refl f l .fst))) (c3_loop_even g (refl f l))) x)))))
      (v ↦ sigma_set_paths_ext X F (A ↦ bsgn three A .fst .snd) (f bc3_point) (f bc3_point) (refl f (c3_loop_section g v)) v
        (bsigma_path_ext three A0 A0 (refl f (c3_loop_section g v) .fst) (v .fst)
          (x ↦ c3_cycle_loop_action (c3_perm_of_loop (v .fst))
            (equiv_inverse_map (Commutes (Fin three) (Fin three) c3_succ c3_succ (c3_perm_of_loop (v .fst) .map))
              (Id Sign (permutation_sign_at three A0 (c3_perm_of_loop (v .fst))) plus.)
              (c3_commutes_iff_even (c3_perm_of_loop (v .fst))) (c3_loop_even g v)) x)))

def c3_shape_map_is_equiv (g : (u : NativeComponent Cycles c3_cycle) → bsgn three (bc3_shape u) .fst .fst)
  : BookIsEquiv (NativeComponent Cycles c3_cycle) (AlternatingShapes three) (c3_shape_map g)
  ≔ native_connected_map_equiv_from_loops (NativeComponent Cycles c3_cycle) (AlternatingShapes three) (c3_shape_map g)
      (bg_connected c3_group) (alternating_shapes_connected (suc. zero.)) bc3_point
      (book_equivalence (Id (NativeComponent Cycles c3_cycle) bc3_point bc3_point)
        (Id (AlternatingShapes three) (c3_shape_map g bc3_point) (c3_shape_map g bc3_point)) (c3_shape_loops_equiv g) .equiv)
      .equiv

{` Parities of the target and source orderings of the standard 3-cycle against
   the standard local ordering: in a pair i < j the target is j iff s(i) = j,
   which happens for {0,1} and {1,2} (even), the source for {0,2} only (odd). `}
def fin_eq_bool (n : Nat) (x y : Fin n) : Bool ≔ bool_not (decision_differ (Id (Fin n) x y) (fin_decidable_equality n x y))

def fin_eq_bool_true (n : Nat) (x y : Fin n) (d : Decidable (Id (Fin n) x y)) (q : Id Bool (bool_not (decision_differ (Id (Fin n) x y) d)) true.)
  : Id (Fin n) x y
  ≔ decision_differ_false (Id (Fin n) x y) d (bool_not_true_false (decision_differ (Id (Fin n) x y) d) q)

def fin_eq_bool_false (n : Nat) (x y : Fin n) (d : Decidable (Id (Fin n) x y)) (q : Id Bool (bool_not (decision_differ (Id (Fin n) x y) d)) false.)
  : Not (Id (Fin n) x y)
  ≔ decision_differ_true (Id (Fin n) x y) d (bool_not_false_true (decision_differ (Id (Fin n) x y) d) q)

def c3_choice_case (tri : TriCycle (Fin three) c3_succ) (e : TwoSubsets (Fin three)) (h' : TwoElement (two_subset_carrier three e))
  (b : Bool) (qb : Id Bool (fin_eq_bool three (c3_succ .map (two_subset_min three e .fst)) (two_subset_max three e .fst)) b)
  : Product
      (Id Bool (two_differ (two_subset_carrier three e) h' (target_ordering (Fin three) (fin_set three) c3_succ tri e) (two_subset_min three e))
        (fin_eq_bool three (c3_succ .map (two_subset_min three e .fst)) (two_subset_max three e .fst)))
      (Id Bool (two_differ (two_subset_carrier three e) h' (source_ordering (Fin three) (fin_set three) c3_succ tri e) (two_subset_min three e))
        (bool_not (fin_eq_bool three (c3_succ .map (two_subset_min three e .fst)) (two_subset_max three e .fst))))
  ≔ let X ≔ Fin three in let t ≔ c3_succ in
    let C ≔ two_subset_carrier three e in let h ≔ two_subset_two_element X e in
    let mn ≔ two_subset_min three e in let mx ≔ two_subset_max three e in
    let eb ≔ fin_eq_bool three (t .map (mn .fst)) (mx .fst) in
    let mo : Id C (pair_other X e mx) mn ≔ two_element_other_other C h mn in
    let nmm : Not (Id C mx mn) ≔ p ↦ two_element_other_ne C h mn p in
    let tw ≔ target_ordering X (fin_set three) t tri e in
    let sw ≔ source_ordering X (fin_set three) t tri e in
    let tunique : (w : C) → Id X (t .map (pair_other X e w .fst)) (w .fst) → Id C tw w
      ≔ w r ↦ refl ((u ↦ u .fst) : TargetChoice X t e → C)
          (target_choice_prop X (fin_set three) t (tri .fst) e
            (mere_rec (TargetChoice X t e) (TargetChoice X t e) (target_choice_prop X (fin_set three) t (tri .fst) e) (u ↦ u)
              (target_choice_mere X t (tri .snd) e)) (w, r)) in
    let sunique : (w : C) → Id X (t .map (w .fst)) (pair_other X e w .fst) → Id C sw w
      ≔ w r ↦ refl ((u ↦ u .fst) : SourceChoice X t e → C)
          (source_choice_prop X (fin_set three) t (tri .fst) e
            (mere_rec (SourceChoice X t e) (SourceChoice X t e) (source_choice_prop X (fin_set three) t (tri .fst) e) (u ↦ u)
              (source_choice_mere X t (tri .snd) e)) (w, r)) in
    match b [
    | true. ↦
        let tmn : Id X (t .map (mn .fst)) (mx .fst)
          ≔ fin_eq_bool_true three (t .map (mn .fst)) (mx .fst) (fin_decidable_equality three (t .map (mn .fst)) (mx .fst)) qb in
        (calc two_differ C h' tw mn
            = two_differ C h' mx mn by refl ((w ↦ two_differ C h' w mn) : C → Bool)
                (tunique mx (concat X (t .map (pair_other X e mx .fst)) (t .map (mn .fst)) (mx .fst)
                  (refl ((u ↦ t .map (u .fst)) : C → X) mo) tmn))
            = true. by two_differ_ne C h' mx mn nmm
            = eb by inverse Bool eb true. qb ∎,
         calc two_differ C h' sw mn
            = two_differ C h' mn mn by refl ((w ↦ two_differ C h' w mn) : C → Bool) (sunique mn tmn)
            = false. by two_differ_refl C h' mn
            = bool_not eb by refl bool_not (inverse Bool eb true. qb) ∎)
    | false. ↦
        let ntmn : Not (Id X (t .map (mn .fst)) (mx .fst))
          ≔ fin_eq_bool_false three (t .map (mn .fst)) (mx .fst) (fin_decidable_equality three (t .map (mn .fst)) (mx .fst)) qb in
        let goal ≔ Product
          (Id Bool (two_differ C h' tw mn) eb) (Id Bool (two_differ C h' sw mn) (bool_not eb)) in
        mere_rec (Sum (Id X (t .map (mn .fst)) (mx .fst)) (Id X (t .map (mx .fst)) (mn .fst))) goal
          (product_prop (Id Bool (two_differ C h' tw mn) eb) (Id Bool (two_differ C h' sw mn) (bool_not eb))
            (bool_set (two_differ C h' tw mn) eb) (bool_set (two_differ C h' sw mn) (bool_not eb)))
          [ inl. r ↦ match ntmn r []
          | inr. r ↦
            (calc two_differ C h' tw mn
                = two_differ C h' mn mn by refl ((w ↦ two_differ C h' w mn) : C → Bool) (tunique mn r)
                = false. by two_differ_refl C h' mn
                = eb by inverse Bool eb false. qb ∎,
             calc two_differ C h' sw mn
                = two_differ C h' mx mn by refl ((w ↦ two_differ C h' w mn) : C → Bool)
                    (sunique mx (concat X (t .map (mx .fst)) (mn .fst) (pair_other X e mx .fst) r
                      (refl ((u ↦ u .fst) : C → X) (inverse C (pair_other X e mx) mn mo))))
                = true. by two_differ_ne C h' mx mn nmm
                = bool_not eb by refl bool_not (inverse Bool eb false. qb) ∎) ]
          (tri .snd (mn .fst) (mx .fst) (fin_lt_ne three (mn .fst) (mx .fst) (two_subset_min_lt_max three e))) ]

def c3_choice_differ (tri : TriCycle (Fin three) c3_succ) (e : TwoSubsets (Fin three)) (h' : TwoElement (two_subset_carrier three e))
  : Product
      (Id Bool (two_differ (two_subset_carrier three e) h' (target_ordering (Fin three) (fin_set three) c3_succ tri e) (two_subset_min three e))
        (fin_eq_bool three (c3_succ .map (two_subset_min three e .fst)) (two_subset_max three e .fst)))
      (Id Bool (two_differ (two_subset_carrier three e) h' (source_ordering (Fin three) (fin_set three) c3_succ tri e) (two_subset_min three e))
        (bool_not (fin_eq_bool three (c3_succ .map (two_subset_min three e .fst)) (two_subset_max three e .fst))))
  ≔ c3_choice_case tri e h' (fin_eq_bool three (c3_succ .map (two_subset_min three e .fst)) (two_subset_max three e .fst))
      (refl (fin_eq_bool three (c3_succ .map (two_subset_min three e .fst)) (two_subset_max three e .fst)))

def c3_target_parity (hE : IsFinite (TwoSubsets (Fin three))) (tri : TriCycle (Fin three) c3_succ)
  : Id Bool (parity_odd (TwoSubsets (Fin three)) hE (two_subset_bsigma (Fin three) (fin_set three))
      (target_ordering (Fin three) (fin_set three) c3_succ tri) (standard_local_ordering three)) false.
  ≔ let E ≔ TwoSubsets (Fin three) in let P ≔ two_subset_bsigma (Fin three) (fin_set three) in
    let w ≔ target_ordering (Fin three) (fin_set three) c3_succ tri in
    calc parity_odd E hE P w (standard_local_ordering three)
      = nat_odd (finite_true_count E hE (parity_differ E P w (standard_local_ordering three)))
        by parity_odd_count E hE P w (standard_local_ordering three)
      = nat_odd (finite_true_count E hE (d ↦ fin_eq_bool three (c3_succ .map (two_subset_min three d .fst)) (two_subset_max three d .fst)))
        by refl nat_odd (finite_true_count_homotopy E hE (parity_differ E P w (standard_local_ordering three))
          (d ↦ fin_eq_bool three (c3_succ .map (two_subset_min three d .fst)) (two_subset_max three d .fst))
          (d ↦ c3_choice_differ tri d (two_set_two_element (P d)) .fst))
      = nat_odd (fin_nat_sum three (i ↦ true_count three (j ↦ bool_and (fin_lt three i j) (fin_eq_bool three (c3_succ .map i) j))))
        by refl nat_odd (two_subsets_pair_count three hE (i j ↦ fin_eq_bool three (c3_succ .map i) j))
      = false. by refl (false. : Bool) ∎

def c3_source_parity (hE : IsFinite (TwoSubsets (Fin three))) (tri : TriCycle (Fin three) c3_succ)
  : Id Bool (parity_odd (TwoSubsets (Fin three)) hE (two_subset_bsigma (Fin three) (fin_set three))
      (source_ordering (Fin three) (fin_set three) c3_succ tri) (standard_local_ordering three)) true.
  ≔ let E ≔ TwoSubsets (Fin three) in let P ≔ two_subset_bsigma (Fin three) (fin_set three) in
    let w ≔ source_ordering (Fin three) (fin_set three) c3_succ tri in
    calc parity_odd E hE P w (standard_local_ordering three)
      = nat_odd (finite_true_count E hE (parity_differ E P w (standard_local_ordering three)))
        by parity_odd_count E hE P w (standard_local_ordering three)
      = nat_odd (finite_true_count E hE (d ↦ bool_not (fin_eq_bool three (c3_succ .map (two_subset_min three d .fst)) (two_subset_max three d .fst))))
        by refl nat_odd (finite_true_count_homotopy E hE (parity_differ E P w (standard_local_ordering three))
          (d ↦ bool_not (fin_eq_bool three (c3_succ .map (two_subset_min three d .fst)) (two_subset_max three d .fst)))
          (d ↦ c3_choice_differ tri d (two_set_two_element (P d)) .snd))
      = nat_odd (fin_nat_sum three (i ↦ true_count three (j ↦ bool_and (fin_lt three i j) (bool_not (fin_eq_bool three (c3_succ .map i) j)))))
        by refl nat_odd (two_subsets_pair_count three hE (i j ↦ bool_not (fin_eq_bool three (c3_succ .map i) j)))
      = true. by refl (true. : Bool) ∎

{` The pointings of ψ and ψ'. ψ(sh) is the designated shape itself; ψ'(sh)
   carries the other sign ordering and is joined to it by the transposition
   (1 2), which reverses the 3-cycle. `}
def c3_designated_value_path (w : LocalOrderingType (Fin three))
  (q : Id Bool (parity_odd (TwoSubsets (Fin three)) (sign_subsets_finite three (standard_shape three))
      (two_subset_bsigma (Fin three) (fin_set three)) w (standard_local_ordering three)) false.)
  : Id (bsgn three (standard_shape three) .fst .fst) (alternating_point_value three) (bc3_class bc3_point w)
  ≔ let A0 ≔ standard_shape three in
    let E ≔ TwoSubsets (Fin three) in let hE ≔ sign_subsets_finite three A0 in let P ≔ two_subset_bsigma (Fin three) (fin_set three) in
    let H ≔ bsgn_three_transport A0 in
    equiv_injective_path (bsgn three A0 .fst .fst) (bsgn_quotient (suc. zero.) A0 .fst .fst) H (alternating_point_value three) (bc3_class bc3_point w)
      (calc H .map (alternating_point_value three)
          = parity_class E hE P (standard_local_ordering three) by alternating_point_standard (suc. zero.)
        = parity_class E hE P w by parity_class_path E hE P (standard_local_ordering three) w
            (concat Bool (parity_odd E hE P (standard_local_ordering three) w) (parity_odd E hE P w (standard_local_ordering three)) false.
              (parity_odd_symm E hE P (standard_local_ordering three) w) q)
        = H .map (bc3_class bc3_point w)
          by inverse (bsgn_quotient (suc. zero.) A0 .fst .fst) (H .map (bc3_class bc3_point w)) (parity_class E hE P w)
            (equiv_counit (bsgn three A0 .fst .fst) (bsgn_quotient (suc. zero.) A0 .fst .fst) H (parity_class E hE P w)) ∎)

def psi_target_point : Id (AlternatingShapes three) (alternating_point three) (psi_target_map bc3_point)
  ≔ let X ≔ BookFiniteSetsAt three in let A0 ≔ standard_shape three in
    let F : X → Type ≔ A ↦ bsgn three A .fst .fst in
    let s1 ≔ bc3_class bc3_point (bc3_target bc3_point) in
    (refl A0, pathover_of_eq X F A0 A0 (refl A0) (alternating_point_value three) s1
      (concat (F A0) (transport X F A0 A0 (refl A0) (alternating_point_value three)) (alternating_point_value three) s1
        (transport_refl X F A0 (alternating_point_value three))
        (c3_designated_value_path (bc3_target bc3_point) (c3_target_parity (sign_subsets_finite three A0) (bc3_tri bc3_point)))))

def fin3_swap12_sign : Id Sign (permutation_sign_at three (standard_shape three) fin3_swap12_equiv) minus.
  ≔ c3_sign_table fin3_swap12_equiv (fin3_swap12_equiv .map (inr. star.)) (fin3_swap12_equiv .map (inl. (inr. star.)))
      (fin3_swap12_equiv .map (inl. (inl. (inr. star.))))
      (refl (fin3_swap12_equiv .map (inr. star.))) (refl (fin3_swap12_equiv .map (inl. (inr. star.))))
      (refl (fin3_swap12_equiv .map (inl. (inl. (inr. star.)))))

def psi_source_point : Id (AlternatingShapes three) (alternating_point three) (psi_source_map bc3_point)
  ≔ let X ≔ BookFiniteSetsAt three in let A0 ≔ standard_shape three in
    let F : X → Type ≔ A ↦ bsgn three A .fst .fst in
    let hT ≔ two_set_two_element (bsgn three A0) in
    let E ≔ TwoSubsets (Fin three) in let hE ≔ sign_subsets_finite three A0 in let P ≔ two_subset_bsigma (Fin three) (fin_set three) in
    let s0 ≔ alternating_point_value three in
    let s1 ≔ bc3_class bc3_point (bc3_source bc3_point) in
    let tau ≔ permutation_loop three A0 fin3_swap12_equiv in
    let moved : Not (Id (F A0) (transport X F A0 A0 tau s0) s0)
      ≔ r ↦ plus_ne_minus (concat Sign plus. (permutation_sign_at three A0 fin3_swap12_equiv) minus.
          (inverse Sign (permutation_sign_at three A0 fin3_swap12_equiv) plus. (bsgn_fixed_sign three A0 s0 tau .map r))
          fin3_swap12_sign) in
    let other : Not (Id (F A0) s1 s0)
      ≔ r ↦ bool_encode true. false.
          (calc (true. : Bool) = parity_odd E hE P (bc3_source bc3_point) (standard_local_ordering three)
              by inverse Bool (parity_odd E hE P (bc3_source bc3_point) (standard_local_ordering three)) true.
                (c3_source_parity hE (bc3_tri bc3_point))
            = false. by parity_class_path_odd E hE P (bc3_source bc3_point) (standard_local_ordering three)
                (calc parity_class E hE P (bc3_source bc3_point)
                    = bsgn_three_transport A0 .map s1
                      by inverse (bsgn_quotient (suc. zero.) A0 .fst .fst) (bsgn_three_transport A0 .map s1) (parity_class E hE P (bc3_source bc3_point))
                        (equiv_counit (F A0) (bsgn_quotient (suc. zero.) A0 .fst .fst) (bsgn_three_transport A0) (parity_class E hE P (bc3_source bc3_point)))
                  = bsgn_three_transport A0 .map s0 by refl (bsgn_three_transport A0 .map) r
                  = parity_class E hE P (standard_local_ordering three) by alternating_point_standard (suc. zero.) ∎) ∎) in
    (tau, pathover_of_eq X F A0 A0 tau s0 s1
      (two_element_ne_ne (F A0) hT (transport X F A0 A0 tau s0) s0 s1 moved other))

{` The homomorphisms ψ, ψ' : C_3 → A_3 and the fact that they are isomorphisms. `}
def psi_target_hom : GroupHom c3_group a3_group ≔ mkhom c3_group a3_group (psi_target_map, psi_target_point)

def psi_source_hom : GroupHom c3_group a3_group ≔ mkhom c3_group a3_group (psi_source_map, psi_source_point)

def psi_target_iso : GroupIso c3_group a3_group
  ≔ (psi_target_hom, c3_shape_map_is_equiv (u ↦ bc3_class u (bc3_target u)))

def psi_source_iso : GroupIso c3_group a3_group
  ≔ (psi_source_hom, c3_shape_map_is_equiv (u ↦ bc3_class u (bc3_source u)))

{` xca:isos_A3_C3: two isomorphisms A_3 → C_3 (the inverses of ψ and ψ'). `}
def a3_c3_target_iso : GroupIso a3_group c3_group
  ≔ group_path_iso_equiv a3_group c3_group .map
      (inverse Group c3_group a3_group (group_path_from_iso c3_group a3_group psi_target_iso))

def a3_c3_source_iso : GroupIso a3_group c3_group
  ≔ group_path_iso_equiv a3_group c3_group .map
      (inverse Group c3_group a3_group (group_path_from_iso c3_group a3_group psi_source_iso))

{` The generator s of C_3 and the action of ψ(s), ψ'(s) on 0 ∈ Fin 3. `}
def c3_generator : USym c3_group ≔ c3_cycle_loop c3_succ (x ↦ refl (c3_succ .map (c3_succ .map x)))

def a3_action_zero (w : USym a3_group) : Fin three
  ≔ transport (AlternatingShapes three) (u ↦ u .fst .fst .fst) (alternating_point three) (alternating_point three) w (inr. star.)

def conjugate_transport (X : Type) (B : X → Type) (a x : X) (c : Id X a x) (l : Id X x x) (y : B a)
  : Id (B a) (transport X B a a (pointed_loop_conjugate X a x c l) y)
      (transport X B x a (inverse X a x c) (transport X B x x l (transport X B a x c y)))
  ≔ concat (B a) (transport X B a a (pointed_loop_conjugate X a x c l) y)
      (transport X B x a (concat X x x a l (inverse X a x c)) (transport X B a x c y))
      (transport X B x a (inverse X a x c) (transport X B x x l (transport X B a x c y)))
      (transport_concat X B a x a c (concat X x x a l (inverse X a x c)) y)
      (transport_concat X B x x a l (inverse X a x c) (transport X B a x c y))

def psi_target_action : Id (Fin three) (a3_action_zero (usym_hom c3_group a3_group psi_target_hom c3_generator)) (inl. (inr. star.))
  ≔ let S ≔ AlternatingShapes three in let B : S → Type ≔ u ↦ u .fst .fst .fst in
    let pt ≔ alternating_point three in let y ≔ psi_target_map bc3_point in
    let c ≔ psi_target_point in let l ≔ refl psi_target_map c3_generator in
    calc a3_action_zero (usym_hom c3_group a3_group psi_target_hom c3_generator)
      = transport S B y pt (inverse S pt y c) (transport S B y y l (transport S B pt y c (inr. star.)))
        by conjugate_transport S B pt y c l (inr. star.)
      = transport S B y pt (inverse S pt y c) (transport S B y y l (inr. star.))
        by refl ((z ↦ transport S B y pt (inverse S pt y c) (transport S B y y l z)) : Fin three → Fin three)
          (transport_refl (BookFiniteSetsAt three) (A ↦ A .fst .fst) (standard_shape three) (inr. star.))
      = transport S B y pt (inverse S pt y c) (inl. (inr. star.))
        by refl (transport S B y pt (inverse S pt y c)) (c3_cycle_loop_action c3_succ (x ↦ refl (c3_succ .map (c3_succ .map x))) (inr. star.))
      = inl. (inr. star.)
        by concat (Fin three) (transport S B y pt (inverse S pt y c) (inl. (inr. star.)))
          (transport S B y pt (inverse S pt y c) (transport S B pt y c (inl. (inr. star.)))) (inl. (inr. star.))
          (refl (transport S B y pt (inverse S pt y c))
            (inverse (Fin three) (transport S B pt y c (inl. (inr. star.))) (inl. (inr. star.))
              (transport_refl (BookFiniteSetsAt three) (A ↦ A .fst .fst) (standard_shape three) (inl. (inr. star.)))))
          (transport_inverse_roundtrip S B pt y c (inl. (inr. star.))) ∎

def psi_source_action : Id (Fin three) (a3_action_zero (usym_hom c3_group a3_group psi_source_hom c3_generator)) (inl. (inl. (inr. star.)))
  ≔ let S ≔ AlternatingShapes three in let B : S → Type ≔ u ↦ u .fst .fst .fst in
    let pt ≔ alternating_point three in let y ≔ psi_source_map bc3_point in
    let c ≔ psi_source_point in let l ≔ refl psi_source_map c3_generator in
    calc a3_action_zero (usym_hom c3_group a3_group psi_source_hom c3_generator)
      = transport S B y pt (inverse S pt y c) (transport S B y y l (transport S B pt y c (inr. star.)))
        by conjugate_transport S B pt y c l (inr. star.)
      = transport S B y pt (inverse S pt y c) (inl. (inr. star.))
        by refl (transport S B y pt (inverse S pt y c)) (c3_cycle_loop_action c3_succ (x ↦ refl (c3_succ .map (c3_succ .map x))) (inr. star.))
      = transport S B y pt (inverse S pt y c) (transport S B pt y c (inl. (inl. (inr. star.))))
        by refl (transport S B y pt (inverse S pt y c)) (refl (inl. (inr. star.) : Fin three))
      = inl. (inl. (inr. star.)) by transport_inverse_roundtrip S B pt y c (inl. (inl. (inr. star.))) ∎

{` The two isomorphisms are different. `}
def a3_c3_isos_differ (p : Id (GroupIso a3_group c3_group) a3_c3_target_iso a3_c3_source_iso) : Empty
  ≔ let G ≔ c3_group in let H ≔ a3_group in
    let P ≔ group_path_from_iso G H psi_target_iso in let P' ≔ group_path_from_iso G H psi_source_iso in
    let q1 : Id (Id Group H G) (inverse Group G H P) (inverse Group G H P')
      ≔ equiv_injective_path (Id Group H G) (GroupIso H G) (group_path_iso_equiv H G) (inverse Group G H P) (inverse Group G H P') p in
    let q2 : Id (Id Group G H) P P'
      ≔ calc P = inverse Group H G (inverse Group G H P) by inverse (Id Group G H) (inverse Group H G (inverse Group G H P)) P (inverse_inverse Group G H P)
          = inverse Group H G (inverse Group G H P') by refl (inverse Group H G) q1
          = P' by inverse_inverse Group G H P' ∎ in
    let q3 : Id (GroupIso G H) psi_target_iso psi_source_iso
      ≔ calc psi_target_iso = group_path_iso_equiv G H .map P
            by inverse (GroupIso G H) (group_path_iso_equiv G H .map P) psi_target_iso (equiv_counit (Id Group G H) (GroupIso G H) (group_path_iso_equiv G H) psi_target_iso)
          = group_path_iso_equiv G H .map P' by refl (group_path_iso_equiv G H .map) q2
          = psi_source_iso by equiv_counit (Id Group G H) (GroupIso G H) (group_path_iso_equiv G H) psi_source_iso ∎ in
    let q5 : Id (Fin three) (a3_action_zero (usym_hom G H psi_target_hom c3_generator)) (a3_action_zero (usym_hom G H psi_source_hom c3_generator))
      ≔ refl ((f ↦ a3_action_zero (usym_hom G H (f .fst) c3_generator)) : GroupIso G H → Fin three) q3 in
    fin3_apart (inl. (inr. star.)) (inl. (inl. (inr. star.)))
      (calc (inl. (inr. star.) : Fin three) = a3_action_zero (usym_hom G H psi_target_hom c3_generator)
          by inverse (Fin three) (a3_action_zero (usym_hom G H psi_target_hom c3_generator)) (inl. (inr. star.)) psi_target_action
        = a3_action_zero (usym_hom G H psi_source_hom c3_generator) by q5
        = inl. (inl. (inr. star.)) by psi_source_action ∎)
