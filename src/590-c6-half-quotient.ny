export "589-c4-bit-fixed-free"

{` exa:C3subC6 (part 1): the C_6-set F(X, t) = X/2 and the subgroup (F, [0]).

   C_6 = Aut_Cyc(Fin 6, s) = cyclic_group_fin 5. F maps a cycle (X, t) to the
   quotient X/2 of X by the orbit relation of t^2 (ModQuotient 1, chapter 3,
   sec:mthroot), as a C_6-set. Here: the action on classes,
   π · [k] = [π(k)] (c6half_act_class); [i] = [j] iff i and j have the same
   parity (c6half_class_path_equiv); the symmetries picked out by [0] are those
   with π(0) even, i.e. the even powers of s (c6half_picks_out_zero), likewise
   for [1], and π · [0] = [1] iff π(0) is odd (footnote); X/2 has decidable
   equality (claim after def:decidable-subgroup). The subgroup itself and its
   underlying group ≅ C_3 are in module 591. `}

def c6half_five : Nat ≔ suc. (suc. (suc. (suc. (suc. zero.))))

def c6half_six : Nat ≔ suc. c6half_five

{` C_6 = Aut_Cyc(Fin 6, s). `}
def c6half_group : Group ≔ cyclic_group_fin c6half_five

def c6half_cycle : Cycles ≔ finite_fin_cycle c6half_five

def C6Pos : Type ≔ Fin c6half_six

def c6half_succ (x : C6Pos) : C6Pos ≔ finite_fin_successor c6half_five .map x

def c6half_q0 : C6Pos ≔ inr. star.
def c6half_q1 : C6Pos ≔ inl. (inr. star.)
def c6half_q2 : C6Pos ≔ inl. (inl. (inr. star.))
def c6half_q3 : C6Pos ≔ inl. (inl. (inl. (inr. star.)))
def c6half_q4 : C6Pos ≔ inl. (inl. (inl. (inl. (inr. star.))))
def c6half_q5 : C6Pos ≔ inl. (inl. (inl. (inl. (inl. (inr. star.)))))

def c6half_pos_ind (P : C6Pos → Type) (h0 : P c6half_q0) (h1 : P c6half_q1) (h2 : P c6half_q2)
  (h3 : P c6half_q3) (h4 : P c6half_q4) (h5 : P c6half_q5) (i : C6Pos) : P i
  ≔ match i [
  | inr. star. ↦ h0
  | inl. (inr. star.) ↦ h1
  | inl. (inl. (inr. star.)) ↦ h2
  | inl. (inl. (inl. (inr. star.))) ↦ h3
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ h4
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ h5
  | inl. (inl. (inl. (inl. (inl. (inl. (e)))))) ↦ match e [] ]

{` X/2 for a cycle (X, t): the quotient of X by the orbit relation of t^2. `}
def c6half_quotient (c : Cycles) : SetTypes
  ≔ (ModQuotient (suc. zero.) (c .fst .fst .fst) (c .fst .snd),
     quotient_set (c .fst .fst .fst) (mod_relation (suc. zero.) (c .fst .fst .fst) (c .fst .snd)))

{` exa:C3subC6: F : BC_6 → Set, F(X, t) ≔ X/2. `}
def c6half_gset : GSet c6half_group ≔ z ↦ c6half_quotient (z .fst)

def C6Half : Type ≔ gset_underlying c6half_group c6half_gset

def c6half_rel : EquivalenceRelation C6Pos ≔ mod_relation (suc. zero.) C6Pos (finite_fin_successor c6half_five)

{` The class [k] of k : Fin 6 in Fin 6 / 2. `}
def c6half_class (k : C6Pos) : C6Half ≔ quotient_class C6Pos c6half_rel k

{` The evaluation g ↦ g(0) of cor:id-m-cycle and the carrier permutation. `}
def c6half_index (g : USym c6half_group) : C6Pos ≔ cyclic_group_fin_usym_equiv c6half_five .map g

def c6half_carrier (g : USym c6half_group) (k : C6Pos) : C6Pos ≔ g .fst .fst .fst .fst .trr k

{` F on symmetries: π · [k] = [π(k)]. `}
def c6half_act_class (g : USym c6half_group) (k : C6Pos)
  : Id C6Half (gset_usym_act c6half_group c6half_gset g (c6half_class k)) (c6half_class (c6half_carrier g k))
  ≔ quotient_cycle_ap_evaluate (suc. zero.) (BG c6half_group .carrier) (u ↦ u .fst) (shape c6half_group) (shape c6half_group) g k

def c6half_carrier_succ (g : USym c6half_group) (k : C6Pos)
  : Id C6Pos (c6half_carrier g (c6half_succ k)) (c6half_succ (c6half_carrier g k))
  ≔ cycle_paths_equiv c6half_cycle c6half_cycle .map (g .fst) .snd k

{` Parity on Fin 6 (0 ↦ bit 0, 1 ↦ bit 1, ...). `}
def c6half_par (k : C6Pos) : Fin two
  ≔ c6half_pos_ind (_ ↦ Fin two) bits4_o bits4_l bits4_o bits4_l bits4_o bits4_l k

def c6half_flip (b : Fin two) : Fin two ≔ bits4_bit_ind (_ ↦ Fin two) bits4_l bits4_o b

def c6half_par_succ (k : C6Pos) : Id (Fin two) (c6half_par (c6half_succ k)) (c6half_flip (c6half_par k))
  ≔ c6half_pos_ind (j ↦ Id (Fin two) (c6half_par (c6half_succ j)) (c6half_flip (c6half_par j)))
      (refl bits4_l) (refl bits4_o) (refl bits4_l) (refl bits4_o) (refl bits4_l) (refl bits4_o) k

def c6half_mod_step (k : C6Pos)
  : Id (Fin two) (c6half_par (mod_power (suc. zero.) C6Pos (finite_fin_successor c6half_five) .map k)) (c6half_par k)
  ≔ c6half_pos_ind (j ↦ Id (Fin two) (c6half_par (mod_power (suc. zero.) C6Pos (finite_fin_successor c6half_five) .map j))
        (c6half_par j))
      (refl bits4_o) (refl bits4_l) (refl bits4_o) (refl bits4_l) (refl bits4_o) (refl bits4_l) k

def c6half_iterate_identity (B : Type) (n : Nat) (y : B) : Id B (iterate B (identity B) n y) y
  ≔ match n [ zero. ↦ refl y | suc. k ↦ c6half_iterate_identity B k y ]

def c6half_power_identity (B : Type) (z : Int) (y : B) : Id B (permutation_power B (identity_equiv B) z y) y
  ≔ match z [ pos. n ↦ c6half_iterate_identity B n y | neg. n ↦ c6half_iterate_identity B (suc. n) y ]

{` Related elements have the same parity. `}
def c6half_rel_par (x y : C6Pos) (r : Rel C6Pos c6half_rel x y) : Id (Fin two) (c6half_par x) (c6half_par y)
  ≔ let M ≔ mod_power (suc. zero.) C6Pos (finite_fin_successor c6half_five) in
    mere_rec (OrbitWitness C6Pos M x y) (Id (Fin two) (c6half_par x) (c6half_par y))
      (fin_set two (c6half_par x) (c6half_par y))
      (w ↦ calc
        c6half_par x
        = permutation_power (Fin two) (identity_equiv (Fin two)) (w .fst) (c6half_par x)
          by inverse (Fin two) (permutation_power (Fin two) (identity_equiv (Fin two)) (w .fst) (c6half_par x)) (c6half_par x)
               (c6half_power_identity (Fin two) (w .fst) (c6half_par x))
        = c6half_par (permutation_power C6Pos M (w .fst) x)
          by inverse (Fin two) (c6half_par (permutation_power C6Pos M (w .fst) x))
               (permutation_power (Fin two) (identity_equiv (Fin two)) (w .fst) (c6half_par x))
               (permutation_power_intertwine C6Pos (Fin two) M (identity_equiv (Fin two)) c6half_par c6half_mod_step (w .fst) x)
        = c6half_par y by refl c6half_par (inverse C6Pos y (permutation_power C6Pos M (w .fst) x) (w .snd)) ∎) r

def c6half_rep (b : Fin two) : C6Pos ≔ bits4_bit_ind (_ ↦ C6Pos) c6half_q0 c6half_q1 b

def c6half_step_rel (k : C6Pos) (n : Nat) (y : C6Pos)
  (e : Id C6Pos y (permutation_power C6Pos (mod_power (suc. zero.) C6Pos (finite_fin_successor c6half_five)) (pos. n) k))
  : Id C6Half (c6half_class k) (c6half_class y)
  ≔ quotient_encode C6Pos c6half_rel k y
      (mere (OrbitWitness C6Pos (mod_power (suc. zero.) C6Pos (finite_fin_successor c6half_five)) k y) (pos. n, e))

{` [k] = [rep(par k)]: every class is [0] or [1]. `}
def c6half_class_rep (k : C6Pos) : Id C6Half (c6half_class k) (c6half_class (c6half_rep (c6half_par k)))
  ≔ c6half_pos_ind (j ↦ Id C6Half (c6half_class j) (c6half_class (c6half_rep (c6half_par j))))
      (refl (c6half_class c6half_q0)) (refl (c6half_class c6half_q1))
      (inverse C6Half (c6half_class c6half_q0) (c6half_class c6half_q2)
        (c6half_step_rel c6half_q0 (suc. zero.) c6half_q2 (refl c6half_q2)))
      (inverse C6Half (c6half_class c6half_q1) (c6half_class c6half_q3)
        (c6half_step_rel c6half_q1 (suc. zero.) c6half_q3 (refl c6half_q3)))
      (inverse C6Half (c6half_class c6half_q0) (c6half_class c6half_q4)
        (c6half_step_rel c6half_q0 (suc. (suc. zero.)) c6half_q4 (refl c6half_q4)))
      (inverse C6Half (c6half_class c6half_q1) (c6half_class c6half_q5)
        (c6half_step_rel c6half_q1 (suc. (suc. zero.)) c6half_q5 (refl c6half_q5))) k

{` [i] = [j] iff i and j have the same parity. `}
def c6half_class_path_equiv (i j : C6Pos)
  : Equiv (Id C6Half (c6half_class i) (c6half_class j)) (Id (Fin two) (c6half_par i) (c6half_par j))
  ≔ iff_equiv (Id C6Half (c6half_class i) (c6half_class j)) (Id (Fin two) (c6half_par i) (c6half_par j))
      (quotient_set C6Pos c6half_rel (c6half_class i) (c6half_class j)) (fin_set two (c6half_par i) (c6half_par j))
      (p ↦ c6half_rel_par i j (quotient_effective C6Pos c6half_rel i j .map p))
      (e ↦ calc
        c6half_class i = c6half_class (c6half_rep (c6half_par i)) by c6half_class_rep i
        = c6half_class (c6half_rep (c6half_par j))
          by refl ((b ↦ c6half_class (c6half_rep b)) : Fin two → C6Half) e
        = c6half_class j
          by inverse C6Half (c6half_class j) (c6half_class (c6half_rep (c6half_par j))) (c6half_class_rep j) ∎)

{` g · [k] = [m] iff g(k) and m have the same parity. `}
def c6half_act_equiv (g : USym c6half_group) (k m : C6Pos)
  : Equiv (Id C6Half (gset_usym_act c6half_group c6half_gset g (c6half_class k)) (c6half_class m))
      (Id (Fin two) (c6half_par (c6half_carrier g k)) (c6half_par m))
  ≔ let gk ≔ gset_usym_act c6half_group c6half_gset g (c6half_class k) in
    iff_equiv (Id C6Half gk (c6half_class m)) (Id (Fin two) (c6half_par (c6half_carrier g k)) (c6half_par m))
      (quotient_set C6Pos c6half_rel gk (c6half_class m)) (fin_set two (c6half_par (c6half_carrier g k)) (c6half_par m))
      (p ↦ c6half_class_path_equiv (c6half_carrier g k) m .map
        (concat C6Half (c6half_class (c6half_carrier g k)) gk (c6half_class m)
          (inverse C6Half gk (c6half_class (c6half_carrier g k)) (c6half_act_class g k)) p))
      (e ↦ concat C6Half gk (c6half_class (c6half_carrier g k)) (c6half_class m) (c6half_act_class g k)
        (equiv_inverse_map (Id C6Half (c6half_class (c6half_carrier g k)) (c6half_class m))
          (Id (Fin two) (c6half_par (c6half_carrier g k)) (c6half_par m))
          (c6half_class_path_equiv (c6half_carrier g k) m) e))

def c6half_flip_equiv (a b : Fin two) : Equiv (Id (Fin two) (c6half_flip a) b) (Id (Fin two) a (c6half_flip b))
  ≔ iff_equiv (Id (Fin two) (c6half_flip a) b) (Id (Fin two) a (c6half_flip b))
      (fin_set two (c6half_flip a) b) (fin_set two a (c6half_flip b))
      (p ↦ concat (Fin two) a (c6half_flip (c6half_flip a)) (c6half_flip b)
        (bits4_bit_ind (a' ↦ Id (Fin two) a' (c6half_flip (c6half_flip a'))) (refl bits4_o) (refl bits4_l) a)
        (refl c6half_flip p))
      (p ↦ concat (Fin two) (c6half_flip a) (c6half_flip (c6half_flip b)) b
        (refl c6half_flip p)
        (bits4_bit_ind (b' ↦ Id (Fin two) (c6half_flip (c6half_flip b')) b') (refl bits4_o) (refl bits4_l) b))

{` exa:C3subC6: the symmetries picked out by [0] are those with π(0) even
   (the even powers of s, by cor:id-m-cycle). `}
def c6half_picks_out_zero (g : USym c6half_group)
  : Equiv (Id C6Half (gset_usym_act c6half_group c6half_gset g (c6half_class c6half_q0)) (c6half_class c6half_q0))
      (Id (Fin two) (c6half_par (c6half_index g)) bits4_o)
  ≔ c6half_act_equiv g c6half_q0 c6half_q0

{` Footnote: the same symmetries are picked out by [1]; and π · [0] = [1],
   π · [1] = [0] hold iff π(0) is odd (the other inscribed triangle). `}
def c6half_picks_out_one (g : USym c6half_group)
  : Equiv (Id C6Half (gset_usym_act c6half_group c6half_gset g (c6half_class c6half_q1)) (c6half_class c6half_q1))
      (Id (Fin two) (c6half_par (c6half_index g)) bits4_o)
  ≔ compose_equiv (Id C6Half (gset_usym_act c6half_group c6half_gset g (c6half_class c6half_q1)) (c6half_class c6half_q1))
      (Id (Fin two) (c6half_par (c6half_carrier g c6half_q1)) bits4_l)
      (Id (Fin two) (c6half_par (c6half_index g)) bits4_o)
      (c6half_act_equiv g c6half_q1 c6half_q1)
      (transport (Fin two) (b ↦ Equiv (Id (Fin two) b bits4_l) (Id (Fin two) (c6half_par (c6half_index g)) bits4_o))
        (c6half_flip (c6half_par (c6half_index g))) (c6half_par (c6half_carrier g c6half_q1))
        (inverse (Fin two) (c6half_par (c6half_carrier g c6half_q1)) (c6half_flip (c6half_par (c6half_index g)))
          (concat (Fin two) (c6half_par (c6half_carrier g c6half_q1)) (c6half_par (c6half_succ (c6half_index g)))
            (c6half_flip (c6half_par (c6half_index g)))
            (refl c6half_par (c6half_carrier_succ g c6half_q0)) (c6half_par_succ (c6half_index g))))
        (c6half_flip_equiv (c6half_par (c6half_index g)) bits4_l))

def c6half_moves_zero_to_one (g : USym c6half_group)
  : Equiv (Id C6Half (gset_usym_act c6half_group c6half_gset g (c6half_class c6half_q0)) (c6half_class c6half_q1))
      (Id (Fin two) (c6half_par (c6half_index g)) bits4_l)
  ≔ c6half_act_equiv g c6half_q0 c6half_q1

def c6half_moves_one_to_zero (g : USym c6half_group)
  : Equiv (Id C6Half (gset_usym_act c6half_group c6half_gset g (c6half_class c6half_q1)) (c6half_class c6half_q0))
      (Id (Fin two) (c6half_par (c6half_index g)) bits4_l)
  ≔ compose_equiv (Id C6Half (gset_usym_act c6half_group c6half_gset g (c6half_class c6half_q1)) (c6half_class c6half_q0))
      (Id (Fin two) (c6half_par (c6half_carrier g c6half_q1)) bits4_o)
      (Id (Fin two) (c6half_par (c6half_index g)) bits4_l)
      (c6half_act_equiv g c6half_q1 c6half_q0)
      (transport (Fin two) (b ↦ Equiv (Id (Fin two) b bits4_o) (Id (Fin two) (c6half_par (c6half_index g)) bits4_l))
        (c6half_flip (c6half_par (c6half_index g))) (c6half_par (c6half_carrier g c6half_q1))
        (inverse (Fin two) (c6half_par (c6half_carrier g c6half_q1)) (c6half_flip (c6half_par (c6half_index g)))
          (concat (Fin two) (c6half_par (c6half_carrier g c6half_q1)) (c6half_par (c6half_succ (c6half_index g)))
            (c6half_flip (c6half_par (c6half_index g)))
            (refl c6half_par (c6half_carrier_succ g c6half_q0)) (c6half_par_succ (c6half_index g))))
        (c6half_flip_equiv (c6half_par (c6half_index g)) bits4_o))

{` def:decidable-subgroup claim: Fin 6 / 2 has decidable equality. `}
def c6half_rel_decidable : DecidableRelation C6Pos c6half_rel
  ≔ x y ↦ match fin_decidable_equality two (c6half_par x) (c6half_par y) [
  | inl. e ↦ inl. (quotient_effective C6Pos c6half_rel x y .map
      (equiv_inverse_map (Id C6Half (c6half_class x) (c6half_class y)) (Id (Fin two) (c6half_par x) (c6half_par y))
        (c6half_class_path_equiv x y) e))
  | inr. n ↦ inr. (r ↦ n (c6half_rel_par x y r)) ]

def c6half_decidable_equality : DecidableEquality C6Half
  ≔ quotient_decidable_equality C6Pos c6half_rel c6half_rel_decidable

{` Litmus: r_2 (any g with g(0) = 2) fixes [0]; [1] ≠ [0]. `}
def c6half_litmus_class_two : Id C6Half (c6half_class c6half_q2) (c6half_class c6half_q0)
  ≔ c6half_class_rep c6half_q2

def c6half_litmus_one_not_zero (p : Id C6Half (c6half_class c6half_q1) (c6half_class c6half_q0)) : Empty
  ≔ sum_encode (Fin (suc. zero.)) Unit (inl. (inr. star.)) (inr. star.) (c6half_class_path_equiv c6half_q1 c6half_q0 .map p)
