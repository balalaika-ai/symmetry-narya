{` Bridges for chapter 5, blind file 02-subgroups: exa:C3subC6, the symmetries picked out by (X/2, [0])
   are exactly the even powers of s. Ours (c6half_picks_out_zero) says "π(0) is even"; here the blind form is
   derived from the action π·[k] = [π(k)] and the relation of X/2 (x ~ y iff y = s^{2r}(x)). `}
export "bridge-02b-subgroup-examples"

{` The carrier permutation of s^k is the k-th power of the successor (cor:id-m-cycle). `}
def bridge_cyc_power_trr (n : Nat) (k : Int) (x : Fin (suc. n))
  : Id (Fin (suc. n)) (cycle_group_power (finite_fin_cycle n) k .fst .fst .fst .fst .trr x)
      (permutation_power (Fin (suc. n)) (finite_fin_successor n) k x)
  ≔ let c ≔ finite_fin_cycle n in
    let g ≔ cycle_group_power c k in
    let lp ≔ loop_power Cycles c (cycle_generating_loop c) k in
    concat (Fin (suc. n)) (g .fst .fst .fst .fst .trr x) (cycle_path_evaluate c c (g .fst) x)
      (permutation_power (Fin (suc. n)) (finite_fin_successor n) k x)
      (inverse (Fin (suc. n)) (cycle_path_evaluate c c (g .fst) x) (g .fst .fst .fst .fst .trr x) (cycle_path_evaluate_transport c c (g .fst) x))
      (concat (Fin (suc. n)) (cycle_path_evaluate c c (g .fst) x) (cycle_path_evaluate c c lp x)
         (permutation_power (Fin (suc. n)) (finite_fin_successor n) k x)
         (refl ((l ↦ cycle_path_evaluate c c l x) : Id Cycles c c → Fin (suc. n))
           (map_loop_power (NativeComponent Cycles c) Cycles (u ↦ u .fst) (component_point Cycles c) (cycle_group_generator c) k))
         (cycle_generator_power_eval c k x))

def bridge_c3c6_picked_out : blind_c3c6_picked_out
  ≔ π ↦
    let S ≔ C6Pos in
    let R ≔ c6half_rel in
    let s ≔ finite_fin_successor c6half_five in
    let c ≔ finite_fin_cycle c6half_five in
    let q0 : C6Pos ≔ inr. star. in
    let two' : Int ≔ pos. (suc. (suc. zero.)) in
    let pw : Int → USym c6half_group ≔ k ↦ cycle_group_power c (int_mul two' k) in
    let car ≔ c6half_carrier π in
    let E ≔ cyclic_group_fin_usym_equiv c6half_five in
    let W ≔ ModWitness (suc. zero.) S s q0 (car q0) in
    let K ≔ Σ Int (k ↦ Id (USym c6half_group) π (pw k)) in
    (h ↦
       let e1 : Id C6Half (c6half_class (car q0)) (c6half_class q0)
         ≔ concat C6Half (c6half_class (car q0)) (gset_usym_act c6half_group c6half_gset π (c6half_class q0)) (c6half_class q0)
             (inverse C6Half (gset_usym_act c6half_group c6half_gset π (c6half_class q0)) (c6half_class (car q0)) (c6half_act_class π q0))
             h in
       let r : Rel S R q0 (car q0) ≔ R .symmetric (car q0) q0 (quotient_effective S R (car q0) q0 .map e1) in
       mere_rec W (Mere K) (mere_isprop K)
         (v ↦ mere K (v .fst,
           equivalence_injective (USym c6half_group) (Fin c6half_six) E π (pw (v .fst))
             (concat (Fin c6half_six) (E .map π) (permutation_power S s (int_mul two' (v .fst)) q0) (E .map (pw (v .fst)))
               (v .snd)
               (inverse (Fin c6half_six) (E .map (pw (v .fst))) (permutation_power S s (int_mul two' (v .fst)) q0)
                 (bridge_cyc_power_trr c6half_five (int_mul two' (v .fst)) q0)))))
         (mod_relation_book (suc. zero.) S s q0 (car q0) .map r),
     m ↦ mere_rec K (Id C6Half (gset_usym_act c6half_group c6half_gset π (c6half_class q0)) (c6half_class q0))
       (quotient_set S R (gset_usym_act c6half_group c6half_gset π (c6half_class q0)) (c6half_class q0))
       (v ↦ concat C6Half (gset_usym_act c6half_group c6half_gset π (c6half_class q0)) (c6half_class (car q0)) (c6half_class q0)
          (c6half_act_class π q0)
          (inverse C6Half (c6half_class q0) (c6half_class (car q0))
            (quotient_encode S R q0 (car q0)
              (equiv_inverse_map (Rel S R q0 (car q0)) (Mere W) (mod_relation_book (suc. zero.) S s q0 (car q0))
                (mere W (v .fst,
                  concat S (car q0) (c6half_carrier (pw (v .fst)) q0) (permutation_power S s (int_mul two' (v .fst)) q0)
                    (refl ((g ↦ c6half_carrier g q0) : USym c6half_group → S) (v .snd))
                    (bridge_cyc_power_trr c6half_five (int_mul two' (v .fst)) q0)))))))
       m)
