export "481-cayley-bicycles"

{` Exercise at group.tex 2303. The two pictured 6-element bicycles, read off
   the TikZ code:
   - the hexagon: nodes n0..n5 = 0..5 of Fin 6, a = (0 1)(2 3)(4 5) and
     b = (1 2)(3 4)(5 0) (both drawn in both directions);
   - the prism: inner nodes x_k = inl k and outer nodes y_k = inr k of
     Fin 3 ⊔ Fin 3, a(x_k) = x_{k−1}, a(y_k) = y_{k+1} (arrows x_n → x_p and
     y_p → y_n for p/n ∈ {0/1, 1/2, 2/0}), b swaps x_k and y_k.
   Both are Cayley bicycles of Σ₃ (module 481): the prism for the generators
   (0 1 2), (1 2), the hexagon for (0 1), (1 2). Hence both automorphism
   groups are identified with Σ₃ = symmetric_group 3, and with each other.
   The identification of Σ₃'s symmetries with Fin 3 ⊔ Fin 3 is the
   classification of the six permutations of Fin 3 (by their values at 0, 1). `}

def bicycle_six : Nat ≔ suc. (suc. (suc. (suc. (suc. (suc. zero.)))))

{` The permutation of Fin 3 named by w : Fin 3 ⊔ Fin 3 (values at 0, 1, 2):
   x₀ = id, x₁ = (0 2 1), x₂ = (0 1 2), y₀ = (1 2), y₁ = (0 2), y₂ = (0 1). `}
def sigma3_named_map (w : Sum (Fin three) (Fin three)) (x : Fin three) : Fin three
  ≔ match w, x [
  | inl. (inr. _), inr. v ↦ inr. v
  | inl. (inr. _), inl. (inr. v) ↦ inl. (inr. v)
  | inl. (inr. _), inl. (inl. (inr. v)) ↦ inl. (inl. (inr. v))
  | inl. (inl. (inr. _)), inr. v ↦ inl. (inl. (inr. v))
  | inl. (inl. (inr. _)), inl. (inr. v) ↦ inr. v
  | inl. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ inl. (inr. v)
  | inl. (inl. (inl. (inr. _))), inr. v ↦ inl. (inr. v)
  | inl. (inl. (inl. (inr. _))), inl. (inr. v) ↦ inl. (inl. (inr. v))
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ inr. v
  | inr. (inr. _), inr. v ↦ inr. v
  | inr. (inr. _), inl. (inr. v) ↦ inl. (inl. (inr. v))
  | inr. (inr. _), inl. (inl. (inr. v)) ↦ inl. (inr. v)
  | inr. (inl. (inr. _)), inr. v ↦ inl. (inl. (inr. v))
  | inr. (inl. (inr. _)), inl. (inr. v) ↦ inl. (inr. v)
  | inr. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ inr. v
  | inr. (inl. (inl. (inr. _))), inr. v ↦ inl. (inr. v)
  | inr. (inl. (inl. (inr. _))), inl. (inr. v) ↦ inr. v
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ inl. (inl. (inr. v))
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. e))), _ ↦ match e []
  | inr. (inl. (inl. (inl. e))), _ ↦ match e [] ]

def sigma3_named_inverse_map (w : Sum (Fin three) (Fin three)) (x : Fin three) : Fin three
  ≔ match w, x [
  | inl. (inr. _), inr. v ↦ inr. v
  | inl. (inr. _), inl. (inr. v) ↦ inl. (inr. v)
  | inl. (inr. _), inl. (inl. (inr. v)) ↦ inl. (inl. (inr. v))
  | inl. (inl. (inr. _)), inr. v ↦ inl. (inr. v)
  | inl. (inl. (inr. _)), inl. (inr. v) ↦ inl. (inl. (inr. v))
  | inl. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ inr. v
  | inl. (inl. (inl. (inr. _))), inr. v ↦ inl. (inl. (inr. v))
  | inl. (inl. (inl. (inr. _))), inl. (inr. v) ↦ inr. v
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ inl. (inr. v)
  | inr. (inr. _), inr. v ↦ inr. v
  | inr. (inr. _), inl. (inr. v) ↦ inl. (inl. (inr. v))
  | inr. (inr. _), inl. (inl. (inr. v)) ↦ inl. (inr. v)
  | inr. (inl. (inr. _)), inr. v ↦ inl. (inl. (inr. v))
  | inr. (inl. (inr. _)), inl. (inr. v) ↦ inl. (inr. v)
  | inr. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ inr. v
  | inr. (inl. (inl. (inr. _))), inr. v ↦ inl. (inr. v)
  | inr. (inl. (inl. (inr. _))), inl. (inr. v) ↦ inr. v
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ inl. (inl. (inr. v))
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. e))), _ ↦ match e []
  | inr. (inl. (inl. (inl. e))), _ ↦ match e [] ]

def sigma3_named_retraction (w : Sum (Fin three) (Fin three)) (x : Fin three)
  : Id (Fin three) (sigma3_named_inverse_map w (sigma3_named_map w x)) x
  ≔ match w, x [
  | inl. (inr. _), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inr. _), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inr. _), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inr. _)), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inl. (inr. _)), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inr. _))), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inr. _), inr. v ↦ refl (inr. v : Fin three)
  | inr. (inr. _), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inr. _), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inr. _)), inr. v ↦ refl (inr. v : Fin three)
  | inr. (inl. (inr. _)), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inl. (inr. _))), inr. v ↦ refl (inr. v : Fin three)
  | inr. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. e))), _ ↦ match e []
  | inr. (inl. (inl. (inl. e))), _ ↦ match e [] ]

def sigma3_named_section (w : Sum (Fin three) (Fin three)) (x : Fin three)
  : Id (Fin three) (sigma3_named_map w (sigma3_named_inverse_map w x)) x
  ≔ match w, x [
  | inl. (inr. _), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inr. _), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inr. _), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inr. _)), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inl. (inr. _)), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inr. _))), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inr. _), inr. v ↦ refl (inr. v : Fin three)
  | inr. (inr. _), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inr. _), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inr. _)), inr. v ↦ refl (inr. v : Fin three)
  | inr. (inl. (inr. _)), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inl. (inr. _))), inr. v ↦ refl (inr. v : Fin three)
  | inr. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. e))), _ ↦ match e []
  | inr. (inl. (inl. (inl. e))), _ ↦ match e [] ]

def sigma3_named (w : Sum (Fin three) (Fin three)) : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) (sigma3_named_map w) (sigma3_named_inverse_map w)
      (sigma3_named_retraction w) (sigma3_named_section w)

{` The name of a permutation from its values at 0 and 1 (garbage x₀ when equal). `}
def sigma3_decode (u v : Fin three) : Sum (Fin three) (Fin three)
  ≔ match u, v [
  | inr. _, inr. _ ↦ inl. (inr. star.)
  | inr. _, inl. (inr. _) ↦ inl. (inr. star.)
  | inr. _, inl. (inl. (inr. _)) ↦ inr. (inr. star.)
  | inl. (inr. _), inr. _ ↦ inr. (inl. (inl. (inr. star.)))
  | inl. (inr. _), inl. (inr. _) ↦ inl. (inr. star.)
  | inl. (inr. _), inl. (inl. (inr. _)) ↦ inl. (inl. (inl. (inr. star.)))
  | inl. (inl. (inr. _)), inr. _ ↦ inl. (inl. (inr. star.))
  | inl. (inl. (inr. _)), inl. (inr. _) ↦ inr. (inl. (inr. star.))
  | inl. (inl. (inr. _)), inl. (inl. (inr. _)) ↦ inl. (inr. star.)
  | inr. _, inl. (inl. (inl. e)) ↦ match e []
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. e)), _ ↦ match e [] ]

def sigma3_point_code (k : Fin three) : Fin three → Type ≔ match k [
  | inr. _ ↦ [ inr. _ ↦ Unit | inl. _ ↦ Empty ]
  | inl. (inr. _) ↦ [ inl. (inr. _) ↦ Unit | inr. _ ↦ Empty | inl. (inl. _) ↦ Empty ]
  | inl. (inl. (inr. _)) ↦ [ inl. (inl. (inr. _)) ↦ Unit | inr. _ ↦ Empty | inl. (inr. _) ↦ Empty | inl. (inl. (inl. e)) ↦ match e [] ]
  | inl. (inl. (inl. e)) ↦ match e [] ]

def sigma3_point_code_refl (k : Fin three) : sigma3_point_code k k
  ≔ match k [
  | inr. _ ↦ star.
  | inl. (inr. _) ↦ star.
  | inl. (inl. (inr. _)) ↦ star.
  | inl. (inl. (inl. e)) ↦ match e [] ]

def sigma3_permutation_injective (σ : Equiv (Fin three) (Fin three)) (i j : Fin three) (p : Id (Fin three) (σ .map i) (σ .map j))
  : sigma3_point_code i j
  ≔ transport (Fin three) (sigma3_point_code i) i j
      (concat (Fin three) i (equiv_inverse_map (Fin three) (Fin three) σ (σ .map i)) j
        (equiv_unit (Fin three) (Fin three) σ i)
        (concat (Fin three) (equiv_inverse_map (Fin three) (Fin three) σ (σ .map i)) (equiv_inverse_map (Fin three) (Fin three) σ (σ .map j)) j
          (refl (equiv_inverse_map (Fin three) (Fin three) σ) p) (equiv_retraction (Fin three) (Fin three) σ j)))
      (sigma3_point_code_refl i)

{` A permutation of Fin 3 is the named permutation of its values at 0 and 1. `}
def sigma3_values (σ : Equiv (Fin three) (Fin three)) (u v t : Fin three)
  : Id (Fin three) (σ .map (inr. star.)) u → Id (Fin three) (σ .map (inl. (inr. star.))) v
    → Id (Fin three) (σ .map (inl. (inl. (inr. star.)))) t
    → (x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode u v) x)
  ≔ match u, v, t [
  | inr. star., inr. star., inr. star. ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inr. star.) (inr. star.)) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inr. star.) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inr. star.) hv)))
  | inr. star., inr. star., inl. (inr. star.) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inr. star.) (inr. star.)) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inr. star.) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inr. star.) hv)))
  | inr. star., inr. star., inl. (inl. (inr. star.)) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inr. star.) (inr. star.)) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inr. star.) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inr. star.) hv)))
  | inr. star., inl. (inr. star.), inr. star. ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inr. star.) (inl. (inr. star.))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inr. star.)) (inr. star.) (σ .map (inl. (inl. (inr. star.)))) hu
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inr. star.) ht)))
  | inr. star., inl. (inr. star.), inl. (inr. star.) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inr. star.) (inl. (inr. star.))) x))
      (sigma3_permutation_injective σ (inl. (inr. star.)) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inl. (inr. star.))) (inl. (inr. star.)) (σ .map (inl. (inl. (inr. star.)))) hv
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inl. (inr. star.)) ht)))
  | inr. star., inl. (inr. star.), inl. (inl. (inr. star.)) ↦ hu hv ht ↦ [ | inr. star. ↦ hu | inl. (inr. star.) ↦ hv | inl. (inl. (inr. star.)) ↦ ht | inl. (inl. (inl. e)) ↦ match e [] ]
  | inr. star., inl. (inl. (inr. star.)), inr. star. ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inr. star.) (inl. (inl. (inr. star.)))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inr. star.)) (inr. star.) (σ .map (inl. (inl. (inr. star.)))) hu
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inr. star.) ht)))
  | inr. star., inl. (inl. (inr. star.)), inl. (inr. star.) ↦ hu hv ht ↦ [ | inr. star. ↦ hu | inl. (inr. star.) ↦ hv | inl. (inl. (inr. star.)) ↦ ht | inl. (inl. (inl. e)) ↦ match e [] ]
  | inr. star., inl. (inl. (inr. star.)), inl. (inl. (inr. star.)) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inr. star.) (inl. (inl. (inr. star.)))) x))
      (sigma3_permutation_injective σ (inl. (inr. star.)) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inl. (inr. star.))) (inl. (inl. (inr. star.))) (σ .map (inl. (inl. (inr. star.)))) hv
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inl. (inl. (inr. star.))) ht)))
  | inl. (inr. star.), inr. star., inr. star. ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inr. star.)) (inr. star.)) x))
      (sigma3_permutation_injective σ (inl. (inr. star.)) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inl. (inr. star.))) (inr. star.) (σ .map (inl. (inl. (inr. star.)))) hv
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inr. star.) ht)))
  | inl. (inr. star.), inr. star., inl. (inr. star.) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inr. star.)) (inr. star.)) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inr. star.)) (σ .map (inl. (inl. (inr. star.)))) hu
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inl. (inr. star.)) ht)))
  | inl. (inr. star.), inr. star., inl. (inl. (inr. star.)) ↦ hu hv ht ↦ [ | inr. star. ↦ hu | inl. (inr. star.) ↦ hv | inl. (inl. (inr. star.)) ↦ ht | inl. (inl. (inl. e)) ↦ match e [] ]
  | inl. (inr. star.), inl. (inr. star.), inr. star. ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inr. star.)) (inl. (inr. star.))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inr. star.)) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inl. (inr. star.)) hv)))
  | inl. (inr. star.), inl. (inr. star.), inl. (inr. star.) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inr. star.)) (inl. (inr. star.))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inr. star.)) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inl. (inr. star.)) hv)))
  | inl. (inr. star.), inl. (inr. star.), inl. (inl. (inr. star.)) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inr. star.)) (inl. (inr. star.))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inr. star.)) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inl. (inr. star.)) hv)))
  | inl. (inr. star.), inl. (inl. (inr. star.)), inr. star. ↦ hu hv ht ↦ [ | inr. star. ↦ hu | inl. (inr. star.) ↦ hv | inl. (inl. (inr. star.)) ↦ ht | inl. (inl. (inl. e)) ↦ match e [] ]
  | inl. (inr. star.), inl. (inl. (inr. star.)), inl. (inr. star.) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inr. star.)) (inl. (inl. (inr. star.)))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inr. star.)) (σ .map (inl. (inl. (inr. star.)))) hu
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inl. (inr. star.)) ht)))
  | inl. (inr. star.), inl. (inl. (inr. star.)), inl. (inl. (inr. star.)) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inr. star.)) (inl. (inl. (inr. star.)))) x))
      (sigma3_permutation_injective σ (inl. (inr. star.)) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inl. (inr. star.))) (inl. (inl. (inr. star.))) (σ .map (inl. (inl. (inr. star.)))) hv
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inl. (inl. (inr. star.))) ht)))
  | inl. (inl. (inr. star.)), inr. star., inr. star. ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inl. (inr. star.))) (inr. star.)) x))
      (sigma3_permutation_injective σ (inl. (inr. star.)) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inl. (inr. star.))) (inr. star.) (σ .map (inl. (inl. (inr. star.)))) hv
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inr. star.) ht)))
  | inl. (inl. (inr. star.)), inr. star., inl. (inr. star.) ↦ hu hv ht ↦ [ | inr. star. ↦ hu | inl. (inr. star.) ↦ hv | inl. (inl. (inr. star.)) ↦ ht | inl. (inl. (inl. e)) ↦ match e [] ]
  | inl. (inl. (inr. star.)), inr. star., inl. (inl. (inr. star.)) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inl. (inr. star.))) (inr. star.)) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inl. (inr. star.))) (σ .map (inl. (inl. (inr. star.)))) hu
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inl. (inl. (inr. star.))) ht)))
  | inl. (inl. (inr. star.)), inl. (inr. star.), inr. star. ↦ hu hv ht ↦ [ | inr. star. ↦ hu | inl. (inr. star.) ↦ hv | inl. (inl. (inr. star.)) ↦ ht | inl. (inl. (inl. e)) ↦ match e [] ]
  | inl. (inl. (inr. star.)), inl. (inr. star.), inl. (inr. star.) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inl. (inr. star.))) (inl. (inr. star.))) x))
      (sigma3_permutation_injective σ (inl. (inr. star.)) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inl. (inr. star.))) (inl. (inr. star.)) (σ .map (inl. (inl. (inr. star.)))) hv
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inl. (inr. star.)) ht)))
  | inl. (inl. (inr. star.)), inl. (inr. star.), inl. (inl. (inr. star.)) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inl. (inr. star.))) (inl. (inr. star.))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inl. (inr. star.)))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inl. (inr. star.))) (σ .map (inl. (inl. (inr. star.)))) hu
          (inverse (Fin three) (σ .map (inl. (inl. (inr. star.)))) (inl. (inl. (inr. star.))) ht)))
  | inl. (inl. (inr. star.)), inl. (inl. (inr. star.)), inr. star. ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inl. (inr. star.))) (inl. (inl. (inr. star.)))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inl. (inr. star.))) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inl. (inl. (inr. star.))) hv)))
  | inl. (inl. (inr. star.)), inl. (inl. (inr. star.)), inl. (inr. star.) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inl. (inr. star.))) (inl. (inl. (inr. star.)))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inl. (inr. star.))) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inl. (inl. (inr. star.))) hv)))
  | inl. (inl. (inr. star.)), inl. (inl. (inr. star.)), inl. (inl. (inr. star.)) ↦ hu hv ht ↦ absurd ((x : Fin three) → Id (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (inl. (inl. (inr. star.))) (inl. (inl. (inr. star.)))) x))
      (sigma3_permutation_injective σ (inr. star.) (inl. (inr. star.))
        (concat (Fin three) (σ .map (inr. star.)) (inl. (inl. (inr. star.))) (σ .map (inl. (inr. star.))) hu
          (inverse (Fin three) (σ .map (inl. (inr. star.))) (inl. (inl. (inr. star.))) hv)))
  | inr. star., inr. star., inl. (inl. (inl. e)) ↦ match e []
  | inr. star., inl. (inr. star.), inl. (inl. (inl. e)) ↦ match e []
  | inr. star., inl. (inl. (inr. star.)), inl. (inl. (inl. e)) ↦ match e []
  | inr. star., inl. (inl. (inl. e)), _ ↦ match e []
  | inl. (inr. star.), inr. star., inl. (inl. (inl. e)) ↦ match e []
  | inl. (inr. star.), inl. (inr. star.), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inr. star.), inl. (inl. (inr. star.)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inr. star.), inl. (inl. (inl. e)), _ ↦ match e []
  | inl. (inl. (inr. star.)), inr. star., inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. star.)), inl. (inr. star.), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. star.)), inl. (inl. (inr. star.)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. star.)), inl. (inl. (inl. e)), _ ↦ match e []
  | inl. (inl. (inl. e)), _, _ ↦ match e [] ]

def sigma3_decode_named (w : Sum (Fin three) (Fin three))
  : Id (Sum (Fin three) (Fin three)) (sigma3_decode (sigma3_named_map w (inr. star.)) (sigma3_named_map w (inl. (inr. star.)))) w
  ≔ match w [
  | inl. (inr. star.) ↦ refl (inl. (inr. star.) : Sum (Fin three) (Fin three))
  | inl. (inl. (inr. star.)) ↦ refl (inl. (inl. (inr. star.)) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inr. star.))) ↦ refl (inl. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three))
  | inr. (inr. star.) ↦ refl (inr. (inr. star.) : Sum (Fin three) (Fin three))
  | inr. (inl. (inr. star.)) ↦ refl (inr. (inl. (inr. star.)) : Sum (Fin three) (Fin three))
  | inr. (inl. (inl. (inr. star.))) ↦ refl (inr. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def sigma3_permutation_code : Equiv (Equiv (Fin three) (Fin three)) (Sum (Fin three) (Fin three))
  ≔ quasi_inverse_equiv (Equiv (Fin three) (Fin three)) (Sum (Fin three) (Fin three))
      (σ ↦ sigma3_decode (σ .map (inr. star.)) (σ .map (inl. (inr. star.))))
      sigma3_named
      (σ ↦ equiv_homotopy (Fin three) (Fin three)
        (sigma3_named (sigma3_decode (σ .map (inr. star.)) (σ .map (inl. (inr. star.))))) σ
        (x ↦ inverse (Fin three) (σ .map x) (sigma3_named_map (sigma3_decode (σ .map (inr. star.)) (σ .map (inl. (inr. star.)))) x)
          (sigma3_values σ (σ .map (inr. star.)) (σ .map (inl. (inr. star.))) (σ .map (inl. (inl. (inr. star.))))
            (refl (σ .map (inr. star.))) (refl (σ .map (inl. (inr. star.)))) (refl (σ .map (inl. (inl. (inr. star.))))) x)))
      sigma3_decode_named

{` Symmetries of Σ₃ and their actions (transport), and the classification
   USym Σ₃ ≃ Fin 3 ⊔ Fin 3. `}
def sigma3_usym_action_equiv : Equiv (USym (symmetric_group three)) (Equiv (Fin three) (Fin three))
  ≔ compose_equiv (USym (symmetric_group three)) (Id SetTypes (standard_set three) (standard_set three))
      (Equiv (Fin three) (Fin three))
      (automorphism_group_usym_equiv SetTypes sets_groupoid (standard_set three))
      (set_paths_transport_equiv (standard_set three) (standard_set three))

def sigma3_usym_action_value (p : USym (symmetric_group three)) (x : Fin three)
  : Id (Fin three) (sigma3_usym_action_equiv .map p .map x) (permutation_action (standard_set three) p x)
  ≔ refl (permutation_action (standard_set three) p x)

def sigma3_usym_ext (p q : USym (symmetric_group three))
  (h : (x : Fin three) → Id (Fin three) (permutation_action (standard_set three) p x) (permutation_action (standard_set three) q x))
  : Id (USym (symmetric_group three)) p q
  ≔ let E ≔ sigma3_usym_action_equiv in
    let Einv ≔ equiv_inverse_map (USym (symmetric_group three)) (Equiv (Fin three) (Fin three)) E in
    calc p = Einv (E .map p)
        by inverse (USym (symmetric_group three)) (Einv (E .map p)) p
          (equiv_retraction (USym (symmetric_group three)) (Equiv (Fin three) (Fin three)) E p)
      = Einv (E .map q) by refl Einv (equiv_homotopy (Fin three) (Fin three) (E .map p) (E .map q) h)
      = q by equiv_retraction (USym (symmetric_group three)) (Equiv (Fin three) (Fin three)) E q ∎

def sigma3_named_symmetry (w : Sum (Fin three) (Fin three)) : USym (symmetric_group three)
  ≔ permutation_symmetry (standard_set three) (sigma3_named w)

def sigma3_usym_code (p : USym (symmetric_group three)) : Sum (Fin three) (Fin three)
  ≔ sigma3_permutation_code .map (sigma3_usym_action_equiv .map p)

def sigma3_named_symmetry_code (w : Sum (Fin three) (Fin three)) : Id (Sum (Fin three) (Fin three)) (sigma3_usym_code (sigma3_named_symmetry w)) w
  ≔ sigma3_decode_named w

def sigma3_code_named_symmetry (p : USym (symmetric_group three))
  : Id (USym (symmetric_group three)) (sigma3_named_symmetry (sigma3_usym_code p)) p
  ≔ sigma3_usym_ext (sigma3_named_symmetry (sigma3_usym_code p)) p
      (x ↦ refl ((σ ↦ σ .map x) : Equiv (Fin three) (Fin three) → Fin three)
        (equiv_retraction (Equiv (Fin three) (Fin three)) (Sum (Fin three) (Fin three)) sigma3_permutation_code (sigma3_usym_action_equiv .map p)))

def sigma3_usym_named_equiv : Equiv (Sum (Fin three) (Fin three)) (USym (symmetric_group three))
  ≔ quasi_inverse_equiv (Sum (Fin three) (Fin three)) (USym (symmetric_group three)) sigma3_named_symmetry sigma3_usym_code
      sigma3_named_symmetry_code sigma3_code_named_symmetry

{` Right multiplication on Σ₃: (p·g)(x) = p(g(x)). `}
def sigma3_right_mul_action (g p : USym (symmetric_group three)) (x : Fin three)
  : Id (Fin three) (permutation_action (standard_set three) (cayley_right_mul (symmetric_group three) g (shape (symmetric_group three)) .map p) x)
      (permutation_action (standard_set three) p (permutation_action (standard_set three) g x))
  ≔ permutation_action_mul (standard_set three) p g x

def sigma3_cycle_symmetry : USym (symmetric_group three) ≔ sigma3_named_symmetry (inl. (inl. (inl. (inr. star.))))
def sigma3_swap12_symmetry : USym (symmetric_group three) ≔ sigma3_named_symmetry (inr. (inr. star.))
def sigma3_swap01_symmetry : USym (symmetric_group three) ≔ sigma3_named_symmetry (inr. (inl. (inl. (inr. star.))))

{` Litmus: the generators act as (0 1 2), (1 2), (0 1). `}
def sigma3_cycle_symmetry_values
  : Id (Product (Fin three) (Product (Fin three) (Fin three)))
      (permutation_action (standard_set three) sigma3_cycle_symmetry (inr. star.),
       (permutation_action (standard_set three) sigma3_cycle_symmetry (inl. (inr. star.)),
        permutation_action (standard_set three) sigma3_cycle_symmetry (inl. (inl. (inr. star.)))))
      (inl. (inr. star.), (inl. (inl. (inr. star.)), inr. star.))
  ≔ refl ((inl. (inr. star.), (inl. (inl. (inr. star.)), inr. star.)) : Product (Fin three) (Product (Fin three) (Fin three)))

{` The prism bicycle (second picture). `}
{` a(x_k) = x_{k−1}, a(y_k) = y_{k+1}. `}
def prism_a_map : Sum (Fin three) (Fin three) → Sum (Fin three) (Fin three) ≔ [
  | inl. (inr. u) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inr. u))
  | inr. (inr. u) ↦ inr. (inl. (inr. u))
  | inr. (inl. (inr. u)) ↦ inr. (inl. (inl. (inr. u)))
  | inr. (inl. (inl. (inr. u))) ↦ inr. (inr. u)
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_a_inverse_map : Sum (Fin three) (Fin three) → Sum (Fin three) (Fin three) ≔ [
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inr. u)
  | inr. (inr. u) ↦ inr. (inl. (inl. (inr. u)))
  | inr. (inl. (inr. u)) ↦ inr. (inr. u)
  | inr. (inl. (inl. (inr. u))) ↦ inr. (inl. (inr. u))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_a_retraction (x : Sum (Fin three) (Fin three))
  : Id (Sum (Fin three) (Fin three)) (prism_a_inverse_map (prism_a_map x)) x
  ≔ match x [
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Sum (Fin three) (Fin three))
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inr. (inr. u) ↦ refl (inr. (inr. u) : Sum (Fin three) (Fin three))
  | inr. (inl. (inr. u)) ↦ refl (inr. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inr. (inl. (inl. (inr. u))) ↦ refl (inr. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_a_section (x : Sum (Fin three) (Fin three))
  : Id (Sum (Fin three) (Fin three)) (prism_a_map (prism_a_inverse_map x)) x
  ≔ match x [
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Sum (Fin three) (Fin three))
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inr. (inr. u) ↦ refl (inr. (inr. u) : Sum (Fin three) (Fin three))
  | inr. (inl. (inr. u)) ↦ refl (inr. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inr. (inl. (inl. (inr. u))) ↦ refl (inr. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_a : Equiv (Sum (Fin three) (Fin three)) (Sum (Fin three) (Fin three))
  ≔ quasi_inverse_equiv (Sum (Fin three) (Fin three)) (Sum (Fin three) (Fin three)) prism_a_map prism_a_inverse_map prism_a_retraction prism_a_section

{` b swaps x_k and y_k. `}
def prism_b_map : Sum (Fin three) (Fin three) → Sum (Fin three) (Fin three) ≔ [
  | inl. (inr. u) ↦ inr. (inr. u)
  | inl. (inl. (inr. u)) ↦ inr. (inl. (inr. u))
  | inl. (inl. (inl. (inr. u))) ↦ inr. (inl. (inl. (inr. u)))
  | inr. (inr. u) ↦ inl. (inr. u)
  | inr. (inl. (inr. u)) ↦ inl. (inl. (inr. u))
  | inr. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_b_inverse_map : Sum (Fin three) (Fin three) → Sum (Fin three) (Fin three) ≔ [
  | inl. (inr. u) ↦ inr. (inr. u)
  | inl. (inl. (inr. u)) ↦ inr. (inl. (inr. u))
  | inl. (inl. (inl. (inr. u))) ↦ inr. (inl. (inl. (inr. u)))
  | inr. (inr. u) ↦ inl. (inr. u)
  | inr. (inl. (inr. u)) ↦ inl. (inl. (inr. u))
  | inr. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_b_retraction (x : Sum (Fin three) (Fin three))
  : Id (Sum (Fin three) (Fin three)) (prism_b_inverse_map (prism_b_map x)) x
  ≔ match x [
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Sum (Fin three) (Fin three))
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inr. (inr. u) ↦ refl (inr. (inr. u) : Sum (Fin three) (Fin three))
  | inr. (inl. (inr. u)) ↦ refl (inr. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inr. (inl. (inl. (inr. u))) ↦ refl (inr. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_b_section (x : Sum (Fin three) (Fin three))
  : Id (Sum (Fin three) (Fin three)) (prism_b_map (prism_b_inverse_map x)) x
  ≔ match x [
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Sum (Fin three) (Fin three))
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inr. (inr. u) ↦ refl (inr. (inr. u) : Sum (Fin three) (Fin three))
  | inr. (inl. (inr. u)) ↦ refl (inr. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inr. (inl. (inl. (inr. u))) ↦ refl (inr. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_b : Equiv (Sum (Fin three) (Fin three)) (Sum (Fin three) (Fin three))
  ≔ quasi_inverse_equiv (Sum (Fin three) (Fin three)) (Sum (Fin three) (Fin three)) prism_b_map prism_b_inverse_map prism_b_retraction prism_b_section

def prism_word_from_origin (y : Sum (Fin three) (Fin three))
  : BicycleWordFrom (Sum (Fin three) (Fin three)) prism_a prism_b (inl. (inr. star.)) y
  ≔ match y [
  | inl. (inr. star.) ↦ (nil., refl (inl. (inr. star.) : Sum (Fin three) (Fin three)))
  | inl. (inl. (inr. star.)) ↦ (cons. (inl. (pos. (suc. (suc. zero.)))) nil., refl (inl. (inl. (inr. star.)) : Sum (Fin three) (Fin three)))
  | inl. (inl. (inl. (inr. star.))) ↦ (cons. (inl. (pos. (suc. zero.))) nil., refl (inl. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)))
  | inr. (inr. star.) ↦ (cons. (inr. (pos. (suc. zero.))) nil., refl (inr. (inr. star.) : Sum (Fin three) (Fin three)))
  | inr. (inl. (inr. star.)) ↦ (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (pos. (suc. (suc. zero.)))) nil.), refl (inr. (inl. (inr. star.)) : Sum (Fin three) (Fin three)))
  | inr. (inl. (inl. (inr. star.))) ↦ (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (pos. (suc. zero.))) nil.), refl (inr. (inl. (inl. (inr. star.))) : Sum (Fin three) (Fin three)))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def prism_bicycle : Bicycles
  ≔ mkbicycle (Sum (Fin three) (Fin three), sum_set (Fin three) (Fin three) (fin_set three) (fin_set three)) prism_a prism_b
      (bicycle_connected_from_point (Sum (Fin three) (Fin three)) prism_a prism_b (inl. (inr. star.))
        (y ↦ mere (BicycleWordFrom (Sum (Fin three) (Fin three)) prism_a prism_b (inl. (inr. star.)) y) (prism_word_from_origin y)))

def prism_a_named (w : Sum (Fin three) (Fin three)) (x : Fin three)
  : Id (Fin three) (sigma3_named_map (prism_a_map w) x)
      (sigma3_named_map w (sigma3_named_map (inl. (inl. (inl. (inr. star.)))) x))
  ≔ match w, x [
  | inl. (inr. _), inr. v ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inr. _), inl. (inr. v) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inr. _), inl. (inl. (inr. v)) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inr. _)), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inl. (inr. _)), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inr. _))), inr. v ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inr. _), inr. v ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inr. _), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inr. _), inl. (inl. (inr. v)) ↦ refl (inr. v : Fin three)
  | inr. (inl. (inr. _)), inr. v ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inl. (inr. _)), inl. (inr. v) ↦ refl (inr. v : Fin three)
  | inr. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inl. (inr. _))), inr. v ↦ refl (inr. v : Fin three)
  | inr. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. e))), _ ↦ match e []
  | inr. (inl. (inl. (inl. e))), _ ↦ match e [] ]

def prism_b_named (w : Sum (Fin three) (Fin three)) (x : Fin three)
  : Id (Fin three) (sigma3_named_map (prism_b_map w) x)
      (sigma3_named_map w (sigma3_named_map (inr. (inr. star.)) x))
  ≔ match w, x [
  | inl. (inr. _), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inr. _), inl. (inr. v) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inr. _), inl. (inl. (inr. v)) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inr. _)), inr. v ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inr. _)), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inr. _))), inr. v ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inr. _), inr. v ↦ refl (inr. v : Fin three)
  | inr. (inr. _), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inr. _), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inr. _)), inr. v ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inr. _)), inl. (inr. v) ↦ refl (inr. v : Fin three)
  | inr. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inl. (inl. (inr. _))), inr. v ↦ refl (inl. (inr. v) : Fin three)
  | inr. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inr. v : Fin three)
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inr. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. e))), _ ↦ match e []
  | inr. (inl. (inl. (inl. e))), _ ↦ match e [] ]

def prism_cayley_commutes_a
  : Commutes (Sum (Fin three) (Fin three)) (USym (symmetric_group three)) prism_a
      (cayley_right_mul (symmetric_group three) sigma3_cycle_symmetry (shape (symmetric_group three))) sigma3_named_symmetry
  ≔ w ↦ sigma3_usym_ext (sigma3_named_symmetry (prism_a_map w))
      (cayley_right_mul (symmetric_group three) sigma3_cycle_symmetry (shape (symmetric_group three)) .map (sigma3_named_symmetry w))
      (x ↦ concat (Fin three) (sigma3_named_map (prism_a_map w) x)
        (sigma3_named_map w (sigma3_named_map (inl. (inl. (inl. (inr. star.)))) x))
        (permutation_action (standard_set three)
          (cayley_right_mul (symmetric_group three) sigma3_cycle_symmetry (shape (symmetric_group three)) .map (sigma3_named_symmetry w)) x)
        (prism_a_named w x)
        (inverse (Fin three) (permutation_action (standard_set three)
            (cayley_right_mul (symmetric_group three) sigma3_cycle_symmetry (shape (symmetric_group three)) .map (sigma3_named_symmetry w)) x)
          (sigma3_named_map w (sigma3_named_map (inl. (inl. (inl. (inr. star.)))) x))
          (sigma3_right_mul_action sigma3_cycle_symmetry (sigma3_named_symmetry w) x)))

def prism_cayley_commutes_b
  : Commutes (Sum (Fin three) (Fin three)) (USym (symmetric_group three)) prism_b
      (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three))) sigma3_named_symmetry
  ≔ w ↦ sigma3_usym_ext (sigma3_named_symmetry (prism_b_map w))
      (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three)) .map (sigma3_named_symmetry w))
      (x ↦ concat (Fin three) (sigma3_named_map (prism_b_map w) x)
        (sigma3_named_map w (sigma3_named_map (inr. (inr. star.)) x))
        (permutation_action (standard_set three)
          (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three)) .map (sigma3_named_symmetry w)) x)
        (prism_b_named w x)
        (inverse (Fin three) (permutation_action (standard_set three)
            (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three)) .map (sigma3_named_symmetry w)) x)
          (sigma3_named_map w (sigma3_named_map (inr. (inr. star.)) x))
          (sigma3_right_mul_action sigma3_swap12_symmetry (sigma3_named_symmetry w) x)))

{` (0 1 2) and (1 2) generate Σ₃: the Cayley bicycle is connected
   (transported from the prism bicycle). `}
def sigma3_prism_generating : CayleyGenerating (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry
  ≔ bicycle_connected_transfer (Sum (Fin three) (Fin three)) (USym (symmetric_group three)) prism_a prism_b
      (cayley_right_mul (symmetric_group three) sigma3_cycle_symmetry (shape (symmetric_group three)))
      (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three)))
      sigma3_usym_named_equiv prism_cayley_commutes_a prism_cayley_commutes_b (bicycle_connectivity prism_bicycle)

def prism_cayley_path
  : Id Bicycles prism_bicycle (cayley_bicycle (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry sigma3_prism_generating)
  ≔ bicycle_path_from_iso prism_bicycle
      (cayley_bicycle (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry sigma3_prism_generating)
      (sigma3_usym_named_equiv, (prism_cayley_commutes_a, prism_cayley_commutes_b))

{` Aut_Bicyc(prism) = Σ₃. `}
def prism_automorphism_group_path : Id Group (bicycle_automorphism_group prism_bicycle) (symmetric_group three)
  ≔ concat Group (bicycle_automorphism_group prism_bicycle)
      (bicycle_automorphism_group
        (cayley_bicycle (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry sigma3_prism_generating))
      (symmetric_group three)
      (refl bicycle_automorphism_group prism_cayley_path)
      (inverse Group (symmetric_group three)
        (bicycle_automorphism_group
          (cayley_bicycle (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry sigma3_prism_generating))
        (cayley_bicycle_group_path (symmetric_group three) sigma3_cycle_symmetry sigma3_swap12_symmetry sigma3_prism_generating))

{` The hexagon bicycle (first picture). `}
{` a = (0 1)(2 3)(4 5). `}
def hexagon_a_map : Fin bicycle_six → Fin bicycle_six ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_a_inverse_map : Fin bicycle_six → Fin bicycle_six ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_a_retraction (x : Fin bicycle_six)
  : Id (Fin bicycle_six) (hexagon_a_inverse_map (hexagon_a_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_six)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_six)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_six)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_a_section (x : Fin bicycle_six)
  : Id (Fin bicycle_six) (hexagon_a_map (hexagon_a_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_six)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_six)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_six)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_a : Equiv (Fin bicycle_six) (Fin bicycle_six)
  ≔ quasi_inverse_equiv (Fin bicycle_six) (Fin bicycle_six) hexagon_a_map hexagon_a_inverse_map hexagon_a_retraction hexagon_a_section

{` b = (1 2)(3 4)(5 0). `}
def hexagon_b_map : Fin bicycle_six → Fin bicycle_six ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_b_inverse_map : Fin bicycle_six → Fin bicycle_six ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_b_retraction (x : Fin bicycle_six)
  : Id (Fin bicycle_six) (hexagon_b_inverse_map (hexagon_b_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_six)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_six)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_six)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_b_section (x : Fin bicycle_six)
  : Id (Fin bicycle_six) (hexagon_b_map (hexagon_b_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin bicycle_six)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_six)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_six)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_b : Equiv (Fin bicycle_six) (Fin bicycle_six)
  ≔ quasi_inverse_equiv (Fin bicycle_six) (Fin bicycle_six) hexagon_b_map hexagon_b_inverse_map hexagon_b_retraction hexagon_b_section

def hexagon_word_from_zero (y : Fin bicycle_six)
  : BicycleWordFrom (Fin bicycle_six) hexagon_a hexagon_b (inr. star.) y
  ≔ match y [
  | inr. star. ↦ (nil., refl (inr. star. : Fin bicycle_six))
  | inl. (inr. star.) ↦ (cons. (inl. (pos. (suc. zero.))) nil., refl (inl. (inr. star.) : Fin bicycle_six))
  | inl. (inl. (inr. star.)) ↦ (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (pos. (suc. zero.))) nil.), refl (inl. (inl. (inr. star.)) : Fin bicycle_six))
  | inl. (inl. (inl. (inr. star.))) ↦ (cons. (inl. (pos. (suc. zero.))) (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (pos. (suc. zero.))) nil.)), refl (inl. (inl. (inl. (inr. star.))) : Fin bicycle_six))
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (pos. (suc. zero.))) (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (pos. (suc. zero.))) nil.))), refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin bicycle_six))
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ (cons. (inl. (pos. (suc. zero.))) (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (pos. (suc. zero.))) (cons. (inr. (pos. (suc. zero.))) (cons. (inl. (pos. (suc. zero.))) nil.)))), refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin bicycle_six))
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_bicycle : Bicycles
  ≔ mkbicycle (Fin bicycle_six, fin_set bicycle_six) hexagon_a hexagon_b
      (bicycle_connected_from_point (Fin bicycle_six) hexagon_a hexagon_b (inr. star.)
        (y ↦ mere (BicycleWordFrom (Fin bicycle_six) hexagon_a hexagon_b (inr. star.) y) (hexagon_word_from_zero y)))

{` Nodes of the hexagon as permutations: 0 ↦ id, 1 ↦ (0 1), 2 ↦ (0 1)(1 2), ...,
   via a bijection with the names Fin 3 ⊔ Fin 3. `}
def hexagon_node_name : Fin bicycle_six → Sum (Fin three) (Fin three) ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inr. (inl. (inl. (inr. u)))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inr. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inr. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_name_node : Sum (Fin three) (Fin three) → Fin bicycle_six ≔ [
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inr. u))
  | inr. (inr. u) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inr. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inr. (inl. (inl. (inr. u))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def hexagon_name_retraction (k : Fin bicycle_six) : Id (Fin bicycle_six) (hexagon_name_node (hexagon_node_name k)) k
  ≔ match k [
  | inr. u ↦ refl (inr. u : Fin bicycle_six)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin bicycle_six)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin bicycle_six)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin bicycle_six)
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

def hexagon_name_section (w : Sum (Fin three) (Fin three)) : Id (Sum (Fin three) (Fin three)) (hexagon_node_name (hexagon_name_node w)) w
  ≔ match w [
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Sum (Fin three) (Fin three))
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inr. (inr. u) ↦ refl (inr. (inr. u) : Sum (Fin three) (Fin three))
  | inr. (inl. (inr. u)) ↦ refl (inr. (inl. (inr. u)) : Sum (Fin three) (Fin three))
  | inr. (inl. (inl. (inr. u))) ↦ refl (inr. (inl. (inl. (inr. u))) : Sum (Fin three) (Fin three))
  | inl. (inl. (inl. (inl. e))) ↦ match e []
  | inr. (inl. (inl. (inl. e))) ↦ match e [] ]

def hexagon_name_equiv : Equiv (Fin bicycle_six) (Sum (Fin three) (Fin three))
  ≔ quasi_inverse_equiv (Fin bicycle_six) (Sum (Fin three) (Fin three)) hexagon_node_name hexagon_name_node hexagon_name_retraction hexagon_name_section

def hexagon_a_named (k : Fin bicycle_six) (x : Fin three)
  : Id (Fin three) (sigma3_named_map (hexagon_node_name (hexagon_a_map k)) x)
      (sigma3_named_map (hexagon_node_name k) (sigma3_named_map (inr. (inl. (inl. (inr. star.)))) x))
  ≔ match k, x [
  | inr. _, inr. v ↦ refl (inl. (inr. v) : Fin three)
  | inr. _, inl. (inr. v) ↦ refl (inr. v : Fin three)
  | inr. _, inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inr. _), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inr. _), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inr. _), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inr. _)), inr. v ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inr. _)), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inr. _))), inr. v ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inl. (inr. _)))), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inl. (inr. _)))), inl. (inr. v) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inl. (inr. _)))), inl. (inl. (inr. v)) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inl. (inl. (inl. (inr. _))))), inr. v ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inl. (inl. (inr. _))))), inl. (inr. v) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inl. (inl. (inr. _))))), inl. (inl. (inr. v)) ↦ refl (inl. (inr. v) : Fin three)
  | inr. _, inl. (inl. (inl. e)) ↦ match e []
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. (inr. _)))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. (inl. (inr. _))))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. (inl. (inl. e))))), _ ↦ match e [] ]

def hexagon_b_named (k : Fin bicycle_six) (x : Fin three)
  : Id (Fin three) (sigma3_named_map (hexagon_node_name (hexagon_b_map k)) x)
      (sigma3_named_map (hexagon_node_name k) (sigma3_named_map (inr. (inr. star.)) x))
  ≔ match k, x [
  | inr. _, inr. v ↦ refl (inr. v : Fin three)
  | inr. _, inl. (inr. v) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. _, inl. (inl. (inr. v)) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inr. _), inr. v ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inr. _), inl. (inr. v) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inr. _), inl. (inl. (inr. v)) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inr. _)), inr. v ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inr. _)), inl. (inr. v) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inr. _)), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inr. _))), inr. v ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inr. v) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inr. v)) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inl. (inl. (inr. _)))), inr. v ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inl. (inl. (inl. (inl. (inr. _)))), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inl. (inl. (inr. _)))), inl. (inl. (inr. v)) ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inl. (inl. (inr. _))))), inr. v ↦ refl (inr. v : Fin three)
  | inl. (inl. (inl. (inl. (inl. (inr. _))))), inl. (inr. v) ↦ refl (inl. (inr. v) : Fin three)
  | inl. (inl. (inl. (inl. (inl. (inr. _))))), inl. (inl. (inr. v)) ↦ refl (inl. (inl. (inr. v)) : Fin three)
  | inr. _, inl. (inl. (inl. e)) ↦ match e []
  | inl. (inr. _), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inr. _)), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inr. _))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. (inr. _)))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. (inl. (inr. _))))), inl. (inl. (inl. e)) ↦ match e []
  | inl. (inl. (inl. (inl. (inl. (inl. e))))), _ ↦ match e [] ]

def hexagon_symmetry (k : Fin bicycle_six) : USym (symmetric_group three) ≔ sigma3_named_symmetry (hexagon_node_name k)

def hexagon_usym_equiv : Equiv (Fin bicycle_six) (USym (symmetric_group three))
  ≔ compose_equiv (Fin bicycle_six) (Sum (Fin three) (Fin three)) (USym (symmetric_group three)) hexagon_name_equiv sigma3_usym_named_equiv

def hexagon_cayley_commutes_a
  : Commutes (Fin bicycle_six) (USym (symmetric_group three)) hexagon_a
      (cayley_right_mul (symmetric_group three) sigma3_swap01_symmetry (shape (symmetric_group three))) hexagon_symmetry
  ≔ k ↦ sigma3_usym_ext (hexagon_symmetry (hexagon_a_map k))
      (cayley_right_mul (symmetric_group three) sigma3_swap01_symmetry (shape (symmetric_group three)) .map (hexagon_symmetry k))
      (x ↦ concat (Fin three) (sigma3_named_map (hexagon_node_name (hexagon_a_map k)) x)
        (sigma3_named_map (hexagon_node_name k) (sigma3_named_map (inr. (inl. (inl. (inr. star.)))) x))
        (permutation_action (standard_set three)
          (cayley_right_mul (symmetric_group three) sigma3_swap01_symmetry (shape (symmetric_group three)) .map (hexagon_symmetry k)) x)
        (hexagon_a_named k x)
        (inverse (Fin three) (permutation_action (standard_set three)
            (cayley_right_mul (symmetric_group three) sigma3_swap01_symmetry (shape (symmetric_group three)) .map (hexagon_symmetry k)) x)
          (sigma3_named_map (hexagon_node_name k) (sigma3_named_map (inr. (inl. (inl. (inr. star.)))) x))
          (sigma3_right_mul_action sigma3_swap01_symmetry (hexagon_symmetry k) x)))

def hexagon_cayley_commutes_b
  : Commutes (Fin bicycle_six) (USym (symmetric_group three)) hexagon_b
      (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three))) hexagon_symmetry
  ≔ k ↦ sigma3_usym_ext (hexagon_symmetry (hexagon_b_map k))
      (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three)) .map (hexagon_symmetry k))
      (x ↦ concat (Fin three) (sigma3_named_map (hexagon_node_name (hexagon_b_map k)) x)
        (sigma3_named_map (hexagon_node_name k) (sigma3_named_map (inr. (inr. star.)) x))
        (permutation_action (standard_set three)
          (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three)) .map (hexagon_symmetry k)) x)
        (hexagon_b_named k x)
        (inverse (Fin three) (permutation_action (standard_set three)
            (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three)) .map (hexagon_symmetry k)) x)
          (sigma3_named_map (hexagon_node_name k) (sigma3_named_map (inr. (inr. star.)) x))
          (sigma3_right_mul_action sigma3_swap12_symmetry (hexagon_symmetry k) x)))

def sigma3_hexagon_generating : CayleyGenerating (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry
  ≔ bicycle_connected_transfer (Fin bicycle_six) (USym (symmetric_group three)) hexagon_a hexagon_b
      (cayley_right_mul (symmetric_group three) sigma3_swap01_symmetry (shape (symmetric_group three)))
      (cayley_right_mul (symmetric_group three) sigma3_swap12_symmetry (shape (symmetric_group three)))
      hexagon_usym_equiv hexagon_cayley_commutes_a hexagon_cayley_commutes_b (bicycle_connectivity hexagon_bicycle)

def hexagon_cayley_path
  : Id Bicycles hexagon_bicycle
      (cayley_bicycle (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry sigma3_hexagon_generating)
  ≔ bicycle_path_from_iso hexagon_bicycle
      (cayley_bicycle (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry sigma3_hexagon_generating)
      (hexagon_usym_equiv, (hexagon_cayley_commutes_a, hexagon_cayley_commutes_b))

{` Aut_Bicyc(hexagon) = Σ₃. `}
def hexagon_automorphism_group_path : Id Group (bicycle_automorphism_group hexagon_bicycle) (symmetric_group three)
  ≔ concat Group (bicycle_automorphism_group hexagon_bicycle)
      (bicycle_automorphism_group
        (cayley_bicycle (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry sigma3_hexagon_generating))
      (symmetric_group three)
      (refl bicycle_automorphism_group hexagon_cayley_path)
      (inverse Group (symmetric_group three)
        (bicycle_automorphism_group
          (cayley_bicycle (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry sigma3_hexagon_generating))
        (cayley_bicycle_group_path (symmetric_group three) sigma3_swap01_symmetry sigma3_swap12_symmetry sigma3_hexagon_generating))

{` The exercise: Aut(hexagon) = Aut(prism), and as an isomorphism of groups. `}
def hexagon_prism_automorphism_path
  : Id Group (bicycle_automorphism_group hexagon_bicycle) (bicycle_automorphism_group prism_bicycle)
  ≔ concat Group (bicycle_automorphism_group hexagon_bicycle) (symmetric_group three) (bicycle_automorphism_group prism_bicycle)
      hexagon_automorphism_group_path
      (inverse Group (bicycle_automorphism_group prism_bicycle) (symmetric_group three) prism_automorphism_group_path)

def hexagon_prism_automorphism_iso : GroupIso (bicycle_automorphism_group hexagon_bicycle) (bicycle_automorphism_group prism_bicycle)
  ≔ group_path_iso_equiv (bicycle_automorphism_group hexagon_bicycle) (bicycle_automorphism_group prism_bicycle)
      .map hexagon_prism_automorphism_path

def hexagon_sigma3_iso : GroupIso (bicycle_automorphism_group hexagon_bicycle) (symmetric_group three)
  ≔ group_path_iso_equiv (bicycle_automorphism_group hexagon_bicycle) (symmetric_group three) .map hexagon_automorphism_group_path

def prism_sigma3_iso : GroupIso (bicycle_automorphism_group prism_bicycle) (symmetric_group three)
  ≔ group_path_iso_equiv (bicycle_automorphism_group prism_bicycle) (symmetric_group three) .map prism_automorphism_group_path
