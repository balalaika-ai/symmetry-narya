export "112-connected-fiber-functors"

def factorization_compare_map (A C D B : Type) (f : A → B) (g : A → C) (h : C → B)
  (r : Id (A → B) f (compose A C B h g)) (i : D → B)
  : RightDiagonals C D B i h → RightDiagonals A D B i f
  ≔ v ↦ (compose A C D (v .fst) g,
      concat (A → B) f (compose A C B h g) (compose A D B i (compose A C D (v .fst) g))
        r (refl (precompose A C B g) (v .snd)))

def mapped_pathover_append (X Y : Type) (F : X → Y) (b : Y) (x y : X) (q : Id X x y) (p : Id Y b (F x))
  : Id (z ↦ Id Y b (F z)) q p (concat Y b (F x) (F y) p (map_path X Y F x y q))
  ≔ let target ≔ concat Y b (F x) (F y) p (map_path X Y F x y q) in
    id_to_equiv (Id (Id Y b (F y)) target target)
      (Id (z ↦ Id Y b (F z)) q p target)
      (inverse Type (Id (z ↦ Id Y b (F z)) q p target) (Id (Id Y b (F y)) target target)
        (pathover_mapped_paths_type X Y F b x y q p target)) .map (refl target)

def factorization_identity_comparison (A C B : Type) (f : A → B) (g k : A → C) (h i : C → B)
  (r : Id (A → B) f (compose A C B h g)) (s : Id (A → B) f (compose A C B i k))
  (beta : Id (C → B) h i)
  (q : Id (RightDiagonals A C B i f) (k, s)
    (factorization_compare_map A C C B f g h r i (identity C, beta)))
  : Id (Factorizations A B f) (C, (g, (h, r))) (C, (k, (i, s)))
  ≔ let n ≔ concat (A → B) f (compose A C B h g) (compose A C B i g)
      r (refl (precompose A C B g) beta) in
    concat (Factorizations A B f) (C, (g, (h, r))) (C, (g, (i, n))) (C, (k, (i, s)))
      (refl C, (refl g, (beta, mapped_pathover_append (C → B) (A → B) (precompose A C B g) f h i beta r)))
      (refl ((v ↦ (C, (v .fst, (i, v .snd)))) : RightDiagonals A C B i f → Factorizations A B f)
        (inverse (RightDiagonals A C B i f) (k, s)
          (factorization_compare_map A C C B f g h r i (identity C, beta)) q))

{` Univalence turns a coherent comparison by an equivalence into a path
   of all four triangular components, including the specified equality.
   The proof uses equivalence induction; its identity case retains q. `}
def factorization_equivalence_comparison (A C D B : Type) (f : A → B) (g : A → C) (h : C → B)
  (r : Id (A → B) f (compose A C B h g)) (k : A → D) (i : D → B)
  (s : Id (A → B) f (compose A D B i k)) (e : Equiv C D)
  (beta : Id (C → B) h (compose C D B i (e .map)))
  (q : Id (RightDiagonals A D B i f) (k, s)
    (factorization_compare_map A C D B f g h r i (e .map, beta)))
  : Id (Factorizations A B f) (C, (g, (h, r))) (D, (k, (i, s)))
  ≔ equivalence_induction C
      (D e ↦ (k : A → D) (i : D → B) (s : Id (A → B) f (compose A D B i k)) →
        (beta : Id (C → B) h (compose C D B i (e .map))) →
        Id (RightDiagonals A D B i f) (k, s)
          (factorization_compare_map A C D B f g h r i (e .map, beta)) →
        Id (Factorizations A B f) (C, (g, (h, r))) (D, (k, (i, s))))
      (k i s beta q ↦ factorization_identity_comparison A C B f g k h i r s beta q) D e k i s beta q
