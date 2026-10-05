export "1491-golden-ring-map"

{` Chapter 14: the edge graph of the icosahedron over every
   Euclidean field K. Module 1440 computes in ℤ[φ] that among the 144
   ordered pairs of vertices the squared distance is 0 exactly on the
   diagonal and otherwise 4, 4 + 4φ or 8 + 4φ (icosa_pair_class, by
   computation). The ring map ℤ[φ] → K (module 1491) sends these to the
   squared distances in 𝔼³ over K, where 0, 4, 4 + 4φ and 8 + 4φ are
   pairwise distinct enough for the conclusions: the 12 vertices are
   distinct (icosahedron_vertex_injective), two vertices are at distance 2
   in K exactly when they are at squared distance 4 in ℤ[φ]
   (icosahedron_edge_iff), so the "distance 2" relation of K is decidable
   and its counts are those of ℤ[φ]: every vertex has exactly 5 neighbours
   at distance 2 (icosahedron_field_degree_five) and there are 60 ordered,
   i.e. 30 unordered, edges (icosahedron_field_edge_count). `}

def IcosaPairClass (i j : IcosaIndex) : Type
  ≔ let g ≔ golden_sq_distance (golden_vertex i) (golden_vertex j) in
    Sum (Product (Id IcosaIndex i j) (Id GoldenInt g golden_zero))
      (Sum (Id GoldenInt g (pos. 4, pos. zero.))
        (Sum (Id GoldenInt g (pos. 4, pos. 4)) (Id GoldenInt g (pos. 8, pos. 4))))

{` By computation over all 144 pairs. `}
def icosa_pair_class_cases (k1 : Fin 3) (b1 c1 : Bool) (k2 : Fin 3) (b2 c2 : Bool)
  : IcosaPairClass (k1, (b1, c1)) (k2, (b2, c2))
  ≔ match k1 [
  | inl. (inl. (inl. e)) ↦ match e [ ]
  | inl. (inl. (inr. star.)) ↦ match b1, c1 [
    | true., true. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inl. (refl ((inl. (inl. (inr. star.)), (true., true.)) : IcosaIndex), refl golden_zero)
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      ]
    | true., false. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inl. (refl ((inl. (inl. (inr. star.)), (true., false.)) : IcosaIndex), refl golden_zero)
        | false., true. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      ]
    | false., true. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | false., true. ↦ inl. (refl ((inl. (inl. (inr. star.)), (false., true.)) : IcosaIndex), refl golden_zero)
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      ]
    | false., false. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inl. (refl ((inl. (inl. (inr. star.)), (false., false.)) : IcosaIndex), refl golden_zero)
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      ]
    ]
  | inl. (inr. star.) ↦ match b1, c1 [
    | true., true. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inl. (refl ((inl. (inr. star.), (true., true.)) : IcosaIndex), refl golden_zero)
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      ]
    | true., false. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inl. (refl ((inl. (inr. star.), (true., false.)) : IcosaIndex), refl golden_zero)
        | false., true. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      ]
    | false., true. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | false., true. ↦ inl. (refl ((inl. (inr. star.), (false., true.)) : IcosaIndex), refl golden_zero)
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      ]
    | false., false. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inl. (refl ((inl. (inr. star.), (false., false.)) : IcosaIndex), refl golden_zero)
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      ]
    ]
  | inr. star. ↦ match b1, c1 [
    | true., true. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inl. (refl ((inr. star., (true., true.)) : IcosaIndex), refl golden_zero)
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        ]
      ]
    | true., false. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inl. (refl ((inr. star., (true., false.)) : IcosaIndex), refl golden_zero)
        | false., true. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      ]
    | false., true. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | true., false. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | false., true. ↦ inl. (refl ((inr. star., (false., true.)) : IcosaIndex), refl golden_zero)
        | false., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        ]
      ]
    | false., false. ↦ match k2 [
      | inl. (inl. (inl. e)) ↦ match e [ ]
      | inl. (inl. (inr. star.)) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., true. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inl. (inr. star.) ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        ]
      | inr. star. ↦ match b2, c2 [
        | true., true. ↦ inr. (inr. (inr. (refl ((pos. 8, pos. 4) : GoldenInt))))
        | true., false. ↦ inr. (inl. (refl ((pos. 4, pos. zero.) : GoldenInt)))
        | false., true. ↦ inr. (inr. (inl. (refl ((pos. 4, pos. 4) : GoldenInt))))
        | false., false. ↦ inl. (refl ((inr. star., (false., false.)) : IcosaIndex), refl golden_zero)
        ]
      ]
    ]
  ]

def icosa_pair_class (i j : IcosaIndex) : IcosaPairClass i j
  ≔ icosa_pair_class_cases (i .fst) (i .snd .fst) (i .snd .snd) (j .fst) (j .snd .fst) (j .snd .snd)

{` Squared distance in 𝔼³ over K. `}
def standard_three_sq_distance (K : EuclideanField) (P Q : Fin 3 → ef_carrier K) : ef_carrier K
  ≔ dot_product K 3 (standard_three_difference K P Q) (standard_three_difference K P Q)

def standard_three_sq_distance_self (K : EuclideanField) (P : Fin 3 → ef_carrier K)
  : Id (ef_carrier K) (standard_three_sq_distance K P P) (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let a ≔ R .add in let m ≔ R .mul in
    let zv : Id (Fin 3 → S) (standard_three_difference K P P) (_ ↦ z)
      ≔ funext (Fin 3) (_ ↦ S) (standard_three_difference K P P) (_ ↦ z) (t ↦ R .add_laws .inv_right (P t)) in
    calc
      standard_three_sq_distance K P P = dot_product K 3 (_ ↦ z) (_ ↦ z)
        by refl ((x ↦ dot_product K 3 x x) : (Fin 3 → S) → S) zv
      = a (a (a z z) z) z by refl ((x ↦ a (a (a z x) x) x) : S → S) (ring_mul_zero_left R z)
      = a (a z z) z by refl ((y ↦ a (a y z) z) : S → S) (R .add_laws .unit_left z)
      = a z z by refl ((y ↦ a y z) : S → S) (R .add_laws .unit_left z)
      = z by R .add_laws .unit_left z ∎

def icosa_field_sq_distance (K : EuclideanField) (i j : IcosaIndex)
  : Id (ef_carrier K) (golden_to_field K (golden_sq_distance (golden_vertex i) (golden_vertex j)))
      (standard_three_sq_distance K (icosahedron_vertex K i) (icosahedron_vertex K j))
  ≔ let S ≔ ef_carrier K in let F ≔ Fin 3 → S in
    let vi ≔ funext (Fin 3) (_ ↦ S) (t ↦ golden_to_field K (golden_vertex i t)) (icosahedron_vertex K i) (golden_vertex_to_field K i) in
    let vj ≔ funext (Fin 3) (_ ↦ S) (t ↦ golden_to_field K (golden_vertex j t)) (icosahedron_vertex K j) (golden_vertex_to_field K j) in
    concat S (golden_to_field K (golden_sq_distance (golden_vertex i) (golden_vertex j)))
      (standard_three_sq_distance K (t ↦ golden_to_field K (golden_vertex i t)) (t ↦ golden_to_field K (golden_vertex j t)))
      (standard_three_sq_distance K (icosahedron_vertex K i) (icosahedron_vertex K j))
      (golden_sq_distance_to_field K (golden_vertex i) (golden_vertex j))
      (refl ((P Q ↦ standard_three_sq_distance K P Q) : F → F → S) vi vj)

{` The images of the four ℤ[φ] values. `}
def golden_to_field_four (K : EuclideanField)
  : Id (ef_carrier K) (golden_to_field K (pos. 4, pos. zero.)) (ring_of_nat (K .field .fst) 4)
  ≔ golden_to_field_nat K 4

def golden_to_field_eight_four (K : EuclideanField)
  : Id (ef_carrier K) (golden_to_field K (pos. 8, pos. 4))
      (K .field .fst .add (ring_of_nat (K .field .fst) 4) (golden_to_field K (pos. 4, pos. 4)))
  ≔ let S ≔ ef_carrier K in
    concat S (golden_to_field K (golden_add (pos. 4, pos. zero.) (pos. 4, pos. 4)))
      (K .field .fst .add (golden_to_field K (pos. 4, pos. zero.)) (golden_to_field K (pos. 4, pos. 4)))
      (K .field .fst .add (ring_of_nat (K .field .fst) 4) (golden_to_field K (pos. 4, pos. 4)))
      (golden_to_field_add K (pos. 4, pos. zero.) (pos. 4, pos. 4))
      (refl ((y ↦ K .field .fst .add y (golden_to_field K (pos. 4, pos. 4))) : S → S) (golden_to_field_four K))

def ef_four_nonzero (K : EuclideanField) (e : Id (ef_carrier K) (ring_of_nat (K .field .fst) 4) (K .field .fst .zero)) : Empty
  ≔ ef_nat_succ_nonzero K 3 e

def golden_four_four_nonneg (K : EuclideanField) : K .nonneg (golden_to_field K (pos. 4, pos. 4))
  ≔ let R ≔ K .field .fst in let r4 ≔ ring_of_nat R 4 in
    K .nonneg_add r4 (R .mul r4 (golden_ratio K)) (ef_nat_nonneg K 4)
      (K .nonneg_mul r4 (golden_ratio K) (ef_nat_nonneg K 4) (golden_ratio_nonneg K))

def golden_four_four_nonzero (K : EuclideanField)
  (e : Id (ef_carrier K) (golden_to_field K (pos. 4, pos. 4)) (K .field .fst .zero)) : Empty
  ≔ let R ≔ K .field .fst in let r4 ≔ ring_of_nat R 4 in
    ef_four_nonzero K
      (ef_sum_zero_left K r4 (R .mul r4 (golden_ratio K)) (ef_nat_nonneg K 4)
        (K .nonneg_mul r4 (golden_ratio K) (ef_nat_nonneg K 4) (golden_ratio_nonneg K)) e)

def golden_four_four_ne_four (K : EuclideanField)
  (e : Id (ef_carrier K) (golden_to_field K (pos. 4, pos. 4)) (ring_of_nat (K .field .fst) 4)) : Empty
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let G ≔ ring_additive_group R in
    let r4 ≔ ring_of_nat R 4 in let φ ≔ golden_ratio K in let X ≔ R .mul r4 φ in
    let X0 : Id S X (R .zero)
      ≔ ag_cancel_left G r4 X (R .zero)
          (concat S (R .add r4 X) r4 (R .add r4 (R .zero)) e (inverse S (R .add r4 (R .zero)) r4 (R .add_laws .unit_right r4))) in
    let φ0 : Id S φ (R .zero)
      ≔ ring_cancel_invertible R r4 (ef_inv K r4 (ef_four_nonzero K)) φ (R .zero)
          (concat S X (R .zero) (R .mul r4 (R .zero)) X0 (inverse S (R .mul r4 (R .zero)) (R .zero) (ring_mul_zero_right R r4))) in
    ef_non_trivial K
      (calc
         R .zero = R .mul (R .zero) (R .zero) by inverse S (R .mul (R .zero) (R .zero)) (R .zero) (ring_mul_zero_left R (R .zero))
         = R .mul φ φ by refl (R .mul) (inverse S φ (R .zero) φ0) (inverse S φ (R .zero) φ0)
         = R .add φ (R .one) by golden_ratio_square K
         = R .add (R .zero) (R .one) by refl ((y ↦ R .add y (R .one)) : S → S) φ0
         = R .one by R .add_laws .unit_left (R .one) ∎)

def golden_eight_four_nonzero (K : EuclideanField)
  (e : Id (ef_carrier K) (golden_to_field K (pos. 8, pos. 4)) (K .field .fst .zero)) : Empty
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let r4 ≔ ring_of_nat R 4 in
    let Y ≔ golden_to_field K (pos. 4, pos. 4) in
    ef_four_nonzero K
      (ef_sum_zero_left K r4 Y (ef_nat_nonneg K 4) (golden_four_four_nonneg K)
        (concat S (R .add r4 Y) (golden_to_field K (pos. 8, pos. 4)) (R .zero)
          (inverse S (golden_to_field K (pos. 8, pos. 4)) (R .add r4 Y) (golden_to_field_eight_four K)) e))

def golden_eight_four_ne_four (K : EuclideanField)
  (e : Id (ef_carrier K) (golden_to_field K (pos. 8, pos. 4)) (ring_of_nat (K .field .fst) 4)) : Empty
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let G ≔ ring_additive_group R in let r4 ≔ ring_of_nat R 4 in
    let Y ≔ golden_to_field K (pos. 4, pos. 4) in
    golden_four_four_nonzero K
      (ag_cancel_left G r4 Y (R .zero)
        (calc
           R .add r4 Y = golden_to_field K (pos. 8, pos. 4)
             by inverse S (golden_to_field K (pos. 8, pos. 4)) (R .add r4 Y) (golden_to_field_eight_four K)
           = r4 by e
           = R .add r4 (R .zero) by inverse S (R .add r4 (R .zero)) r4 (R .add_laws .unit_right r4) ∎))

{` The 12 vertices of the icosahedron over K are distinct. `}
def icosahedron_vertex_injective (K : EuclideanField) (i j : IcosaIndex)
  (e : Id (Fin 3 → ef_carrier K) (icosahedron_vertex K i) (icosahedron_vertex K j)) : Id IcosaIndex i j
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let ψ ≔ golden_to_field K in
    let g ≔ golden_sq_distance (golden_vertex i) (golden_vertex j) in
    let ψ0 : Id S (ψ g) (R .zero)
      ≔ concat S (ψ g) (standard_three_sq_distance K (icosahedron_vertex K i) (icosahedron_vertex K j)) (R .zero)
          (icosa_field_sq_distance K i j)
          (concat S (standard_three_sq_distance K (icosahedron_vertex K i) (icosahedron_vertex K j))
             (standard_three_sq_distance K (icosahedron_vertex K j) (icosahedron_vertex K j)) (R .zero)
             (refl ((P ↦ standard_three_sq_distance K P (icosahedron_vertex K j)) : (Fin 3 → S) → S) e)
             (standard_three_sq_distance_self K (icosahedron_vertex K j))) in
    match icosa_pair_class i j [
    | inl. u ↦ u .fst
    | inr. (inl. p) ↦
      match ef_four_nonzero K
        (concat S (ring_of_nat R 4) (ψ g) (R .zero)
          (inverse S (ψ g) (ring_of_nat R 4) (concat S (ψ g) (ψ (pos. 4, pos. zero.)) (ring_of_nat R 4) (refl ψ p) (golden_to_field_four K)))
          ψ0) [ ]
    | inr. (inr. (inl. p)) ↦
      match golden_four_four_nonzero K (concat S (ψ (pos. 4, pos. 4)) (ψ g) (R .zero) (inverse S (ψ g) (ψ (pos. 4, pos. 4)) (refl ψ p)) ψ0) [ ]
    | inr. (inr. (inr. p)) ↦
      match golden_eight_four_nonzero K (concat S (ψ (pos. 8, pos. 4)) (ψ g) (R .zero) (inverse S (ψ g) (ψ (pos. 8, pos. 4)) (refl ψ p)) ψ0) [ ] ]

{` Two vertices are at distance 2 in K iff their ℤ[φ] squared distance is 4. `}
def icosahedron_edge_iff (K : EuclideanField) (i j : IcosaIndex)
  : Product
      (Id (ef_carrier K) (standard_three_distance K (icosahedron_vertex K i) (icosahedron_vertex K j)) (ef_two K)
        → Id GoldenInt (golden_sq_distance (golden_vertex i) (golden_vertex j)) (pos. 4, pos. zero.))
      (Id GoldenInt (golden_sq_distance (golden_vertex i) (golden_vertex j)) (pos. 4, pos. zero.)
        → Id (ef_carrier K) (standard_three_distance K (icosahedron_vertex K i) (icosahedron_vertex K j)) (ef_two K))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let ψ ≔ golden_to_field K in
    let g ≔ golden_sq_distance (golden_vertex i) (golden_vertex j) in
    let D ≔ standard_three_difference K (icosahedron_vertex K i) (icosahedron_vertex K j) in
    let sq ≔ dot_product K 3 D D in
    let h ≔ dot_product_inner K 3 .nonneg D in
    let r4 ≔ ring_of_nat R 4 in
    let toψ : Id S sq r4 → Id S (ψ g) r4 ≔ q ↦ concat S (ψ g) sq r4 (icosa_field_sq_distance K i j) q in
    (e ↦
       let q : Id S sq r4
         ≔ calc
             sq = R .mul (K .sqrt sq h) (K .sqrt sq h) by inverse S (R .mul (K .sqrt sq h) (K .sqrt sq h)) sq (K .sqrt_square sq h)
             = R .mul (ef_two K) (ef_two K) by refl (R .mul) e e
             = r4 by ef_two_square K ∎ in
       let qψ ≔ toψ q in
       match icosa_pair_class i j [
       | inl. u ↦
         match ef_four_nonzero K
           (calc
              r4 = ψ g by inverse S (ψ g) r4 qψ
              = ψ golden_zero by refl ψ (u .snd)
              = R .zero by golden_to_field_zero K ∎) [ ]
       | inr. (inl. p) ↦ p
       | inr. (inr. (inl. p)) ↦
         match golden_four_four_ne_four K (concat S (ψ (pos. 4, pos. 4)) (ψ g) r4 (inverse S (ψ g) (ψ (pos. 4, pos. 4)) (refl ψ p)) qψ) [ ]
       | inr. (inr. (inr. p)) ↦
         match golden_eight_four_ne_four K (concat S (ψ (pos. 8, pos. 4)) (ψ g) r4 (inverse S (ψ g) (ψ (pos. 8, pos. 4)) (refl ψ p)) qψ) [ ] ],
     p ↦
       let q : Id S sq r4
         ≔ calc
             sq = ψ g by inverse S (ψ g) sq (icosa_field_sq_distance K i j)
             = ψ (pos. 4, pos. zero.) by refl ψ p
             = r4 by golden_to_field_four K ∎ in
       ef_sqrt_unique K sq h (ef_two K) (ef_two_nonneg K)
         (concat S (R .mul (ef_two K) (ef_two K)) r4 sq (ef_two_square K) (inverse S sq r4 q)))

{` "Distance 2" between vertices is decidable over K, decided by the ℤ[φ]
   computation; counting with this decision gives the counts of ℤ[φ]. `}
def icosahedron_edge_dec (K : EuclideanField) (i j : IcosaIndex)
  : Decidable (Id (ef_carrier K) (standard_three_distance K (icosahedron_vertex K i) (icosahedron_vertex K j)) (ef_two K))
  ≔ match golden_dec_eq (golden_sq_distance (golden_vertex i) (golden_vertex j)) (pos. 4, pos. zero.) [
    | inl. p ↦ inl. (icosahedron_edge_iff K i j .snd p)
    | inr. n ↦ inr. (q ↦ n (icosahedron_edge_iff K i j .fst q)) ]

def icosahedron_edge_indicator (K : EuclideanField) (i j : IcosaIndex) : Nat
  ≔ match icosahedron_edge_dec K i j [ inl. _ ↦ 1 | inr. _ ↦ 0 ]

def icosahedron_field_degree (K : EuclideanField) (i : IcosaIndex) : Nat
  ≔ sum_over_icosa_index (j ↦ icosahedron_edge_indicator K i j)

def icosahedron_field_edge_count (K : EuclideanField) : Id Nat (sum_over_icosa_index (i ↦ icosahedron_field_degree K i)) 60
  ≔ refl (60 : Nat)

def icosahedron_field_degree_five_cases (K : EuclideanField) (k : Fin 3) (b c : Bool)
  : Id Nat (icosahedron_field_degree K (k, (b, c))) 5
  ≔ match k [
    | inl. (inl. (inl. e)) ↦ match e [ ]
    | inl. (inl. (inr. star.)) ↦ match b, c [
      | true., true. ↦ refl (5 : Nat) | true., false. ↦ refl (5 : Nat)
      | false., true. ↦ refl (5 : Nat) | false., false. ↦ refl (5 : Nat) ]
    | inl. (inr. star.) ↦ match b, c [
      | true., true. ↦ refl (5 : Nat) | true., false. ↦ refl (5 : Nat)
      | false., true. ↦ refl (5 : Nat) | false., false. ↦ refl (5 : Nat) ]
    | inr. star. ↦ match b, c [
      | true., true. ↦ refl (5 : Nat) | true., false. ↦ refl (5 : Nat)
      | false., true. ↦ refl (5 : Nat) | false., false. ↦ refl (5 : Nat) ] ]

{` Every vertex of the icosahedron over K has exactly 5 vertices at
   distance 2. `}
def icosahedron_field_degree_five (K : EuclideanField) (i : IcosaIndex) : Id Nat (icosahedron_field_degree K i) 5
  ≔ icosahedron_field_degree_five_cases K (i .fst) (i .snd .fst) (i .snd .snd)
