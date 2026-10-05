export "480-product-bicycle-automorphisms"

{` Cayley bicycles (auxiliary for the exercise at group.tex 2303). For a
   group G and symmetries g, h : USym G, the family of bicycles over BG
     z ↦ (sh_G = z, p ↦ p·g, p ↦ p·h)        (p·g = concat g p)
   is defined when the bicycle at z = sh_G is connected (g and h generate
   G). Its fiber at sh_G is the Cayley bicycle (USym G, −·g, −·h), and the
   induced pointed map BG → Bicyc_(Cay) is an equivalence:
   G = Aut_Bicyc(Cay(G; g, h)) (cayley_bicycle_group_path). `}

def cayley_torsor (G : Group) (z : BG G .carrier) : Type ≔ Id (BG G .carrier) (shape G) z

def cayley_torsor_set (G : Group) (z : BG G .carrier) : SetTypes
  ≔ (cayley_torsor G z, bg_groupoid G (shape G) z)

def cayley_right_mul (G : Group) (g : USym G) (z : BG G .carrier) : Equiv (cayley_torsor G z) (cayley_torsor G z)
  ≔ let A ≔ BG G .carrier in let s ≔ shape G in
    quasi_inverse_equiv (cayley_torsor G z) (cayley_torsor G z)
      (p ↦ concat A s s z g p) (p ↦ concat A s s z (inverse A s s g) p)
      (p ↦ calc
        concat A s s z (inverse A s s g) (concat A s s z g p)
        = concat A s s z (concat A s s s (inverse A s s g) g) p
          by inverse (Id A s z) (concat A s s z (concat A s s s (inverse A s s g) g) p)
            (concat A s s z (inverse A s s g) (concat A s s z g p)) (concat_assoc A s s s z (inverse A s s g) g p)
        = concat A s s z (refl s) p
          by refl ((r ↦ concat A s s z r p) : Id A s s → Id A s z) (concat_inverse_left A s s g)
        = p by concat_1p A s z p ∎)
      (p ↦ calc
        concat A s s z g (concat A s s z (inverse A s s g) p)
        = concat A s s z (concat A s s s g (inverse A s s g)) p
          by inverse (Id A s z) (concat A s s z (concat A s s s g (inverse A s s g)) p)
            (concat A s s z g (concat A s s z (inverse A s s g) p)) (concat_assoc A s s s z g (inverse A s s g) p)
        = concat A s s z (refl s) p
          by refl ((r ↦ concat A s s z r p) : Id A s s → Id A s z) (concat_inverse_right A s s g)
        = p by concat_1p A s z p ∎)

def CayleyGenerating (G : Group) (g h : USym G) : Type
  ≔ BicycleConnected (USym G) (cayley_right_mul G g (shape G)) (cayley_right_mul G h (shape G))

def cayley_family_connected (G : Group) (g h : USym G) (gen : CayleyGenerating G g h) (z : BG G .carrier)
  : BicycleConnected (cayley_torsor G z) (cayley_right_mul G g z) (cayley_right_mul G h z)
  ≔ mere_rec (Id (BG G .carrier) (shape G) z)
      (BicycleConnected (cayley_torsor G z) (cayley_right_mul G g z) (cayley_right_mul G h z))
      (bicycle_connected_prop (cayley_torsor G z) (cayley_right_mul G g z) (cayley_right_mul G h z))
      (q ↦ transport (BG G .carrier)
        (w ↦ BicycleConnected (cayley_torsor G w) (cayley_right_mul G g w) (cayley_right_mul G h w))
        (shape G) z q gen)
      (bg_connected G .snd (shape G) z)

def cayley_bicycle_family (G : Group) (g h : USym G) (gen : CayleyGenerating G g h) (z : BG G .carrier) : Bicycles
  ≔ mkbicycle (cayley_torsor_set G z) (cayley_right_mul G g z) (cayley_right_mul G h z)
      (cayley_family_connected G g h gen z)

def cayley_bicycle (G : Group) (g h : USym G) (gen : CayleyGenerating G g h) : Bicycles
  ≔ cayley_bicycle_family G g h gen (shape G)

{` A loop ℓ at sh_G acts on the Cayley bicycle by p ↦ p·ℓ⁻¹... precisely by
   transport in z ↦ (sh = z), which is concat p ℓ. `}
def cayley_loop_evaluate (G : Group) (g h : USym G) (gen : CayleyGenerating G g h) (l : USym G) (p : USym G)
  : Id (USym G)
      (bicycle_path_evaluate (cayley_bicycle G g h gen) (cayley_bicycle G g h gen)
        (refl (cayley_bicycle_family G g h gen) l) p)
      (concat (BG G .carrier) (shape G) (shape G) (shape G) p l)
  ≔ refl (concat (BG G .carrier) (shape G) (shape G) (shape G) p l)

def cayley_component_map (G : Group) (g h : USym G) (gen : CayleyGenerating G g h) (z : BG G .carrier)
  : NativeComponent Bicycles (cayley_bicycle G g h gen)
  ≔ (cayley_bicycle_family G g h gen z,
      mere_rec (Id (BG G .carrier) (shape G) z) (Mere (Id Bicycles (cayley_bicycle G g h gen) (cayley_bicycle_family G g h gen z)))
        (mere_isprop (Id Bicycles (cayley_bicycle G g h gen) (cayley_bicycle_family G g h gen z)))
        (q ↦ mere (Id Bicycles (cayley_bicycle G g h gen) (cayley_bicycle_family G g h gen z))
          (refl (cayley_bicycle_family G g h gen) q))
        (bg_connected G .snd (shape G) z))

def cayley_loops_path_reflecting (G : Group) (g h : USym G) (gen : CayleyGenerating G g h)
  : PathReflecting (USym G)
      (Id (NativeComponent Bicycles (cayley_bicycle G g h gen))
        (cayley_component_map G g h gen (shape G)) (cayley_component_map G g h gen (shape G)))
      (map_path (BG G .carrier) (NativeComponent Bicycles (cayley_bicycle G g h gen)) (cayley_component_map G g h gen)
        (shape G) (shape G))
  ≔ let A ≔ BG G .carrier in let s ≔ shape G in
    let Cay ≔ cayley_bicycle G g h gen in
    let Fz ≔ cayley_component_map G g h gen in
    l l' q ↦ calc
      l = concat A s s s (refl s) l by inverse (USym G) (concat A s s s (refl s) l) l (concat_1p A s s l)
      = concat A s s s (refl s) l'
        by refl ((r ↦ bicycle_path_evaluate Cay Cay (r .fst) (refl s))
            : Id (NativeComponent Bicycles Cay) (Fz s) (Fz s) → USym G) q
      = l' by concat_1p A s s l' ∎

def cayley_loops_surjective (G : Group) (g h : USym G) (gen : CayleyGenerating G g h)
  : Surjective (USym G)
      (Id (NativeComponent Bicycles (cayley_bicycle G g h gen))
        (cayley_component_map G g h gen (shape G)) (cayley_component_map G g h gen (shape G)))
      (map_path (BG G .carrier) (NativeComponent Bicycles (cayley_bicycle G g h gen)) (cayley_component_map G g h gen)
        (shape G) (shape G))
  ≔ let A ≔ BG G .carrier in let s ≔ shape G in
    let Cay ≔ cayley_bicycle G g h gen in
    let Fz ≔ cayley_component_map G g h gen in
    let C ≔ NativeComponent Bicycles Cay in
    let CP ≔ component_path_equiv Bicycles Cay (Fz s) (Fz s) in
    lam ↦ mere (BookFiber (USym G) (Id C (Fz s) (Fz s)) (map_path A C Fz s s) lam)
      (let l ≔ bicycle_path_evaluate Cay Cay (lam .fst) (refl s) in
       let fst_eq : Id (Id Bicycles Cay Cay) (lam .fst) (refl (cayley_bicycle_family G g h gen) l)
         ≔ bicycle_evaluation_path_reflecting Cay Cay (refl s) (lam .fst) (refl (cayley_bicycle_family G g h gen) l)
             (inverse (USym G) (concat A s s s (refl s) l) l (concat_1p A s s l)) in
       (l, calc
         lam = equiv_inverse_map (Id C (Fz s) (Fz s)) (Id Bicycles Cay Cay) CP (CP .map lam)
           by inverse (Id C (Fz s) (Fz s)) (equiv_inverse_map (Id C (Fz s) (Fz s)) (Id Bicycles Cay Cay) CP (CP .map lam)) lam
             (equiv_retraction (Id C (Fz s) (Fz s)) (Id Bicycles Cay Cay) CP lam)
         = equiv_inverse_map (Id C (Fz s) (Fz s)) (Id Bicycles Cay Cay) CP (CP .map (map_path A C Fz s s l))
           by refl (equiv_inverse_map (Id C (Fz s) (Fz s)) (Id Bicycles Cay Cay) CP) fst_eq
         = map_path A C Fz s s l by equiv_retraction (Id C (Fz s) (Fz s)) (Id Bicycles Cay Cay) CP (map_path A C Fz s s l) ∎))

def cayley_loops_equiv (G : Group) (g h : USym G) (gen : CayleyGenerating G g h)
  : BookIsEquiv (USym G)
      (Id (NativeComponent Bicycles (cayley_bicycle G g h gen))
        (cayley_component_map G g h gen (shape G)) (cayley_component_map G g h gen (shape G)))
      (map_path (BG G .carrier) (NativeComponent Bicycles (cayley_bicycle G g h gen)) (cayley_component_map G g h gen)
        (shape G) (shape G))
  ≔ let A ≔ BG G .carrier in let s ≔ shape G in
    let Cay ≔ cayley_bicycle G g h gen in
    let C ≔ NativeComponent Bicycles Cay in
    let Fz ≔ cayley_component_map G g h gen in
    embedding_surjection_equiv native_truncation (USym G) (Id C (Fz s) (Fz s)) (map_path A C Fz s s)
      (path_reflecting_set_embedding (USym G) (Id C (Fz s) (Fz s))
        (component_groupoid Bicycles bicycles_groupoid Cay (Fz s) (Fz s))
        (map_path A C Fz s s) (cayley_loops_path_reflecting G g h gen))
      (cayley_loops_surjective G g h gen) .equiv

def cayley_component_equiv (G : Group) (g h : USym G) (gen : CayleyGenerating G g h)
  : BookEquiv (BG G .carrier) (NativeComponent Bicycles (cayley_bicycle G g h gen))
  ≔ native_connected_map_equiv_from_loops (BG G .carrier) (NativeComponent Bicycles (cayley_bicycle G g h gen))
      (cayley_component_map G g h gen) (bg_connected G)
      (native_component_connected Bicycles (cayley_bicycle G g h gen)) (shape G)
      (cayley_loops_equiv G g h gen)

{` G = Aut_Bicyc(Cay(G; g, h)) when g, h generate. `}
def cayley_bicycle_group_path (G : Group) (g h : USym G) (gen : CayleyGenerating G g h)
  : Id Group G (bicycle_automorphism_group (cayley_bicycle G g h gen))
  ≔ group_path_from_pointed_equiv G (bicycle_automorphism_group (cayley_bicycle G g h gen))
      ((cayley_component_map G g h gen,
        component_path Bicycles (cayley_bicycle G g h gen)
          (component_point Bicycles (cayley_bicycle G g h gen)) (cayley_component_map G g h gen (shape G))
          (refl (cayley_bicycle G g h gen))),
       cayley_component_equiv G g h gen .equiv)
