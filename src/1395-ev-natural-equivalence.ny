export "1333-pointed-circle-evaluation"
export "616-loop-functor"

{` Chapter 13 (fields.tex:461, margin note after rem:pointing-ev): "ev_- is an example of a wild
   natural equivalence between the wild functors Ω, O : U_* → U_*". Ω is the wild functor LoopFunctor
   of chapter 6 (module 616, ex:loop-functor) and O is o_wild_functor (module 1332). The components are
   the pointed maps ev_A : O A →* Ω A of rem:pointing-ev; the naturality squares (cats.tex def:nat-trans,
   oriented Ω(f) ∘ ev_A = ev_B ∘ O(f)) are con:Omega-O (omega_o_square). LoopFunctor points Ω(f) by its
   own path induction, which differs from loops_pointed_map; maps into Ω B are determined by their
   underlying functions (cor:Id-(B->*loopsA)), so the square transfers. Every component is an isomorphism
   of the wild category PointedWild, since ev_A is a pointed equivalence (pointed_equivalence_is_iso). `}

def ev_wild_nat_trans (C : CircleSignature) : WildNatTrans PointedWild PointedWild (o_wild_functor C) LoopFunctor
  ≔ (component ≔ A ↦ pointed_circle_ev_pointed C A,
     natural ≔ A B f ↦
       loops_pointed_map_path_from_underlying B (circle_pointed_maps C A)
         (book_pointed_compose (circle_pointed_maps C A) (Omega A) (Omega B) (pointed_circle_ev_pointed C A)
           (loop_functor_map A B f))
         (book_pointed_compose (circle_pointed_maps C A) (circle_pointed_maps C B) (Omega B)
           (o_functor_map C A B f) (pointed_circle_ev_pointed C B))
         (omega_o_square C A B f .fst))

def ev_wild_nat_iso (C : CircleSignature) : NatIso PointedWild PointedWild (o_wild_functor C) LoopFunctor
  ≔ (ev_wild_nat_trans C,
     A ↦ pointed_equivalence_is_iso (circle_pointed_maps C A) (Omega A, pointed_circle_ev_pointed_equiv C A))
