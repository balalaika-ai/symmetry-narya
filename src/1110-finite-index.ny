export "504-torsors"

{` def:finite-index (fggroups.tex:609) and the claims after it (613-618).

   A subgroup of G (Subgroups G, chapter 5: a transitive G-set X : BG → Set with
   a point of X(sh_G)) has finite index m if X is a family of finite sets of
   cardinality m: every X(z) is merely equal to Fin m (GSetHasIndex).  The
   definition does not mention the point, so it is the same for all conjugates
   (subgroup_index_point_independent, line 615).  Line 613: this holds iff
   X(sh_G) has cardinality m (gset_index_iff_shape; BG is connected).  Line 618:
   the classifying type of the subgroup is Σ_{t:BG} X(t), pointed by the chosen
   point (subgroup_group_classifying, module 502, holds by refl). `}

def GSetHasIndex (G : Group) (X : GSet G) (m : Nat) : Type
  ≔ (z : BG G .carrier) → Mere (Id Type (X z .fst) (Fin m))

def SubgroupHasIndex (G : Group) (H : Subgroups G) (m : Nat) : Type ≔ GSetHasIndex G (H .gset) m

def gset_has_index_prop (G : Group) (X : GSet G) (m : Nat) : isProp (GSetHasIndex G X m)
  ≔ pi_prop (BG G .carrier) (z ↦ Mere (Id Type (X z .fst) (Fin m))) (z ↦ mere_isprop (Id Type (X z .fst) (Fin m)))

{` Line 613: finite index m iff the set acted on, X(sh_G), has cardinality m. `}
def gset_index_iff_shape (G : Group) (X : GSet G) (m : Nat)
  : Product (GSetHasIndex G X m → Mere (Id Type (gset_underlying G X) (Fin m)))
      (Mere (Id Type (gset_underlying G X) (Fin m)) → GSetHasIndex G X m)
  ≔ (h ↦ h (shape G),
     h z ↦ mere_rec (Id (BG G .carrier) (shape G) z) (Mere (Id Type (X z .fst) (Fin m)))
       (mere_isprop (Id Type (X z .fst) (Fin m)))
       (p ↦ transport (BG G .carrier) (w ↦ Mere (Id Type (X w .fst) (Fin m))) (shape G) z p h)
       (bg_connected G .snd (shape G) z))

{` Line 615: the index does not depend on the chosen point. `}
def subgroup_index_point_independent (G : Group) (H : Subgroups G) (x : gset_underlying G (H .gset)) (m : Nat)
  : Id Type (SubgroupHasIndex G H m) (SubgroupHasIndex G (H .gset, x, H .transitive) m)
  ≔ refl (SubgroupHasIndex G H m)

{` The underlying set of a finite-index G-set is finite of cardinality m. `}
def gset_index_finite (G : Group) (X : GSet G) (m : Nat) (h : GSetHasIndex G X m) (z : BG G .carrier)
  : IsFinite (X z .fst)
  ≔ mere_rec (Id Type (X z .fst) (Fin m)) (IsFinite (X z .fst)) (mere_isprop (Σ Nat (k ↦ Id Type (X z .fst) (Fin k))))
      (p ↦ mere (Σ Nat (k ↦ Id Type (X z .fst) (Fin k))) (m, p)) (h z)
