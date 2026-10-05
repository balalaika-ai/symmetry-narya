export "566-wedge-circle-gsets"
export "569-wedge-lagrange"
export "865-free-group"
export "879-free-sum-wedges"
export "880-free-groups-iterated-wedges"
export "848-decidable-sums-of-groups"

{` Chapter 5: discharging the hypothesis isGroupoid(S¹ ∨ S¹) of
   xca:not-normal (module 566) and xca:lagrange-if-subgr-not-normal
   (module 569).

   A CircleWedgeSignature (module 566: a point and two loops with the
   dependent eliminator) is the same thing as a FreeGroupSignature on Bool
   (def:bfree, module 860): the two loops are the loops indexed by true and
   false, and the boundary data correspond by splitting a Bool-indexed
   family into its two values (the computation law is transferred along
   this correspondence, using funext over Bool). Chapter 8 proves that the
   carrier of every free-group signature on a set with decidable equality
   is a groupoid (free_signature_groupoid, module 865, by encode-decode with
   reduced words, thm:free-group-elements). Hence the carrier of EVERY
   CircleWedgeSignature is a groupoid (circle_wedge_carrier_groupoid), and
   the results of 566/569 hold with no hypothesis (the *_unconditional
   declarations below).

   Non-vacuity: chapter 8's constructed free group on Bool (no HITs, no
   axioms) gives an instance constructed_circle_wedge_signature, whose
   carrier is by definition the carrier of chapter 8's constructed
   S¹ ∨ S¹ (constructed_circle_wedge, a WedgeSignature of two constructed
   circles, module 879), and whose group mkgroup(S¹ ∨ S¹) is chapter 8's
   free group F_2 = free_bool_group. Conversely, every CircleWedgeSignature
   yields a chapter-8 WedgeSignature of two copies of any circle with the
   same carrier (circle_wedge_to_wedge_signature, via
   circle_wedge_from_free_bool of module 879), and every chapter-8 wedge
   signature of two copies of a circle C is a groupoid and is pointed-equal
   to it (chapter8_circle_wedge_groupoid, chapter8_circle_wedge_pointed_path). `}

{` The two loops as a Bool-indexed family (true ↦ loop₁, false ↦ loop₂). `}
def circle_wedge_loop_family (W : CircleWedgeSignature) (b : Bool) : Id (W .carrier) (W .base) (W .base)
  ≔ match b [ true. ↦ W .loop1 | false. ↦ W .loop2 ]

def circle_wedge_boundary_to_free (W : CircleWedgeSignature) (P : W .carrier → Type)
  (u : CircleWedgeBoundary (W .carrier) (W .base) (W .loop1) (W .loop2) P)
  : FreeGroupBoundary Bool (W .carrier) (W .base) (circle_wedge_loop_family W) P
  ≔ (u .fst, b ↦ match b [ true. ↦ u .snd .fst | false. ↦ u .snd .snd ])

def circle_wedge_boundary_from_free (W : CircleWedgeSignature) (P : W .carrier → Type)
  (d : FreeGroupBoundary Bool (W .carrier) (W .base) (circle_wedge_loop_family W) P)
  : CircleWedgeBoundary (W .carrier) (W .base) (W .loop1) (W .loop2) P
  ≔ (d .fst, (d .snd true., d .snd false.))

def circle_wedge_boundary_free_eta (W : CircleWedgeSignature) (P : W .carrier → Type)
  (d : FreeGroupBoundary Bool (W .carrier) (W .base) (circle_wedge_loop_family W) P)
  : Id (FreeGroupBoundary Bool (W .carrier) (W .base) (circle_wedge_loop_family W) P)
      (circle_wedge_boundary_to_free W P (circle_wedge_boundary_from_free W P d)) d
  ≔ (refl (d .fst),
     funext Bool (b ↦ Id P (circle_wedge_loop_family W b) (d .fst) (d .fst))
       (circle_wedge_boundary_to_free W P (circle_wedge_boundary_from_free W P d) .snd) (d .snd)
       (b ↦ match b [ true. ↦ refl (d .snd true.) | false. ↦ refl (d .snd false.) ]))

def circle_wedge_evaluate_free (W : CircleWedgeSignature) (P : W .carrier → Type) (f : (x : W .carrier) → P x)
  : Id (FreeGroupBoundary Bool (W .carrier) (W .base) (circle_wedge_loop_family W) P)
      (free_group_evaluate Bool (W .carrier) (W .base) (circle_wedge_loop_family W) P f)
      (circle_wedge_boundary_to_free W P (circle_wedge_evaluate (W .carrier) (W .base) (W .loop1) (W .loop2) P f))
  ≔ (refl (f (W .base)),
     funext Bool (b ↦ Id P (circle_wedge_loop_family W b) (f (W .base)) (f (W .base)))
       (b ↦ refl f (circle_wedge_loop_family W b))
       (circle_wedge_boundary_to_free W P (circle_wedge_evaluate (W .carrier) (W .base) (W .loop1) (W .loop2) P f) .snd)
       (b ↦ match b [ true. ↦ refl (refl f (W .loop1)) | false. ↦ refl (refl f (W .loop2)) ]))

{` Every CircleWedgeSignature is a free-group signature on Bool. `}
def circle_wedge_free_signature (W : CircleWedgeSignature) : FreeGroupSignature Bool
  ≔ (W .carrier, W .base, circle_wedge_loop_family W,
     P d ↦
       let r ≔ W .induction P (circle_wedge_boundary_from_free W P d) in
       let B ≔ FreeGroupBoundary Bool (W .carrier) (W .base) (circle_wedge_loop_family W) P in
       let c ≔ circle_wedge_boundary_to_free W P (circle_wedge_evaluate (W .carrier) (W .base) (W .loop1) (W .loop2) P (r .fst)) in
       (r .fst,
        concat B (free_group_evaluate Bool (W .carrier) (W .base) (circle_wedge_loop_family W) P (r .fst)) c d
          (circle_wedge_evaluate_free W P (r .fst))
          (concat B c (circle_wedge_boundary_to_free W P (circle_wedge_boundary_from_free W P d)) d
            (refl (circle_wedge_boundary_to_free W P) (r .snd))
            (circle_wedge_boundary_free_eta W P d))))

{` S¹ ∨ S¹ is a groupoid (for every signature), by chapter 8's
   encode-decode for free groups. `}
def circle_wedge_carrier_groupoid (W : CircleWedgeSignature) : isGroupoid (W .carrier)
  ≔ free_signature_groupoid Bool fw_bool_decidable_equality (circle_wedge_free_signature W)

{` Conversely every free-group signature on Bool is a CircleWedgeSignature. `}
def free_bool_boundary_restrict (F : FreeGroupSignature Bool) (P : F .carrier → Type)
  (u : FreeGroupBoundary Bool (F .carrier) (F .base) (F .loop) P)
  : CircleWedgeBoundary (F .carrier) (F .base) (F .loop true.) (F .loop false.) P
  ≔ (u .fst, (u .snd true., u .snd false.))

def free_bool_boundary_lift (F : FreeGroupSignature Bool) (P : F .carrier → Type)
  (d : CircleWedgeBoundary (F .carrier) (F .base) (F .loop true.) (F .loop false.) P)
  : FreeGroupBoundary Bool (F .carrier) (F .base) (F .loop) P
  ≔ (d .fst, b ↦ match b [ true. ↦ d .snd .fst | false. ↦ d .snd .snd ])

def free_bool_circle_wedge_signature (F : FreeGroupSignature Bool) : CircleWedgeSignature
  ≔ (F .carrier, F .base, F .loop true., F .loop false.,
     P d ↦ (F .induction P (free_bool_boundary_lift F P d) .fst,
       refl (free_bool_boundary_restrict F P) (F .induction P (free_bool_boundary_lift F P d) .snd)))

{` Every CircleWedgeSignature gives a chapter-8 wedge signature of two
   copies of any circle C, with the same carrier. `}
def circle_wedge_to_wedge_signature (W : CircleWedgeSignature) (C : CircleSignature)
  : WedgeSignature (circle_pointed C) (circle_pointed C)
  ≔ circle_wedge_from_free_bool (circle_wedge_free_signature W) C

def circle_wedge_to_wedge_signature_carrier (W : CircleWedgeSignature) (C : CircleSignature)
  : Id Type (circle_wedge_to_wedge_signature W C .carrier) (W .carrier)
  ≔ refl (W .carrier)

{` Chapter 8's side: the carrier of every chapter-8 wedge signature of two
   copies of a circle is a groupoid (lem:wedgeofgpoidisgpoid, via
   decidable_sum_groupoid of module 848), and it is identified as a pointed
   type with the wedge obtained from any CircleWedgeSignature (uniqueness of
   wedges, module 880). `}
def chapter8_circle_wedge_groupoid (C : CircleSignature) (V : WedgeSignature (circle_pointed C) (circle_pointed C))
  : isGroupoid (V .carrier)
  ≔ decidable_sum_groupoid (circle_group C) (circle_group C) V (circle_group_decidable C) (circle_group_decidable C)

def chapter8_circle_wedge_pointed_path (C : CircleSignature) (V : WedgeSignature (circle_pointed C) (circle_pointed C))
  (W : CircleWedgeSignature)
  : Id Pointed (wedge_pointed (circle_pointed C) (circle_pointed C) V)
      (wedge_pointed (circle_pointed C) (circle_pointed C) (circle_wedge_to_wedge_signature W C))
  ≔ wedge_signatures_pointed_path (circle_pointed C) (circle_pointed C) V (circle_wedge_to_wedge_signature W C)

{` The instance: S¹ ∨ S¹ without HITs, from chapter 8's constructed free
   group on Bool. `}
def constructed_circle_wedge_signature : CircleWedgeSignature
  ≔ free_bool_circle_wedge_signature (constructed_free_group_signature Bool fw_bool_decidable_equality)

def constructed_circle_wedge_signature_carrier
  : Id Type (constructed_circle_wedge_signature .carrier) (constructed_circle_wedge .carrier)
  ≔ refl (constructed_circle_wedge .carrier)

{` G ≔ mkgroup(S¹ ∨ S¹), now without hypothesis. `}
def circle_wedge_free_group (W : CircleWedgeSignature) : Group
  ≔ circle_wedge_group W (circle_wedge_carrier_groupoid W)

{` For the instance, mkgroup(S¹ ∨ S¹) is chapter 8's F_2. `}
def constructed_circle_wedge_group_path
  : Id Group (circle_wedge_free_group constructed_circle_wedge_signature) free_bool_group
  ≔ equiv_inverse_map (Id Group (circle_wedge_free_group constructed_circle_wedge_signature) free_bool_group)
      (Id Pointed (BG (circle_wedge_free_group constructed_circle_wedge_signature)) (BG free_bool_group))
      (group_path_pointed_equiv (circle_wedge_free_group constructed_circle_wedge_signature) free_bool_group)
      (refl (BG free_bool_group))

{` The results of modules 566 and 569 without the groupoid hypothesis. `}
def wedge_gset_unconditional (W : CircleWedgeSignature) : GSet (circle_wedge_free_group W)
  ≔ wedge_gset W (circle_wedge_carrier_groupoid W)

def wedge_gset_symmetries_contractible_unconditional (W : CircleWedgeSignature)
  : BookIsContr (Id (GSet (circle_wedge_free_group W)) (wedge_gset_unconditional W) (wedge_gset_unconditional W))
  ≔ wedge_gset_symmetries_contractible W (circle_wedge_carrier_groupoid W)

def wedge_gset_transitive_unconditional (W : CircleWedgeSignature)
  : IsTransitive (circle_wedge_free_group W) (wedge_gset_unconditional W)
  ≔ wedge_gset_transitive W (circle_wedge_carrier_groupoid W)

def wedge_subgroup_unconditional (W : CircleWedgeSignature) : Subgroups (circle_wedge_free_group W)
  ≔ wedge_subgroup W (circle_wedge_carrier_groupoid W)

def wedge_eval_injective_unconditional (W : CircleWedgeSignature) (x : wedge_family W (W .base) .fst)
  : IsEmbedding (Id (GSet (circle_wedge_free_group W)) (wedge_gset_unconditional W) (wedge_gset_unconditional W))
      (wedge_family W (W .base) .fst)
      (gset_path_eval (circle_wedge_free_group W) (wedge_gset_unconditional W) (wedge_gset_unconditional W) (W .base) x)
  ≔ wedge_eval_injective W (circle_wedge_carrier_groupoid W) x

def wedge_eval_not_surjective_unconditional (W : CircleWedgeSignature) (x : wedge_family W (W .base) .fst)
  (h : Surjective (Id (GSet (circle_wedge_free_group W)) (wedge_gset_unconditional W) (wedge_gset_unconditional W))
        (wedge_family W (W .base) .fst)
        (gset_path_eval (circle_wedge_free_group W) (wedge_gset_unconditional W) (wedge_gset_unconditional W) (W .base) x))
  : Empty
  ≔ wedge_eval_not_surjective W (circle_wedge_carrier_groupoid W) x h

{` xca:not-normal, unconditionally. `}
def wedge_gset_not_normal_unconditional (W : CircleWedgeSignature)
  (h : IsNormalGSet (circle_wedge_free_group W) (wedge_gset_unconditional W)) : Empty
  ≔ wedge_gset_not_normal W (circle_wedge_carrier_groupoid W) h

{` xca:lagrange-if-subgr-not-normal, unconditionally. `}
def wedge_lagrange_equiv_unconditional (W : CircleWedgeSignature)
  : Equiv (USym (circle_wedge_free_group W))
      (Product (wedge_family W (W .base) .fst)
        (USym (subgroup_group (circle_wedge_free_group W) (wedge_subgroup_unconditional W))))
  ≔ wedge_lagrange_equiv W (circle_wedge_carrier_groupoid W)

def wedge_lagrange_fin3_equiv_unconditional (W : CircleWedgeSignature)
  : Equiv (USym (circle_wedge_free_group W))
      (Product (Fin three) (USym (subgroup_group (circle_wedge_free_group W) (wedge_subgroup_unconditional W))))
  ≔ wedge_lagrange_fin3_equiv W (circle_wedge_carrier_groupoid W)

{` Litmus: for the constructed S¹ ∨ S¹, F_2 has a non-normal subgroup of
   index 3. `}
def constructed_wedge_gset_not_normal
  (h : IsNormalGSet (circle_wedge_free_group constructed_circle_wedge_signature)
        (wedge_gset_unconditional constructed_circle_wedge_signature)) : Empty
  ≔ wedge_gset_not_normal_unconditional constructed_circle_wedge_signature h
