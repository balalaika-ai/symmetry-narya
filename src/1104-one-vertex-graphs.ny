export "1103-graph-quotient-steps"
export "882-free-group-bridge"

{` fggroups.tex, remark at line 279: for the graph (1, S) on one vertex with an
   S-indexed family of edges, 1/S is "essentially the same" as B F_S.

   The one-vertex type 1 is OneVertex ≔ sig () (a unit type with judgmental η),
   so boundary data on (1, S) and boundary data of def:bfree correspond
   judgmentally.  free_to_one_vertex and one_vertex_to_free turn a
   FreeGroupSignature S into a graph quotient of (1, S) with the same carrier,
   base and loops, and conversely; the two constructions are mutually inverse on
   the nose (free_one_vertex_roundtrip_*).

   Remark at line 106 (notation a, A = a⁻¹): letters are SignedLetter S with
   inl. a = a, inr. a = A (module 861); the claim aA = Aa = 1 is
   free_word_cancel_pair (for every free group signature) and its litmus
   instances for the constructed F_{a,b}. `}

def OneVertex : Type ≔ sig ()

def one_vertex : OneVertex ≔ ()

def OneVertexEdges (S : Type) (u v : OneVertex) : Type ≔ S

def free_to_one_vertex (S : Type) (F : FreeGroupSignature S) : GraphQuotientSignature OneVertex (OneVertexEdges S)
  ≔ (F .carrier, _ ↦ F .base, _ _ s ↦ F .loop s,
     P d ↦
       let r ≔ F .induction P (d .fst (), s ↦ d .snd () () s) in
       (r .fst,
        refl ((b : free_boundary S F P) ↦
            ((_ ↦ b .fst, _ _ s ↦ b .snd s)
              : GraphQuotientBoundary OneVertex (OneVertexEdges S) (F .carrier) (_ ↦ F .base) (_ _ s ↦ F .loop s) P))
          (r .snd)))

def one_vertex_to_free (S : Type) (G : GraphQuotientSignature OneVertex (OneVertexEdges S)) : FreeGroupSignature S
  ≔ (G .carrier, G .vertex (), s ↦ G .edge () () s,
     P d ↦
       let r ≔ G .induction P (_ ↦ d .fst, _ _ s ↦ d .snd s) in
       (r .fst,
        refl ((b : gq_boundary OneVertex (OneVertexEdges S) G P) ↦
            ((b .fst (), s ↦ b .snd () () s)
              : FreeGroupBoundary S (G .carrier) (G .vertex ()) (s ↦ G .edge () () s) P))
          (r .snd)))

{` The underlying data correspond on the nose. `}
def free_one_vertex_carrier (S : Type) (F : FreeGroupSignature S)
  : Id Type (free_to_one_vertex S F .carrier) (F .carrier)
  ≔ refl (F .carrier)

def free_one_vertex_base (S : Type) (F : FreeGroupSignature S)
  : Id (F .carrier) (one_vertex_to_free S (free_to_one_vertex S F) .base) (F .base)
  ≔ refl (F .base)

def free_one_vertex_loop (S : Type) (F : FreeGroupSignature S) (s : S)
  : Id (Id (F .carrier) (F .base) (F .base)) (one_vertex_to_free S (free_to_one_vertex S F) .loop s) (F .loop s)
  ≔ refl (F .loop s)

{` Remark 279: 1/S ≃ B F_S, for every graph quotient of (1, S) and every free
   group signature (pointed: [()] ↦ base). `}
def one_vertex_free_equiv (S : Type) (G : GraphQuotientSignature OneVertex (OneVertexEdges S)) (F : FreeGroupSignature S)
  : Equiv (G .carrier) (F .carrier)
  ≔ graph_quotient_equiv OneVertex (OneVertexEdges S) G (free_to_one_vertex S F)

def one_vertex_free_equiv_base (S : Type) (G : GraphQuotientSignature OneVertex (OneVertexEdges S)) (F : FreeGroupSignature S)
  : Id (F .carrier) (one_vertex_free_equiv S G F .map (G .vertex ())) (F .base)
  ≔ graph_quotient_map_vertex OneVertex (OneVertexEdges S) G (free_to_one_vertex S F) ()

{` B F_T as a graph quotient of (1, T), for T with decidable equality (constructed, no HITs). `}
def constructed_one_vertex_quotient (T : Type) (dec : DecidableEquality T)
  : GraphQuotientSignature OneVertex (OneVertexEdges T)
  ≔ free_to_one_vertex T (constructed_free_group_signature T dec)

{` Remark 106: aA = Aa = 1. `}
def free_word_cancel_pair (S : Type) (dec : DecidableEquality S) (F : FreeGroupSignature S) (x : SignedLetter S)
  : Id (USym (free_group S dec F)) (free_group_word S dec F (cons. x (cons. (letter_complement S x) nil.)))
      (usym_unit (free_group S dec F))
  ≔ let w ≔ (cons. x (cons. (letter_complement S x) nil.) : SignedWord S) in
    concat (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F w)
      (free_word_interpretation S F (word_reduction S dec w)) (refl (F .base))
      (inverse (Id (F .carrier) (F .base) (F .base)) (free_word_interpretation S F (word_reduction S dec w))
        (free_word_interpretation S F w) (free_word_interpretation_reduction S dec F w))
      (refl (free_word_interpretation S F) (word_reduction_cancel_pair S dec x nil.))

def free_bool_aA (F : FreeGroupSignature Bool)
  : Id (USym (free_group Bool fw_bool_decidable_equality F))
      (free_group_word Bool fw_bool_decidable_equality F (cons. fw_letter_a (cons. fw_letter_A nil.)))
      (usym_unit (free_group Bool fw_bool_decidable_equality F))
  ≔ free_word_cancel_pair Bool fw_bool_decidable_equality F fw_letter_a

def free_bool_Aa (F : FreeGroupSignature Bool)
  : Id (USym (free_group Bool fw_bool_decidable_equality F))
      (free_group_word Bool fw_bool_decidable_equality F (cons. fw_letter_A (cons. fw_letter_a nil.)))
      (usym_unit (free_group Bool fw_bool_decidable_equality F))
  ≔ free_word_cancel_pair Bool fw_bool_decidable_equality F fw_letter_A
