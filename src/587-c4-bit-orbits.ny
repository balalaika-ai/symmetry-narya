export "586-c4-bit-sequences"

{` exa:prep-burnside (part 2): the six orbits of the C_4-set of binary
   sequences of length 4, decided by computation.

   Method: Fin 4 → Fin 2 is enumerated by Fin 16 (bits4_decode_equiv), and
   statements quantified over all sequences are proved by Boolean
   reflection: a closed Boolean check over all 16 (or 256) cases normalises to
   true (refl), and soundness lemmas turn it into the typed statement.

   Results: x and y lie in the same orbit iff they have the same orbit index
   (bits4_same_orbit_equiv), iff y is a cyclic rotation of x
   (bits4_same_orbit_rotation_equiv); X/C_4 ≃ Fin 6 (bits4_orbits_equiv), so
   there are six orbits; the orbit C_4 · x has 1, 1, 4, 4, 2, 4 elements in the
   six rows of fig:C4-action-on-4-bits (bits4_orbit_underlying_equiv). `}

def c4bits_six : Nat ≔ suc. (suc. (suc. (suc. (suc. (suc. zero.)))))

def c4bits_sixteen : Nat
  ≔ suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))))))))

def Bits4Code : Type ≔ Fin c4bits_sixteen

def bits4_r0 : Fin c4bits_six ≔ inr. star.
def bits4_r1 : Fin c4bits_six ≔ inl. (inr. star.)
def bits4_r2 : Fin c4bits_six ≔ inl. (inl. (inr. star.))
def bits4_r3 : Fin c4bits_six ≔ inl. (inl. (inl. (inr. star.)))
def bits4_r4 : Fin c4bits_six ≔ inl. (inl. (inl. (inl. (inr. star.))))
def bits4_r5 : Fin c4bits_six ≔ inl. (inl. (inl. (inl. (inl. (inr. star.)))))

{` Case analysis on the six rows. `}
def bits4_row_ind (P : Fin c4bits_six → Type) (h0 : P bits4_r0) (h1 : P bits4_r1) (h2 : P bits4_r2)
  (h3 : P bits4_r3) (h4 : P bits4_r4) (h5 : P bits4_r5) (r : Fin c4bits_six) : P r
  ≔ match r [
  | inr. star. ↦ h0
  | inl. (inr. star.) ↦ h1
  | inl. (inl. (inr. star.)) ↦ h2
  | inl. (inl. (inl. (inr. star.))) ↦ h3
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ h4
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ h5
  | inl. (inl. (inl. (inl. (inl. (inl. e))))) ↦ match e [] ]

{` The enumeration Fin 16 → Bits4: code j ↦ the binary expansion of j,
   most significant bit at position 0 (j = 1 ↦ 0001). `}
def bits4_decode : Bits4Code → Bits4 ≔ [
  | inr. star. ↦ bits4_mk bits4_o bits4_o bits4_o bits4_o
  | inl. (inr. star.) ↦ bits4_mk bits4_o bits4_o bits4_o bits4_l
  | inl. (inl. (inr. star.)) ↦ bits4_mk bits4_o bits4_o bits4_l bits4_o
  | inl. (inl. (inl. (inr. star.))) ↦ bits4_mk bits4_o bits4_o bits4_l bits4_l
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ bits4_mk bits4_o bits4_l bits4_o bits4_o
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ bits4_mk bits4_o bits4_l bits4_o bits4_l
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ bits4_mk bits4_o bits4_l bits4_l bits4_o
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ bits4_mk bits4_o bits4_l bits4_l bits4_l
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))) ↦ bits4_mk bits4_l bits4_o bits4_o bits4_o
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))) ↦ bits4_mk bits4_l bits4_o bits4_o bits4_l
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))) ↦ bits4_mk bits4_l bits4_o bits4_l bits4_o
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))) ↦ bits4_mk bits4_l bits4_o bits4_l bits4_l
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))) ↦ bits4_mk bits4_l bits4_l bits4_o bits4_o
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))) ↦ bits4_mk bits4_l bits4_l bits4_o bits4_l
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))))) ↦ bits4_mk bits4_l bits4_l bits4_l bits4_o
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))))) ↦ bits4_mk bits4_l bits4_l bits4_l bits4_l
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))))))))))) ↦ match e [] ]

def bits4_encode_mk (a b c d : Fin two) : Bits4Code
  ≔ match a [
    | inr. star. ↦ match b [
      | inr. star. ↦ match c [
        | inr. star. ↦ match d [
          | inr. star. ↦ (inr. star. : Bits4Code)
          | inl. (inr. star.) ↦ (inl. (inr. star.) : Bits4Code)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inr. star.) ↦ match d [
          | inr. star. ↦ (inl. (inl. (inr. star.)) : Bits4Code)
          | inl. (inr. star.) ↦ (inl. (inl. (inl. (inr. star.))) : Bits4Code)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inl. e) ↦ match e [] ]
      | inl. (inr. star.) ↦ match c [
        | inr. star. ↦ match d [
          | inr. star. ↦ (inl. (inl. (inl. (inl. (inr. star.)))) : Bits4Code)
          | inl. (inr. star.) ↦ (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Bits4Code)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inr. star.) ↦ match d [
          | inr. star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Bits4Code)
          | inl. (inr. star.) ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Bits4Code)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inl. e) ↦ match e [] ]
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inr. star.) ↦ match b [
      | inr. star. ↦ match c [
        | inr. star. ↦ match d [
          | inr. star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))) : Bits4Code)
          | inl. (inr. star.) ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))) : Bits4Code)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inr. star.) ↦ match d [
          | inr. star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))) : Bits4Code)
          | inl. (inr. star.) ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))) : Bits4Code)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inl. e) ↦ match e [] ]
      | inl. (inr. star.) ↦ match c [
        | inr. star. ↦ match d [
          | inr. star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))) : Bits4Code)
          | inl. (inr. star.) ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))) : Bits4Code)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inr. star.) ↦ match d [
          | inr. star. ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))))) : Bits4Code)
          | inl. (inr. star.) ↦ (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))))) : Bits4Code)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inl. e) ↦ match e [] ]
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inl. e) ↦ match e [] ]

def bits4_decode_encode_mk (a b c d : Fin two)
  : Id Bits4 (bits4_decode (bits4_encode_mk a b c d)) (bits4_mk a b c d)
  ≔ match a [
    | inr. star. ↦ match b [
      | inr. star. ↦ match c [
        | inr. star. ↦ match d [
          | inr. star. ↦ refl (bits4_mk bits4_o bits4_o bits4_o bits4_o)
          | inl. (inr. star.) ↦ refl (bits4_mk bits4_o bits4_o bits4_o bits4_l)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inr. star.) ↦ match d [
          | inr. star. ↦ refl (bits4_mk bits4_o bits4_o bits4_l bits4_o)
          | inl. (inr. star.) ↦ refl (bits4_mk bits4_o bits4_o bits4_l bits4_l)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inl. e) ↦ match e [] ]
      | inl. (inr. star.) ↦ match c [
        | inr. star. ↦ match d [
          | inr. star. ↦ refl (bits4_mk bits4_o bits4_l bits4_o bits4_o)
          | inl. (inr. star.) ↦ refl (bits4_mk bits4_o bits4_l bits4_o bits4_l)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inr. star.) ↦ match d [
          | inr. star. ↦ refl (bits4_mk bits4_o bits4_l bits4_l bits4_o)
          | inl. (inr. star.) ↦ refl (bits4_mk bits4_o bits4_l bits4_l bits4_l)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inl. e) ↦ match e [] ]
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inr. star.) ↦ match b [
      | inr. star. ↦ match c [
        | inr. star. ↦ match d [
          | inr. star. ↦ refl (bits4_mk bits4_l bits4_o bits4_o bits4_o)
          | inl. (inr. star.) ↦ refl (bits4_mk bits4_l bits4_o bits4_o bits4_l)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inr. star.) ↦ match d [
          | inr. star. ↦ refl (bits4_mk bits4_l bits4_o bits4_l bits4_o)
          | inl. (inr. star.) ↦ refl (bits4_mk bits4_l bits4_o bits4_l bits4_l)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inl. e) ↦ match e [] ]
      | inl. (inr. star.) ↦ match c [
        | inr. star. ↦ match d [
          | inr. star. ↦ refl (bits4_mk bits4_l bits4_l bits4_o bits4_o)
          | inl. (inr. star.) ↦ refl (bits4_mk bits4_l bits4_l bits4_o bits4_l)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inr. star.) ↦ match d [
          | inr. star. ↦ refl (bits4_mk bits4_l bits4_l bits4_l bits4_o)
          | inl. (inr. star.) ↦ refl (bits4_mk bits4_l bits4_l bits4_l bits4_l)
          | inl. (inl. e) ↦ match e [] ]
        | inl. (inl. e) ↦ match e [] ]
      | inl. (inl. e) ↦ match e [] ]
    | inl. (inl. e) ↦ match e [] ]

def bits4_encode (x : Bits4) : Bits4Code ≔ bits4_encode_mk (x bits4_p0) (x bits4_p1) (x bits4_p2) (x bits4_p3)

def bits4_encode_decode (j : Bits4Code) : Id Bits4Code (bits4_encode (bits4_decode j)) j ≔ match j [
  | inr. star. ↦ refl (inr. star. : Bits4Code)
  | inl. (inr. star.) ↦ refl (inl. (inr. star.) : Bits4Code)
  | inl. (inl. (inr. star.)) ↦ refl (inl. (inl. (inr. star.)) : Bits4Code)
  | inl. (inl. (inl. (inr. star.))) ↦ refl (inl. (inl. (inl. (inr. star.))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ refl (inl. (inl. (inl. (inl. (inr. star.)))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))))) : Bits4Code)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))))))))))) ↦ match e [] ]

{` The orbit index of a code (rows of fig:C4-action-on-4-bits: 0 ↦ {0000},
   1 ↦ {1111}, 2 ↦ one 1, 3 ↦ one 0, 4 ↦ {0101, 1010}, 5 ↦ two adjacent 1s). `}
def bits4_orbit_index_code : Bits4Code → Fin c4bits_six ≔ [
  | inr. star. ↦ inr. star.
  | inl. (inr. star.) ↦ inl. (inl. (inr. star.))
  | inl. (inl. (inr. star.)) ↦ inl. (inl. (inr. star.))
  | inl. (inl. (inl. (inr. star.))) ↦ inl. (inl. (inl. (inl. (inl. (inr. star.)))))
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ inl. (inl. (inr. star.))
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ inl. (inl. (inl. (inl. (inr. star.))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. star.)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ inl. (inl. (inl. (inr. star.)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))) ↦ inl. (inl. (inr. star.))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. star.)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))) ↦ inl. (inl. (inl. (inl. (inr. star.))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))) ↦ inl. (inl. (inl. (inr. star.)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. star.)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))) ↦ inl. (inl. (inl. (inr. star.)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))))))))))) ↦ inl. (inl. (inl. (inr. star.)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))))) ↦ inl. (inr. star.)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (e)))))))))))))))) ↦ match e [] ]

{` The chosen representatives 0000, 1111, 0001, 0111, 0101, 0011. `}
def bits4_row_rep : Fin c4bits_six → Bits4 ≔ [
  | inr. star. ↦ bits4_decode (inr. star.)
  | inl. (inr. star.) ↦ bits4_decode (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))))))))))
  | inl. (inl. (inr. star.)) ↦ bits4_decode (inl. (inr. star.))
  | inl. (inl. (inl. (inr. star.))) ↦ bits4_decode (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))))
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ bits4_decode (inl. (inl. (inl. (inl. (inl. (inr. star.))))))
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ bits4_decode (inl. (inl. (inl. (inr. star.))))
  | inl. (inl. (inl. (inl. (inl. (inl. (e)))))) ↦ match e [] ]


def bits4_decode_encode (x : Bits4) : Id Bits4 (bits4_decode (bits4_encode x)) x
  ≔ concat Bits4 (bits4_decode (bits4_encode x)) (bits4_mk (x bits4_p0) (x bits4_p1) (x bits4_p2) (x bits4_p3)) x
      (bits4_decode_encode_mk (x bits4_p0) (x bits4_p1) (x bits4_p2) (x bits4_p3)) (bits4_mk_eta x)

{` Fin 16 ≃ (Fin 4 → Fin 2). `}
def bits4_decode_equiv : Equiv Bits4Code Bits4
  ≔ quasi_inverse_equiv Bits4Code Bits4 bits4_decode bits4_encode bits4_encode_decode bits4_decode_encode

{` Boolean reflection kit. `}
def bits4_and (a b : Bool) : Bool ≔ match a [ false. ↦ false. | true. ↦ b ]

def bits4_or (a b : Bool) : Bool ≔ match a [ false. ↦ b | true. ↦ true. ]

def bits4_implies (a b : Bool) : Bool ≔ match a [ false. ↦ true. | true. ↦ b ]

def bits4_and_left (a b : Bool) : Id Bool (bits4_and a b) true. → Id Bool a true.
  ≔ match a [ false. ↦ h ↦ h | true. ↦ _ ↦ refl (true. : Bool) ]

def bits4_and_right (a b : Bool) : Id Bool (bits4_and a b) true. → Id Bool b true.
  ≔ match a [ false. ↦ h ↦ absurd (Id Bool b true.) (bool_encode false. true. h) | true. ↦ h ↦ h ]

def bits4_and_intro (a b : Bool) : Id Bool a true. → Id Bool b true. → Id Bool (bits4_and a b) true.
  ≔ match a [ false. ↦ ha _ ↦ ha | true. ↦ _ hb ↦ hb ]

def bits4_or_elim (a b : Bool) : Id Bool (bits4_or a b) true. → Sum (Id Bool a true.) (Id Bool b true.)
  ≔ match a [ false. ↦ h ↦ inr. h | true. ↦ _ ↦ inl. (refl (true. : Bool)) ]

def bits4_or_left (a b : Bool) : Id Bool a true. → Id Bool (bits4_or a b) true.
  ≔ match a [ false. ↦ h ↦ absurd (Id Bool b true.) (bool_encode false. true. h) | true. ↦ _ ↦ refl (true. : Bool) ]

def bits4_or_right (a b : Bool) : Id Bool b true. → Id Bool (bits4_or a b) true.
  ≔ match a [ false. ↦ h ↦ h | true. ↦ _ ↦ refl (true. : Bool) ]

def bits4_implies_mp (a b : Bool) : Id Bool (bits4_implies a b) true. → Id Bool a true. → Id Bool b true.
  ≔ match a [ false. ↦ _ ha ↦ absurd (Id Bool b true.) (bool_encode false. true. ha) | true. ↦ h _ ↦ h ]

def bits4_bool_eqb (a b : Bool) : Bool ≔ match a [ false. ↦ bool_not b | true. ↦ b ]

def bits4_bool_eqb_sound (a b : Bool) : Id Bool (bits4_bool_eqb a b) true. → Id Bool a b
  ≔ match a [
  | false. ↦ match b [
    | false. ↦ _ ↦ refl (false. : Bool)
    | true. ↦ h ↦ absurd (Id Bool false. true.) (bool_encode false. true. h) ]
  | true. ↦ match b [
    | false. ↦ h ↦ absurd (Id Bool true. false.) (bool_encode false. true. h)
    | true. ↦ _ ↦ refl (true. : Bool) ] ]

{` Conjunction over Fin n. `}
def bits4_fin_all (n : Nat) (b : Fin n → Bool) : Bool
  ≔ match n [ zero. ↦ true. | suc. m ↦ bits4_and (bits4_fin_all m (i ↦ b (inl. i))) (b (inr. star.)) ]

def bits4_fin_all_sound (n : Nat) (b : Fin n → Bool) (h : Id Bool (bits4_fin_all n b) true.) (i : Fin n)
  : Id Bool (b i) true.
  ≔ match n [
  | zero. ↦ match i []
  | suc. m ↦ match i [
    | inl. i' ↦ bits4_fin_all_sound m (j ↦ b (inl. j))
        (bits4_and_left (bits4_fin_all m (j ↦ b (inl. j))) (b (inr. star.)) h) i'
    | inr. star. ↦ bits4_and_right (bits4_fin_all m (j ↦ b (inl. j))) (b (inr. star.)) h ] ]

def bits4_fin_all_complete (n : Nat) (b : Fin n → Bool) (h : (i : Fin n) → Id Bool (b i) true.)
  : Id Bool (bits4_fin_all n b) true.
  ≔ match n [
  | zero. ↦ refl (true. : Bool)
  | suc. m ↦ bits4_and_intro (bits4_fin_all m (j ↦ b (inl. j))) (b (inr. star.))
      (bits4_fin_all_complete m (j ↦ b (inl. j)) (j ↦ h (inl. j))) (h (inr. star.)) ]

{` Conjunction over all 16 sequences, and over the four positions. `}
def bits4_all (P : Bits4 → Bool) : Bool ≔ bits4_fin_all c4bits_sixteen (j ↦ P (bits4_decode j))

def bits4_all_sound (P : Bits4 → Bool) (h : Id Bool (bits4_all P) true.) (x : Bits4) : Id Bool (P x) true.
  ≔ transport Bits4 (y ↦ Id Bool (P y) true.) (bits4_decode (bits4_encode x)) x (bits4_decode_encode x)
      (bits4_fin_all_sound c4bits_sixteen (j ↦ P (bits4_decode j)) h (bits4_encode x))

def bits4_pos_all (b : Bits4Pos → Bool) : Bool ≔ bits4_fin_all c4bits_four b

{` Decidable equality of sequences (pointwise). `}
def bits4_dec (x y : Bits4) : Decidable (Id Bits4 x y)
  ≔ match fin_decidable_equality two (x bits4_p0) (y bits4_p0) [
  | inr. n ↦ inr. (p ↦ n (p (refl bits4_p0)))
  | inl. e0 ↦ match fin_decidable_equality two (x bits4_p1) (y bits4_p1) [
    | inr. n ↦ inr. (p ↦ n (p (refl bits4_p1)))
    | inl. e1 ↦ match fin_decidable_equality two (x bits4_p2) (y bits4_p2) [
      | inr. n ↦ inr. (p ↦ n (p (refl bits4_p2)))
      | inl. e2 ↦ match fin_decidable_equality two (x bits4_p3) (y bits4_p3) [
        | inr. n ↦ inr. (p ↦ n (p (refl bits4_p3)))
        | inl. e3 ↦ inl. (funext Bits4Pos (_ ↦ Fin two) x y
            (bits4_pos_ind (i ↦ Id (Fin two) (x i) (y i)) e0 e1 e2 e3)) ] ] ] ]

def bits4_eqb (x y : Bits4) : Bool ≔ decision_bool (Id Bits4 x y) (bits4_dec x y)

def bits4_eqb_sound (x y : Bits4) (h : Id Bool (bits4_eqb x y) true.) : Id Bits4 x y
  ≔ decision_bool_reflect (Id Bits4 x y) (bits4_dec x y) h

def bits4_eqb_complete (x y : Bits4) (p : Id Bits4 x y) : Id Bool (bits4_eqb x y) true.
  ≔ decision_bool_true (Id Bits4 x y) (bits4_dec x y) p

def bits4_row_eqb (r s : Fin c4bits_six) : Bool
  ≔ decision_bool (Id (Fin c4bits_six) r s) (fin_decidable_equality c4bits_six r s)

def bits4_row_eqb_sound (r s : Fin c4bits_six) (h : Id Bool (bits4_row_eqb r s) true.) : Id (Fin c4bits_six) r s
  ≔ decision_bool_reflect (Id (Fin c4bits_six) r s) (fin_decidable_equality c4bits_six r s) h

def bits4_row_eqb_complete (r s : Fin c4bits_six) (p : Id (Fin c4bits_six) r s) : Id Bool (bits4_row_eqb r s) true.
  ≔ decision_bool_true (Id (Fin c4bits_six) r s) (fin_decidable_equality c4bits_six r s) p

{` The row (orbit index) of a sequence in fig:C4-action-on-4-bits. `}
def bits4_orbit_index (x : Bits4) : Fin c4bits_six ≔ bits4_orbit_index_code (bits4_encode x)

def bits4_row_rep_index (r : Fin c4bits_six) : Id (Fin c4bits_six) (bits4_orbit_index (bits4_row_rep r)) r
  ≔ bits4_row_ind (r' ↦ Id (Fin c4bits_six) (bits4_orbit_index (bits4_row_rep r')) r')
      (refl bits4_r0) (refl bits4_r1) (refl bits4_r2) (refl bits4_r3) (refl bits4_r4) (refl bits4_r5) r

{` The orbit index is invariant under rotation (checked on all 16 × 4 cases). `}
def bits4_index_rot_check
  : Id Bool (bits4_all (x ↦ bits4_pos_all (k ↦
      bits4_row_eqb (bits4_orbit_index (bits4_rot k x)) (bits4_orbit_index x)))) true.
  ≔ refl (true. : Bool)

def bits4_orbit_index_rot (k : Bits4Pos) (x : Bits4)
  : Id (Fin c4bits_six) (bits4_orbit_index (bits4_rot k x)) (bits4_orbit_index x)
  ≔ bits4_row_eqb_sound (bits4_orbit_index (bits4_rot k x)) (bits4_orbit_index x)
      (bits4_fin_all_sound c4bits_four
        (k' ↦ bits4_row_eqb (bits4_orbit_index (bits4_rot k' x)) (bits4_orbit_index x))
        (bits4_all_sound (x' ↦ bits4_pos_all (k' ↦
            bits4_row_eqb (bits4_orbit_index (bits4_rot k' x')) (bits4_orbit_index x')))
          bits4_index_rot_check x) k)

{` A rotation aligning x with y (the first k with rot_k x = y, if any). `}
def bits4_first (b0 b1 b2 : Bool) : Bits4Pos
  ≔ match b0 [
  | true. ↦ bits4_p0
  | false. ↦ match b1 [ true. ↦ bits4_p1 | false. ↦ match b2 [ true. ↦ bits4_p2 | false. ↦ bits4_p3 ] ] ]

def bits4_align (x y : Bits4) : Bits4Pos
  ≔ bits4_first (bits4_eqb (bits4_rot bits4_p0 x) y) (bits4_eqb (bits4_rot bits4_p1 x) y)
      (bits4_eqb (bits4_rot bits4_p2 x) y)

{` Same orbit index implies being rotations of each other (all 256 pairs). `}
def bits4_align_check
  : Id Bool (bits4_all (x ↦ bits4_all (y ↦ bits4_implies
      (bits4_row_eqb (bits4_orbit_index x) (bits4_orbit_index y))
      (bits4_eqb (bits4_rot (bits4_align x y) x) y)))) true.
  ≔ refl (true. : Bool)

def bits4_align_rot (x y : Bits4) (e : Id (Fin c4bits_six) (bits4_orbit_index x) (bits4_orbit_index y))
  : Id Bits4 (bits4_rot (bits4_align x y) x) y
  ≔ let Q : Bits4 → Bits4 → Bool ≔ x' y' ↦ bits4_implies
        (bits4_row_eqb (bits4_orbit_index x') (bits4_orbit_index y'))
        (bits4_eqb (bits4_rot (bits4_align x' y') x') y') in
    bits4_eqb_sound (bits4_rot (bits4_align x y) x) y
      (bits4_implies_mp (bits4_row_eqb (bits4_orbit_index x) (bits4_orbit_index y))
        (bits4_eqb (bits4_rot (bits4_align x y) x) y)
        (bits4_all_sound (Q x) (bits4_all_sound (x' ↦ bits4_all (Q x')) bits4_align_check x) y)
        (bits4_row_eqb_complete (bits4_orbit_index x) (bits4_orbit_index y) e))

def bits4_orbit_relation_index (x y : Bits4) (r : OrbitRelation c4bits_group bits4_gset x y)
  : Id (Fin c4bits_six) (bits4_orbit_index x) (bits4_orbit_index y)
  ≔ mere_rec (Σ (USym c4bits_group) (g ↦ Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) y))
      (Id (Fin c4bits_six) (bits4_orbit_index x) (bits4_orbit_index y))
      (fin_set c4bits_six (bits4_orbit_index x) (bits4_orbit_index y))
      (u ↦ calc
        bits4_orbit_index x
        = bits4_orbit_index (bits4_rot (bits4_index (u .fst)) x)
          by inverse (Fin c4bits_six) (bits4_orbit_index (bits4_rot (bits4_index (u .fst)) x)) (bits4_orbit_index x)
               (bits4_orbit_index_rot (bits4_index (u .fst)) x)
        = bits4_orbit_index (gset_usym_act c4bits_group bits4_gset (u .fst) x)
          by refl bits4_orbit_index (inverse Bits4 (gset_usym_act c4bits_group bits4_gset (u .fst) x)
               (bits4_rot (bits4_index (u .fst)) x) (bits4_act_rot (u .fst) x))
        = bits4_orbit_index y by refl bits4_orbit_index (u .snd) ∎) r

def bits4_index_orbit_relation (x y : Bits4) (e : Id (Fin c4bits_six) (bits4_orbit_index x) (bits4_orbit_index y))
  : OrbitRelation c4bits_group bits4_gset x y
  ≔ mere (Σ (USym c4bits_group) (g ↦ Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) y))
      (bits4_symmetry (bits4_align x y),
       concat Bits4 (gset_usym_act c4bits_group bits4_gset (bits4_symmetry (bits4_align x y)) x)
         (bits4_rot (bits4_align x y) x) y (bits4_symmetry_act (bits4_align x y) x) (bits4_align_rot x y e))

{` [x] = [y] iff x and y lie in the same row of fig:C4-action-on-4-bits. `}
def bits4_same_orbit_equiv (x y : Bits4)
  : Equiv (Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
      (Id (Fin c4bits_six) (bits4_orbit_index x) (bits4_orbit_index y))
  ≔ iff_equiv
      (Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
      (Id (Fin c4bits_six) (bits4_orbit_index x) (bits4_orbit_index y))
      (orbits_set c4bits_group bits4_gset (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
      (fin_set c4bits_six (bits4_orbit_index x) (bits4_orbit_index y))
      (p ↦ bits4_orbit_relation_index x y (orbit_relation_from_path c4bits_group bits4_gset x y p))
      (e ↦ orbit_relation_to_path c4bits_group bits4_gset x y (bits4_index_orbit_relation x y e))

{` exa:prep-burnside: "the equivalence class of any x consists precisely of
   all cyclic rotations of x". `}
def bits4_same_orbit_rotation_equiv (x y : Bits4)
  : Equiv (Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
      (Mere (Σ Bits4Pos (k ↦ Id Bits4 (bits4_rot k x) y)))
  ≔ let R ≔ Σ (USym c4bits_group) (g ↦ Id Bits4 (gset_usym_act c4bits_group bits4_gset g x) y) in
    let K ≔ Σ Bits4Pos (k ↦ Id Bits4 (bits4_rot k x) y) in
    iff_equiv
      (Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
      (Mere K)
      (orbits_set c4bits_group bits4_gset (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
      (mere_isprop K)
      (p ↦ mere_rec R (Mere K) (mere_isprop K)
        (u ↦ mere K (bits4_index (u .fst),
          concat Bits4 (bits4_rot (bits4_index (u .fst)) x) (gset_usym_act c4bits_group bits4_gset (u .fst) x) y
            (inverse Bits4 (gset_usym_act c4bits_group bits4_gset (u .fst) x) (bits4_rot (bits4_index (u .fst)) x)
              (bits4_act_rot (u .fst) x)) (u .snd)))
        (orbit_relation_from_path c4bits_group bits4_gset x y p))
      (m ↦ orbit_relation_to_path c4bits_group bits4_gset x y
        (mere_rec K (OrbitRelation c4bits_group bits4_gset x y) (mere_isprop R)
          (v ↦ mere R (bits4_symmetry (v .fst),
            concat Bits4 (gset_usym_act c4bits_group bits4_gset (bits4_symmetry (v .fst)) x) (bits4_rot (v .fst) x) y
              (bits4_symmetry_act (v .fst) x) (v .snd))) m))

{` X/C_4 ≃ Fin 6: the six rows are the six orbits. `}
def bits4_orbit_of_row (r : Fin c4bits_six) : Orbits c4bits_group bits4_gset
  ≔ orbit_of_point c4bits_group bits4_gset (bits4_row_rep r)

def bits4_orbit_of_row_reflects : PathReflecting (Fin c4bits_six) (Orbits c4bits_group bits4_gset) bits4_orbit_of_row
  ≔ r s p ↦ calc
      r = bits4_orbit_index (bits4_row_rep r)
        by inverse (Fin c4bits_six) (bits4_orbit_index (bits4_row_rep r)) r (bits4_row_rep_index r)
      = bits4_orbit_index (bits4_row_rep s) by bits4_same_orbit_equiv (bits4_row_rep r) (bits4_row_rep s) .map p
      = s by bits4_row_rep_index s ∎

def bits4_orbit_of_row_surjective : Surjective (Fin c4bits_six) (Orbits c4bits_group bits4_gset) bits4_orbit_of_row
  ≔ O ↦ mere_rec (BookFiber Bits4 (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset) O)
      (Mere (BookFiber (Fin c4bits_six) (Orbits c4bits_group bits4_gset) bits4_orbit_of_row O))
      (mere_isprop (BookFiber (Fin c4bits_six) (Orbits c4bits_group bits4_gset) bits4_orbit_of_row O))
      (u ↦ mere (BookFiber (Fin c4bits_six) (Orbits c4bits_group bits4_gset) bits4_orbit_of_row O)
        (bits4_orbit_index (u .fst),
         concat (Orbits c4bits_group bits4_gset) O (orbit_of_point c4bits_group bits4_gset (u .fst))
           (bits4_orbit_of_row (bits4_orbit_index (u .fst))) (u .snd)
           (equiv_inverse_map
             (Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset (u .fst))
               (bits4_orbit_of_row (bits4_orbit_index (u .fst))))
             (Id (Fin c4bits_six) (bits4_orbit_index (u .fst)) (bits4_orbit_index (bits4_row_rep (bits4_orbit_index (u .fst)))))
             (bits4_same_orbit_equiv (u .fst) (bits4_row_rep (bits4_orbit_index (u .fst))))
             (inverse (Fin c4bits_six) (bits4_orbit_index (bits4_row_rep (bits4_orbit_index (u .fst))))
               (bits4_orbit_index (u .fst)) (bits4_row_rep_index (bits4_orbit_index (u .fst)))))))
      (orbit_of_point_surjective c4bits_group bits4_gset O)

def bits4_orbits_equiv : BookEquiv (Fin c4bits_six) (Orbits c4bits_group bits4_gset)
  ≔ embedding_surjection_equiv native_truncation (Fin c4bits_six) (Orbits c4bits_group bits4_gset) bits4_orbit_of_row
      (path_reflecting_set_embedding (Fin c4bits_six) (Orbits c4bits_group bits4_gset) (orbits_set c4bits_group bits4_gset)
        bits4_orbit_of_row bits4_orbit_of_row_reflects)
      bits4_orbit_of_row_surjective

def bits4_orbits_fin_equiv : Equiv (Orbits c4bits_group bits4_gset) (Fin c4bits_six)
  ≔ canonical_inverse_equiv (Fin c4bits_six) (Orbits c4bits_group bits4_gset)
      (native_equivalence (Fin c4bits_six) (Orbits c4bits_group bits4_gset) bits4_orbits_equiv)

def bits4_orbits_finite : IsFinite (Orbits c4bits_group bits4_gset)
  ≔ finite_from_equiv (Orbits c4bits_group bits4_gset) c4bits_six bits4_orbits_fin_equiv

{` "Thus we have distributed all 16 sequences over six orbits". `}
def bits4_orbits_card (h : IsFinite (Orbits c4bits_group bits4_gset))
  : Id Nat (cardinality (Orbits c4bits_group bits4_gset) h) c4bits_six
  ≔ cardinality_from_path (Orbits c4bits_group bits4_gset) h c4bits_six
      (ua (Orbits c4bits_group bits4_gset) (Fin c4bits_six) bits4_orbits_fin_equiv)

{` Counting sequences with a decidable property. `}
def bits4_sigma_bool_equiv (P : Bits4 → Bool)
  : Equiv (Σ Bits4 (y ↦ Id Bool (P y) true.)) (Fin (true_count c4bits_sixteen (j ↦ P (bits4_decode j))))
  ≔ compose_equiv (Σ Bits4 (y ↦ Id Bool (P y) true.)) (BoolCarrier c4bits_sixteen (j ↦ P (bits4_decode j)))
      (Fin (true_count c4bits_sixteen (j ↦ P (bits4_decode j))))
      (canonical_inverse_equiv (BoolCarrier c4bits_sixteen (j ↦ P (bits4_decode j))) (Σ Bits4 (y ↦ Id Bool (P y) true.))
        (sigma_pullback_equiv Bits4Code Bits4 bits4_decode_equiv (y ↦ Id Bool (P y) true.)))
      (bool_carrier_fin c4bits_sixteen (j ↦ P (bits4_decode j)))

{` Sizes of the six orbits (left column of fig:C4-action-on-4-bits). `}
def bits4_row_size (r : Fin c4bits_six) : Nat
  ≔ bits4_row_ind (_ ↦ Nat) (suc. zero.) (suc. zero.) c4bits_four c4bits_four two c4bits_four r

def bits4_row_count (r : Fin c4bits_six) : Nat
  ≔ true_count c4bits_sixteen (j ↦ bits4_row_eqb r (bits4_orbit_index (bits4_decode j)))

def bits4_row_count_size (r : Fin c4bits_six) : Id Nat (bits4_row_count r) (bits4_row_size r)
  ≔ bits4_row_ind (r' ↦ Id Nat (bits4_row_count r') (bits4_row_size r'))
      (refl (suc. zero. : Nat)) (refl (suc. zero. : Nat)) (refl c4bits_four) (refl c4bits_four) (refl two)
      (refl c4bits_four) r

def bits4_orbit_underlying_equiv (x : Bits4)
  : Equiv (OrbitUnderlying c4bits_group bits4_gset x) (Fin (bits4_row_size (bits4_orbit_index x)))
  ≔ let r ≔ bits4_orbit_index x in
    let P : Bits4 → Bool ≔ y ↦ bits4_row_eqb r (bits4_orbit_index y) in
    compose_equiv (OrbitUnderlying c4bits_group bits4_gset x) (Σ Bits4 (y ↦ Id Bool (P y) true.))
      (Fin (bits4_row_size r))
      (family_equiv Bits4
        (y ↦ Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
        (y ↦ Id Bool (P y) true.)
        (y ↦ compose_equiv
          (Id (Orbits c4bits_group bits4_gset) (orbit_of_point c4bits_group bits4_gset x) (orbit_of_point c4bits_group bits4_gset y))
          (Id (Fin c4bits_six) r (bits4_orbit_index y)) (Id Bool (P y) true.)
          (bits4_same_orbit_equiv x y)
          (iff_equiv (Id (Fin c4bits_six) r (bits4_orbit_index y)) (Id Bool (P y) true.)
            (fin_set c4bits_six r (bits4_orbit_index y)) (bool_set (P y) true.)
            (bits4_row_eqb_complete r (bits4_orbit_index y)) (bits4_row_eqb_sound r (bits4_orbit_index y)))))
      (compose_equiv (Σ Bits4 (y ↦ Id Bool (P y) true.)) (Fin (bits4_row_count r)) (Fin (bits4_row_size r))
        (bits4_sigma_bool_equiv P)
        (transport_equiv (Fin (bits4_row_count r)) (Fin (bits4_row_size r)) (refl Fin (bits4_row_count_size r))))

def bits4_orbit_finite (x : Bits4) : IsFinite (OrbitUnderlying c4bits_group bits4_gset x)
  ≔ finite_from_equiv (OrbitUnderlying c4bits_group bits4_gset x) (bits4_row_size (bits4_orbit_index x))
      (bits4_orbit_underlying_equiv x)

{` Card(C_4 · x) is the size of the row of x. `}
def bits4_orbit_card (x : Bits4) (h : IsFinite (OrbitUnderlying c4bits_group bits4_gset x))
  : Id Nat (cardinality (OrbitUnderlying c4bits_group bits4_gset x) h) (bits4_row_size (bits4_orbit_index x))
  ≔ cardinality_from_path (OrbitUnderlying c4bits_group bits4_gset x) h (bits4_row_size (bits4_orbit_index x))
      (ua (OrbitUnderlying c4bits_group bits4_gset x) (Fin (bits4_row_size (bits4_orbit_index x)))
        (bits4_orbit_underlying_equiv x))

{` Litmus: 0101 and 1010 form one orbit (of size 2); 0001 and 0111 do not. `}
def bits4_litmus_0101_1010
  : Id (Orbits c4bits_group bits4_gset)
      (orbit_of_point c4bits_group bits4_gset (bits4_mk bits4_o bits4_l bits4_o bits4_l))
      (orbit_of_point c4bits_group bits4_gset (bits4_mk bits4_l bits4_o bits4_l bits4_o))
  ≔ equiv_inverse_map
      (Id (Orbits c4bits_group bits4_gset)
        (orbit_of_point c4bits_group bits4_gset (bits4_mk bits4_o bits4_l bits4_o bits4_l))
        (orbit_of_point c4bits_group bits4_gset (bits4_mk bits4_l bits4_o bits4_l bits4_o)))
      (Id (Fin c4bits_six) bits4_r4 bits4_r4)
      (bits4_same_orbit_equiv (bits4_mk bits4_o bits4_l bits4_o bits4_l) (bits4_mk bits4_l bits4_o bits4_l bits4_o))
      (refl bits4_r4)

def bits4_litmus_0001_not_0111
  (p : Id (Orbits c4bits_group bits4_gset)
      (orbit_of_point c4bits_group bits4_gset (bits4_mk bits4_o bits4_o bits4_o bits4_l))
      (orbit_of_point c4bits_group bits4_gset (bits4_mk bits4_o bits4_l bits4_l bits4_l))) : Empty
  ≔ bool_encode false. true.
      (bits4_row_eqb_complete bits4_r2 bits4_r3
        (bits4_same_orbit_equiv (bits4_mk bits4_o bits4_o bits4_o bits4_l) (bits4_mk bits4_o bits4_l bits4_l bits4_l) .map p))

def bits4_litmus_row_size_0101
  : Id Nat (bits4_row_size (bits4_orbit_index (bits4_mk bits4_o bits4_l bits4_o bits4_l))) two
  ≔ refl two
