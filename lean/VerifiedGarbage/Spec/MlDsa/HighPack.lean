import VerifiedGarbage.Spec.MlDsa.Poly

namespace VG.Spec.MlDsa

/-- Fixed-parameter fused HighBits and SimpleBitPack helper, with the same
output encoding as the separate standard operations. -/
def highPackSig (gamma2 : Nat) : Sig where
  params := [("r", .array false .u32 256),
    ("out", .array true .u8 (32*bitlen ((q-1)/(2*gamma2)-1)))]

/-- Fused helper contract. Input coefficients are canonical; output
bytes are the original HighBits followed by SimpleBitPack, with no leakage
of coefficient values. The parameter is fixed when the helper is generated. -/
def highPackContract (gamma2 : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (highPackSig gamma2).contract A
    (pre := fun r _out m => Reduced m r)
    (post := fun r out m m' _ =>
      Spec.Sha3.bytesAt m' out (32*bitlen ((q-1)/(2*gamma2)-1)) =
        simpleBitPack ((polyAt m r).map fun c => (highBits gamma2 c).toNat) ((q-1)/(2*gamma2)-1))
    (writeArgs := true)
    (stack := stack)

/-- Fixed-parameter helper used by the signing implementation. -/
def highPackApi (gamma2 : Nat) : Api where
  module := "mldsa"
  name := if gamma2 = 261888 then "vg_mldsa_high_pack4" else "vg_mldsa_high_pack6"
  sig := highPackSig gamma2
  writeArgs := true
  contracts := some fun A stack => highPackContract gamma2 A stack
  summary := "Writes the packed HighBits of the 256 canonical coefficients of `r`." ++
    " Its timing depends only on the pointers, as specified by `highPackContract`."
  safety := ["Each coefficient of `r` must be less than 8380417."]

end VG.Spec.MlDsa
