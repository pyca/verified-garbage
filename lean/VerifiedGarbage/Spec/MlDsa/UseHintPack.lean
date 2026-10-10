module

public import VerifiedGarbage.Spec.MlDsa.Poly

@[expose] public section

namespace VG.Spec.MlDsa

/-- The fixed-gamma API retains the measured four-register ABI. -/
def useHintPackSig (g : Nat) : Sig where
  params := [("out", .array true .u8 (32*bitlen ((q-1)/(2*g)-1))),
    ("hints", .array false .u32 256), ("w", .array false .u32 256), ("gamma2", .int .u32 true)]

/-- Exact composition of FIPS 204 UseHint and SimpleBitPack. Every nonzero
hint word is interpreted as true, just as in the separate UseHint helper. -/
def useHintPackContract (g : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (useHintPackSig g).contract A
    (pre := fun _out _h w gamma m => gamma.toNat=g ∧ g∈gamma2s ∧ Reduced m w)
    (post := fun out h w _gamma m m' _ =>
      Spec.Sha3.bytesAt m' out (32*bitlen ((q-1)/(2*g)-1)) =
        simpleBitPack (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
          ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m w)) ((q-1)/(2*g)-1))
    (writeArgs := true) (stack := stack)

def useHintPackApi (g : Nat) : Api where
  module := "mldsa"
  name := if g=261888 then "vg_mldsa_usehint_pack4" else "vg_mldsa_usehint_pack6"
  sig := useHintPackSig g
  writeArgs := true
  contracts := some fun A stack=>useHintPackContract g A stack
  summary := "Applies UseHint to the canonical polynomial and writes its packed high bits."
  safety := ["Each coefficient of `w` must be less than 8380417.",
    s!"`gamma2` must equal {g}."]

end VG.Spec.MlDsa
