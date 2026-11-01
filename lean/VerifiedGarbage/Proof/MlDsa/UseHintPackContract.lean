module

public import VerifiedGarbage.Proof.MlDsa.Contract

/-!
# ML-DSA: the contract of `UseHint`, packed

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

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

end VG.Proof.MlDsa
