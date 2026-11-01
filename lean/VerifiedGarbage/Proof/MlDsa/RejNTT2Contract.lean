module

public import VerifiedGarbage.Proof.MlDsa.Contract

/-!
# ML-DSA: the contract of two `RejNTTPoly`s at once

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Exactly two independent 34-byte seeds and two 256-coefficient outputs. -/
def rejNTT2Sig : Sig where
  params := [("seeds",.array false .u8 68),("a",.array true .u32 512),
    ("scratch",.array true .u64 1024)]
  ret := some .u32

/-- Two instances of the same bounded Algorithm 30 contract as `rejNTT4Contract`.
The declared input leakage is exactly the two seeds; writable scratch and
output contents are not public inputs. -/
def rejNTT2Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  rejNTT2Sig.contract A
    (post := fun seeds a _scratch m m' r =>
      (r=1 → ∀k<2,Reduced m' (poly4 a k)) ∧
        ((r=1 ∧ ∀k<2,∃b : Bounds,rejNTTPoly b.rejNTT (seed4 m seeds k)=
          some (polyAt m' (poly4 a k))) ∨
         (r=0 ∧ ∃k<2,rejNTTPoly minBounds.rejNTT (seed4 m seeds k)=none)))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seeds _a _scratch m => leakBytes (Spec.Sha3.bytesAt m seeds 68))

end VG.Proof.MlDsa
