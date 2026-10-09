import VerifiedGarbage.Spec.MlDsa.Poly

namespace VG.Spec.MlDsa
open VG

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

/-- Two public-seed matrix streams through the ordinary checked helper ABI. -/
def rejNTT2Api : Api where
  module := "mldsa"
  name := "vg_mldsa_rej_ntt_poly2"
  sig := rejNTT2Sig
  writeArgs := true
  contracts := some fun A stack => rejNTT2Contract A stack
  summary := "RejNTTPoly (FIPS 204 Algorithm 30) for two independent 34-byte seeds. " ++
    "On success, writes two canonical 256-coefficient polynomials and returns 1. " ++
    "Returns 0 if a stream fails within the specified minimum sampling bound; output is then unspecified." ++
    " Timing may depend on the pointers and the two public seeds."
  safety := ["Scratch holds 1024 writable u64 words and must not overlap seeds or output."]

end VG.Spec.MlDsa
