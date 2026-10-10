import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Framework.Scratch

/-!
# Streaming SM3 with its working space as an argument

`vg_sm3_update` and `vg_sm3_finalize` keep their working space in a frame of
their own (`Verified.stackScratch`), around code proved with the working
space as a last argument: `updateScratchContract n` and
`finalizeScratchContract n` are the shared contracts with a `scratch` buffer
of `n` words appended, whatever it holds (each target lays out its own).
-/

namespace VG.Proof.Sm3

open VG.Spec.Sm3

/-- `vg_sm3_update` with `scratch: *mut [u64; n]`. -/
def updateScratchSig (n : Nat) : Sig where
  params := updateSig.params ++ [("scratch", .array true .u64 n)]

/-- `updatePost`, whatever `scratch` is. -/
def updateScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (updateScratchSig n).contract A
    (post := fun state count data len _scratch => updatePost A.ptrBits state count data len)
    (writeArgs := true) (stack := stack)

theorem updateScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    updateScratchContract A n stack = Sig.scratchContract A updateSig "scratch" .u64 n
      (Curry.const (fun _ => True) _) (updatePost A.ptrBits) true stack := rfl

/-- `vg_sm3_finalize` with `scratch: *mut [u64; n]`. -/
def finalizeScratchSig (n : Nat) : Sig where
  params := finalizeSig.params ++ [("scratch", .array true .u64 n)]

/-- `finalizePost`, whatever `scratch` is. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (finalizeScratchSig n).contract A
    (post := fun state count out _scratch => finalizePost A.ptrBits state count out)
    (writeArgs := true) (stack := stack)

theorem finalizeScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    finalizeScratchContract A n stack = Sig.scratchContract A finalizeSig "scratch" .u64 n
      (Curry.const (fun _ => True) _) (finalizePost A.ptrBits) true stack := rfl

end VG.Proof.Sm3
