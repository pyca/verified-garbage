module

public import VerifiedGarbage.Proof.Sm4.X86.CtrVerified
import Mathlib.Tactic.SplitIfs

/-! # SM4-CTR artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.X86

/-- How the function computes SM4, and the mode. -/
def note : String :=
  "Baseline IA-32: full 128-bit big-endian counter increments and in-place XOR, with each counter encrypted \
  by the bitsliced SM4 core in general-purpose registers, with no table lookups. The key schedule's table of \
  round keys is built once per call. One block per batch of eight is used."

def artifacts : List Artifact := [
  { Spec.Sm4.ctrApi with
    target := X86.target
    doc := Spec.Sm4.ctrApi.doc (notes := [note])
    code := Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 Impl.Sm4.X86.ctr
    contract := Spec.Sm4.ctrContract X86.abi 1472
    stack := 1472
    verified := Proof.Sm4.X86.Ctr.ctr_framed
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sm4Ctr.X86
