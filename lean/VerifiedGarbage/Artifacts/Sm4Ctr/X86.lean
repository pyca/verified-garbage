module

public import VerifiedGarbage.Proof.Sm4.X86.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.CtrLit

/-! # SM4-CTR artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.X86

/-- How the function computes SM4, and the mode. -/
def note : String :=
  "Baseline IA-32: full 128-bit big-endian counter increments and in-place XOR, with each counter encrypted \
  by the bitsliced SM4 core in general-purpose registers, with no table lookups. The key schedule's table of \
  round keys is built once per call, by `vg_sm4_prepare_keys`, and each batch encrypted by `vg_sm4_crypt_prepared`. One block per batch of eight is used."

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact X86.target {
    notes := [note]
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.ctr
    stack := 1516
    verified := Proof.Sm4.X86.Ctr.ctr_framed }]

end VG.Artifacts.Sm4Ctr.X86
