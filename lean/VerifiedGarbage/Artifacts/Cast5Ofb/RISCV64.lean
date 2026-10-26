module

public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit

/-! # CAST5-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.RISCV64

/-- How the functions compute CAST5, and the mode. -/
def note : String :=
  "Baseline RV64I: one block at a time, through the generic modes of `Impl/Modes/RISCV64/` over \
  CAST5's ECB block function (inlined): each S-box lookup is a scan of the whole table in the static \
  `VG_CAST5_S1234`, so no secret is an address. The subkeys are read where the caller passed them, a \
  byte at a time; the public number of rounds chooses one of two copies of the mode, each with its \
  count fixed. The mode runs in a frame of 128 bytes on the stack, 16-byte aligned, which is zeroed \
  before returning: it keeps its state in `s1`-`s4`, which the block function uses, so they are kept \
  in `a3`, `a4`, `s11` and `ra` meanwhile, and our caller's `s0`, `s5`-`s11` and `ra` in the frame."

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact RISCV64.target {
    notes := [note]
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.RISCV64.ofb
    stack := 128
    verified := Proof.Cast5.RISCV64.Modes.ofb_verified }]

end VG.Artifacts.Cast5Ofb.RISCV64
