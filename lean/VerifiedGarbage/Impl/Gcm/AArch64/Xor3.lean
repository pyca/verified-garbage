module

public import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section
namespace VG.Impl.Gcm.AArch64.Stitch
open VG.AArch64

/-- Expand a three-input XOR for FEAT_AES/PMULL cores with no FEAT_SHA3.
The register comparisons take place when generating the instruction list. -/
def xor3Base (d a b c : VReg) : List Instr :=
  if c != d then [.vop (.logic .eor d a b), .vop (.logic .eor d d c)]
  else if b != d then [.vop (.logic .eor d c a), .vop (.logic .eor d d b)]
  else [.vop (.logic .orr d a a)]

def lowerXor3 : Instr → List Instr
  | .vop (.eor3 d a b c) => xor3Base d a b c
  | i => [i]

end VG.Impl.Gcm.AArch64.Stitch
