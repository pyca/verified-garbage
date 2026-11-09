module
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4`'s contract

What the proofs of `vg_mlkem_sample_ntt4` share in showing that the contract
they are written against (`sample4K`) implies the shared one of `Spec/`: a
state it permits (`sample4Sat`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def sample4Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 136⟩]
  wr := [⟨0x2000, 4096⟩, ⟨0x4000, 8192⟩]

end VG.Proof.MlKem.X86_64
