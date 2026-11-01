module

import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBaseCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBase
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Ed25519.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointOps
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-!
# `vg_ed25519_scalar_base` on RISC-V, verified

The function meets its contract of `Spec/Ed25519/Contract.lean`, with no
stack: the proof against the contract's facts by register (`baseRV`), which
it implies, from a `scratch` aligned to 8 bytes as an `[u64]` is
(`RISCV64.abi`'s `alignsBufs`), and a state satisfying it. Only the pointers
are public (`scalarBase_ct`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64

/-- A state satisfying the precondition. -/
def baseSat : State where
  gpr r := match r with | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem scalarBase_verified :
    Verified RISCV64.target Impl.Ed25519.RISCV64.scalarBase (Proof.Ed25519.scalarBaseContract RISCV64.abi) :=
  Verified.of_correct base_ok' (scalarBase_ct fun _ _ _ _ ⟨h0, h1, h2, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Proof.Ed25519.scalarBaseContract, Proof.Ed25519.scalarBaseSig, baseRV,
      Spec.Ed25519.scratchWords, RISCV64.abi, RISCV64.argRegs] [baseSat] using baseSat)

end VG.Proof.Ed25519.RISCV64
