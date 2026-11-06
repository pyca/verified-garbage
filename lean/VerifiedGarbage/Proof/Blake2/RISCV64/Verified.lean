module

public import VerifiedGarbage.Proof.Blake2.RISCV64.Contract
public import VerifiedGarbage.Impl.Blake2.RISCV64
public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.Proof.Blake2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Blake2.RISCV64.Round
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Blake2.RISCV64.Compress
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Contract
meta import VerifiedGarbage.Impl.Blake2.RISCV64
meta import VerifiedGarbage.Spec.Blake2.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# BLAKE2 compression function on RISC-V: `Verified`

Correctness (`Compress.lean`), constant time (by taint tracking,
`taint_decide`), and a state satisfying the precondition, against
`Proof.Blake2.compressRISCV64`, then moved to the shared contracts of
`Spec/Blake2/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64

open VG VG.RISCV64

theorem rok_b : ROk (z := .d) Spec.Blake2.b := by unfold ROk; decide
theorem rok_s : ROk (z := .w) Spec.Blake2.s := by unfold ROk; decide

theorem compress_correct {z : Size} (P : Spec.Blake2.Params z.bits) (hR : ROk P) :
    ∀ s, (compressRISCV64 P).pre s → ∃ t s', Exec isa (Impl.Blake2.RISCV64.compress P) s t s' ∧
      abiPreserved s s' ∧ (compressRISCV64 P).post s s' := fun s hs => by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct P hR (pre_of P s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

end VG.Proof.Blake2.RISCV64
