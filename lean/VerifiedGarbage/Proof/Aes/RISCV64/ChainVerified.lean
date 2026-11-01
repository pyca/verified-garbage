module

public import VerifiedGarbage.Proof.Aes.RISCV64.Chain
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Aes.RISCV64.Chain
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Aes.RISCV64.Chain

/-!
# AES chaining on RISC-V: correctness and constant time

Correctness (`Chain.lean`) and constant time (by taint tracking,
`taint_decide`: only the pointers, `rounds`, `n` and what is computed from
them reach addresses and branches), against `Proof.Aes.chainRISCV64`, as for
`vg_aes_ctr32` (`Ctr32Verified.lean`). `chain` has no `Api`: the functions
that call it are proven with these, through their calls of it.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.Proof.Aes

theorem chain_correct (out : Bool) (s : State) (hs : (Proof.Aes.chainRISCV64 out).pre s) :
    ∃ t s', Exec isa (Impl.Aes.RISCV64.chain out) s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.chainRISCV64 out).post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct_chain hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

theorem chain_agree (out : Bool) :
    ∀ s₁ s₂, (Proof.Aes.chainRISCV64 out).pre s₁ → (Proof.Aes.chainRISCV64 out).pre s₂ →
      (Proof.Aes.chainRISCV64 out).pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) s₁ s₂ := by
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

theorem chain_ct (out : Bool) : ConstantTime isa (Proof.Aes.chainRISCV64 out).pre
    (Proof.Aes.chainRISCV64 out).pub (Impl.Aes.RISCV64.chain out) := by
  cases out
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (chain_agree _) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (chain_agree _) (by taint_decide)

end VG.Proof.Aes.RISCV64
