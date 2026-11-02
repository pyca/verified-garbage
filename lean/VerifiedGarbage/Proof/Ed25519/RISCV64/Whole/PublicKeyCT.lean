module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb

/-!
# `vg_ed25519_public_key` on RISC-V, with its frame as an argument: constant time

Only the pointers are public: they stay in `s1`–`s4`, which no function
called writes, so the taint analysis (`taint_decide`) sees them public
throughout, callees included. So is the address of the comb's table
(`taintSym`), which `vg_ed25519_scalar_base` reads.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole

theorem publicKey_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ (∀ r ∈ [Reg.a0, .a1, .a2, .a3], s₁.gpr r = s₂.gpr r) ∧
        s₁.syms Impl.Ed25519.RISCV64.combSym = s₂.syms Impl.Ed25519.RISCV64.combSym) :
    ConstantTime isa Pre Pub publicKey :=
  VG.Taint.constantTime (A := taintSym [Impl.Ed25519.RISCV64.combSym]) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr, hsy⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨⟨hsp, fun r h => hr r (by simpa using h)⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

end VG.Proof.Ed25519.RISCV64.Whole
