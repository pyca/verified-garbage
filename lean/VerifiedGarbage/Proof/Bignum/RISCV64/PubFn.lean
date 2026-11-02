module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# The RSA public-key operation on RISC-V: the contract on the registers

`fnContract`: `vg_rsa_public_precomputed_checked` on the registers and the
stack, its working space and length the arguments in memory.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64

/-- The arguments on the stack: `scratch` and `scratch_len`. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- `vg_rsa_public_precomputed_checked`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let pre : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat * 8⟩
    let e : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
    let inp : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.rd = [pre, e, inp, stackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint pre ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint (stackArgs s) ∧
      pre.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .a1).toNat ∧ (s.gpr .a3).toNat = Spec.Rsa.precomputedWords (s.gpr .a1).toNat ∧
      (s.gpr .a7).toNat = (s.gpr .a1).toNat ∧ 1 ≤ (s.gpr .a5).toNat ∧
      (s.gpr .a5).toNat ≤ (s.gpr .a1).toNat ∧ Spec.Rsa.publicScratchWords (s.gpr .a1).toNat ≤ (stackArg s 1).toNat ∧
      (s.gpr .a2).toNat % 8 = 0 ∧ (stackArg s 0).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s s' :=
    ∀ nB : List Byte, nB.length = (s.gpr .a1).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .a0) (s.gpr .a1).toNat ((s'.gpr .a0).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a1).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      (Spec.Rsa.wordsAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a4) (s₁.gpr .a5).toNat).map (·.toNat) =
        (Spec.Rsa.wordsAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a4) (s₂.gpr .a5).toNat).map (·.toNat)

end VG.Proof.Bignum.RISCV64.Pub
