module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_crt_values` on PPC64LE: the contract the proofs are written against

`cvP`: the shared contract (`Spec.Rsa.crtValuesContract`) stated on the
registers and the stack, as AArch64's (`Proof/Rsa/AArch64/CvCode.lean`):
`(dp = r3, dp_len = r4, dq = r5, dq_len = r6, qinv = r7, qinv_len = r8,
n = r9, n_len = r10)` and `p`, `p_len`, `q`, `q_len`, `d`, `d_len`,
`scratch` and `scratch_len` the stack arguments 0–7. `cv_implies`: it is
implied by the shared contract.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE

/-- `vg_rsa_crt_values` on the registers and the stack. -/
def cvP : Contract isa where
  pre s :=
    let dp : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let dq : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let qi : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let n : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let d : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let scr : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 64⟩
    s.sp.toNat + 32 + 8 * 16 ≤ 2 ^ 64 ∧
      s.rd = [n, p, q, d, args] ∧ s.wr = [dp, dq, qi, scr] ∧
      dp.Disjoint dq ∧ dp.Disjoint qi ∧ dp.Disjoint n ∧ dp.Disjoint p ∧ dp.Disjoint q ∧ dp.Disjoint d ∧
      dp.Disjoint scr ∧ dp.Disjoint args ∧
      dq.Disjoint qi ∧ dq.Disjoint n ∧ dq.Disjoint p ∧ dq.Disjoint q ∧ dq.Disjoint d ∧ dq.Disjoint scr ∧
      dq.Disjoint args ∧
      qi.Disjoint n ∧ qi.Disjoint p ∧ qi.Disjoint q ∧ qi.Disjoint d ∧ qi.Disjoint scr ∧ qi.Disjoint args ∧
      n.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r10).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .r10).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .r10).toNat ∧ (s.gpr .r4).toNat = (stackArg s 1).toNat ∧
      (s.gpr .r8).toNat = (stackArg s 1).toNat ∧ (s.gpr .r6).toNat = (stackArg s 3).toNat ∧
      1 ≤ (stackArg s 5).toNat ∧ (stackArg s 5).toNat ≤ (s.gpr .r10).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r10).toNat ≤ (stackArg s 7).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .r3, (stackArg s 1).toNat), (s.gpr .r5, (stackArg s 3).toNat),
        (s.gpr .r7, (stackArg s 1).toNat)] ((s'.gpr .r3).setWidth 32)
      ((Spec.Rsa.crtKey (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)).map fun v => [v.1, v.2.1, v.2.2])
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 8).map (stackArg s₁) = (List.range 8).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r9) (s₁.gpr .r10).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r9) (s₂.gpr .r10).toNat

end VG.Proof.Rsa.PPC64LE.CrtValues
