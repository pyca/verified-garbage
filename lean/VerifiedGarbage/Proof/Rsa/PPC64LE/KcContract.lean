module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `vg_rsa_check_key` and `vg_rsa_check_crt_key` on PPC64LE: the contracts the proofs are written against

The shared contracts (`Spec.Rsa.checkKeyContract`,
`Spec.Rsa.checkCrtKeyContract`) stated on the registers and the stack.
`vg_rsa_check_key`: `(n, n_len, e, e_len, d, d_len, p, p_len)` in
`r3`–`r10` and `q`, `q_len`, `dp`, `dp_len`, `dq`, `dq_len`, `qinv`,
`qinv_len`, `scratch` and `scratch_len` the stack arguments 0–9;
`vg_rsa_check_crt_key`: `(n, n_len, e, e_len, p, p_len, q, q_len)` in
`r3`–`r10` and `dp`, `dp_len`, `dq`, `dq_len`, `qinv`, `qinv_len`,
`scratch` and `scratch_len` the stack arguments 0–7.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE

/-- `vg_rsa_check_key` on the registers and the stack. -/
def ckP : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let e : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let d : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let p : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dp : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dq : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let qi : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    s.sp.toNat + 32 + 8 * 18 ≤ 2 ^ 64 ∧
      s.rd = [n, e, d, p, q, dp, dq, qi, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧ (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r4).toNat ∧ 1 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat ≤ (s.gpr .r4).toNat ∧
      1 ≤ (s.gpr .r8).toNat ∧ (s.gpr .r8).toNat ≤ (s.gpr .r4).toNat ∧
      1 ≤ (s.gpr .r10).toNat ∧ (s.gpr .r10).toNat < (s.gpr .r4).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .r4).toNat ∧
      (stackArg s 3).toNat = (s.gpr .r10).toNat ∧ (stackArg s 7).toNat = (s.gpr .r10).toNat ∧
      (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r4).toNat ≤ (stackArg s 9).toNat
  post s s' :=
    (s'.gpr .r3).setWidth 32 = if Spec.Rsa.checkKey (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .r10).toNat) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 10).map (stackArg s₁) = (List.range 10).map (stackArg s₂) ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat ++
          Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat ++
          Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat).map (·.toNat)

/-- `vg_rsa_check_crt_key` on the registers and the stack. -/
def cckP : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let e : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let p : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let q : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let dp : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dq : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let qi : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let scr : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 64⟩
    s.sp.toNat + 32 + 8 * 16 ≤ 2 ^ 64 ∧
      s.rd = [n, e, p, q, dp, dq, qi, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r4).toNat ∧ 1 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat ≤ (s.gpr .r4).toNat ∧
      1 ≤ (s.gpr .r8).toNat ∧ (s.gpr .r8).toNat < (s.gpr .r4).toNat ∧
      1 ≤ (s.gpr .r10).toNat ∧ (s.gpr .r10).toNat < (s.gpr .r4).toNat ∧
      (stackArg s 1).toNat = (s.gpr .r8).toNat ∧ (stackArg s 5).toNat = (s.gpr .r8).toNat ∧
      (stackArg s 3).toNat = (s.gpr .r10).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r4).toNat ≤ (stackArg s 7).toNat
  post s s' :=
    (s'.gpr .r3).setWidth 32 = if Spec.Rsa.checkCrtKey (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r10).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (s.gpr .r8).toNat) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 8).map (stackArg s₁) = (List.range 8).map (stackArg s₂) ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat ++
          Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat ++
          Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat).map (·.toNat)

end VG.Proof.Rsa.PPC64LE.KeyCheck
