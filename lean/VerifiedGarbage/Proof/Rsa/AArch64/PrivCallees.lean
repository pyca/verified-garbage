import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# The checked RSA private-key operation on AArch64: its callees' contracts

`vg_rsa_private_checked` calls `vg_rsa_private_crt`,
`vg_rsa_public_precompute` and `vg_rsa_public_precomputed_checked`, each
verified against its shared contract (with no stack: none of them has a
frame). Its proof works with those contracts spelt out on the registers and
the stack (`crtA`, `pcA`, `pdA`), and moves to them from the shared ones
(`crt_pre`, `crt_post`, `crt_pub`, …).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64

/-- Two leaks of two byte strings, the first of the same length in both. -/
theorem leak_eq {a b c d : List Byte} (hl : a.length = c.length)
    (h : (a ++ b).map (·.toNat) = (c ++ d).map (·.toNat)) : a = c ∧ b = d := by
  have hi : (a ++ b) = (c ++ d) := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  exact List.append_inj hi hl

/-! ## `vg_rsa_private_crt` -/

/-- `vg_rsa_private_crt(out = x0, out_len = x1, n = x2, n_len = x3,
input = x4, input_len = x5, p = x6, p_len = x7, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, scratch, scratch_len)`, the last ten on the
stack. -/
def crtA : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let inp : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let p : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dp : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dq : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let qi : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    s.sp.toNat + 80 ≤ 2 ^ 64 ∧
      s.rd = [n, inp, p, q, dp, dq, qi, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x3).toNat ∧
      (s.gpr .x5).toNat = (s.gpr .x3).toNat ∧ 1 ≤ (s.gpr .x7).toNat ∧
      (s.gpr .x7).toNat < (s.gpr .x3).toNat ∧ 1 ≤ (stackArg s 1).toNat ∧
      (stackArg s 1).toNat < (s.gpr .x3).toNat ∧ (stackArg s 3).toNat = (s.gpr .x7).toNat ∧
      (stackArg s 7).toNat = (s.gpr .x7).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (stackArg s 9).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 10).map (stackArg s₁) = (List.range 10).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

theorem crt_pre {s : State} (h : crtA.pre s) : (Spec.Rsa.privateCrtContract abi 0).pre s := by
  sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, stackArgs_ten,
    List.append_eq]
  sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, stackArgs_ten,
    List.append_eq]
  simp only [crtA] at h
  sig_split h
  sig_and_intros
  all_goals with_reducible assumption

theorem crt_post {s s' : State} (h : (Spec.Rsa.privateCrtContract abi 0).post s s') : crtA.post s s' := by
  sig_post [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, stackArgs_ten,
    List.append_eq] at h
  exact h

theorem crt_pub {s₁ s₂ : State} (h : crtA.pub s₁ s₂) : (Spec.Rsa.privateCrtContract abi 0).pub s₁ s₂ := by
  sig_pub [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, stackArgs_ten,
    List.append_eq]
  obtain ⟨hr, hsp, ha, hn⟩ := h
  simp only [stackArgs_ten, List.cons.injEq, and_true] at ha
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ha
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [hn]
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsp, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1,
    a2, a3, a4, a5, a6, a7, a8, a9, and_self]

/-! ## `vg_rsa_public_precompute` -/

/-- `vg_rsa_public_precompute(pre = x0, pre_len = x1, n = x2, n_len = x3,
scratch = x4, scratch_len = x5)`. -/
def pcA : Contract isa where
  pre s :=
    let pre : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scr : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩
    s.rd = [n] ∧ s.wr = [pre, scr] ∧
      pre.Disjoint n ∧ pre.Disjoint scr ∧ n.Disjoint scr ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧
      (s.gpr .x1).toNat = Spec.Rsa.precomputedWords (s.gpr .x3).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (s.gpr .x5).toNat
  post s s' :=
    match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) with
    | some ws => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat = ws
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat = List.replicate (s.gpr .x1).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5], s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat

theorem pc_pre {s : State} (h : pcA.pre s) : (Spec.Rsa.publicPrecomputeContract abi 0).pre s := by
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs]
  simp only [pcA] at h
  sig_split h
  sig_and_intros
  all_goals with_reducible assumption

theorem pc_post {s s' : State} (h : (Spec.Rsa.publicPrecomputeContract abi 0).post s s') : pcA.post s s' := by
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs] at h
  exact h

theorem pc_pub {s₁ s₂ : State} (h : pcA.pub s₁ s₂) : (Spec.Rsa.publicPrecomputeContract abi 0).pub s₁ s₂ := by
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs]
  obtain ⟨hr, hsp, hn⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hr
  rw [hn]
  simp only [hsp, r0, r1, r2, r3, r4, r5, and_self]

/-! ## `vg_rsa_public_precomputed_checked` -/

/-- `vg_rsa_public_precomputed_checked(out = x0, out_len = x1, pre = x2,
pre_len = x3, e = x4, e_len = x5, input = x6, input_len = x7, scratch,
scratch_len)`, the last two on the stack. -/
def pdA : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let pre : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩
    let e : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let inp : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    s.sp.toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [pre, e, inp, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint pre ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      pre.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x1).toNat ∧
      (s.gpr .x3).toNat = Spec.Rsa.precomputedWords (s.gpr .x1).toNat ∧
      (s.gpr .x7).toNat = (s.gpr .x1).toNat ∧ 1 ≤ (s.gpr .x5).toNat ∧ (s.gpr .x5).toNat ≤ (s.gpr .x1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x1).toNat ≤ (stackArg s 1).toNat
  post s s' :=
    ∀ nB : List Byte, nB.length = (s.gpr .x1).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x1).toNat ((s'.gpr .x0).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      Spec.Rsa.wordsAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.wordsAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem pd_pre {s : State} (h : pdA.pre s) : (Spec.Rsa.publicPrecomputedCheckedContract abi 0).pre s := by
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  simp only [pdA] at h
  sig_split h
  sig_and_intros
  all_goals with_reducible assumption

theorem pd_post {s s' : State} (h : (Spec.Rsa.publicPrecomputedCheckedContract abi 0).post s s') :
    pdA.post s s' := by
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq] at h
  exact h

theorem pd_pub {s₁ s₂ : State} (h : pdA.pub s₁ s₂) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 0).pub s₁ s₂ := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  obtain ⟨hr, hsp, a0, a1, hw, he⟩ := h
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [hw, he]
  simp only [List.getD_cons_succ, List.getD_cons_zero, hsp, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1,
    and_self]

end VG.Proof.Rsa.AArch64
