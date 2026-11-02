module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvImplies
public import VerifiedGarbage.Spec.Rsa.RecoverDet
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_recover_primes_det` on PPC64LE: the contract the proofs are written against

`rdP`: `Spec.Rsa.recoverPrimesDetContract` on the registers and the stack, as
`rvP` states `vg_rsa_recover_primes`' (`RvContract.lean`), which has the same
signature: its precondition but `e_len ≤ 8`, so it implies `rvP`'s
(`rdP_pre`), and the factors by Appendix C.2; only `n` and `e` are public.
`rd_implies`: the shared contract implies it.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE

/-- `vg_rsa_recover_primes_det` on the registers and the stack. -/
def rdP : Contract isa where
  pre s :=
    let p : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let q : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let n : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let e : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let d : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    s.sp.toNat + 32 + 8 * 12 ≤ 2 ^ 64 ∧
      s.rd = [n, e, d, args] ∧ s.wr = [p, q, scr] ∧
      p.Disjoint q ∧ p.Disjoint n ∧ p.Disjoint e ∧ p.Disjoint d ∧ p.Disjoint scr ∧ p.Disjoint args ∧
      q.Disjoint n ∧ q.Disjoint e ∧ q.Disjoint d ∧ q.Disjoint scr ∧ q.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r8).toNat ∧ (s.gpr .r4).toNat = (s.gpr .r8).toNat ∧
      (s.gpr .r6).toNat = (s.gpr .r8).toNat ∧ 1 ≤ (s.gpr .r10).toNat ∧ (s.gpr .r10).toNat ≤ 8 ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat ≤ (s.gpr .r8).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .r3, (s.gpr .r8).toNat), (s.gpr .r5, (s.gpr .r8).toNat)]
      ((s'.gpr .r3).setWidth 32) ((Spec.Rsa.primesKeyDet (nB s) (eB s) (dB s)).map fun v => [v.1, v.2])
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
      (nB s₁ ++ eB s₁).map (·.toNat) = (nB s₂ ++ eB s₂).map (·.toNat)

theorem rdP_pre {s : State} (h : rdP.pre s) : rvP.pre s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, ⟨l1, l2⟩, a26, a27, a28, a29, a30, a31, a32⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, ⟨l1, l2⟩, a26, a27, a28, by omega, a30, a31, a32⟩

theorem rd_implies : rdP.Implies (Spec.Rsa.recoverPrimesDetContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdP, stackArgs_four,
      List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdP, stackArgs_four,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdP, stackArgs_four,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdP,
      stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdP, stackArgs_four,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_four, stackArgs_four, a0, a1, a2, a3], hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdP,
      stackArgs_four, List.append_eq] [rvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rvSatState

end VG.Proof.Rsa.PPC64LE.Recover
