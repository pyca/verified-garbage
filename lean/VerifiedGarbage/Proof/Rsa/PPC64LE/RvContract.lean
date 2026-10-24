module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_recover_primes` on PPC64LE: the contract the proofs are written against

`rvP`: the shared contract (`Spec.Rsa.recoverPrimesContract`) stated on the
registers and the stack: `(p = r3, p_len = r4, q = r5, q_len = r6, n = r7,
n_len = r8, e = r9, e_len = r10)` and `d`, `d_len`, `scratch` and
`scratch_len` the stack arguments 0–3.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE

/-- The bytes of `n`, `e` and `d`. -/
abbrev nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat
abbrev eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat
abbrev dB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat

/-- `vg_rsa_recover_primes` on the registers and the stack. -/
def rvP : Contract isa where
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
      (s.gpr .r6).toNat = (s.gpr .r8).toNat ∧ 1 ≤ (s.gpr .r10).toNat ∧ (s.gpr .r10).toNat ≤ (s.gpr .r8).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat ≤ (s.gpr .r8).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .r3, (s.gpr .r8).toNat), (s.gpr .r5, (s.gpr .r8).toNat)]
      ((s'.gpr .r3).setWidth 32) ((Spec.Rsa.primesKey (nB s) (eB s) (dB s)).1.map fun v => [v.1, v.2])
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
      (nB s₁ ++ eB s₁).map (·.toNat) ++ [(Spec.Rsa.primesKey (nB s₁) (eB s₁) (dB s₁)).2] =
        (nB s₂ ++ eB s₂).map (·.toNat) ++ [(Spec.Rsa.primesKey (nB s₂) (eB s₂) (dB s₂)).2]

end VG.Proof.Rsa.PPC64LE.Recover
