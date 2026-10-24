module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_keygen_key` on PPC64LE: the contract the proofs are written against

`keyP`: the shared contract (`Spec.RsaKeyGen.keyContract`) stated on the
registers and the stack, as `vg_rsa_crt_values`'s `cvP`
(`Proof/Rsa/PPC64LE/CvContract.lean`): `(n = r3, n_len = r4, d = r5,
d_len = r6, p = r7, p_len = r8, q = r9, q_len = r10)` and `dp`, `dp_len`,
`dq`, `dq_len`, `qinv`, `qinv_len`, `e`, `e_len`, `scratch` and
`scratch_len` the stack arguments 0–9. Its public data are the arguments
alone: the code reads `e` only as a number, as it does the primes.
`key_implies`: it is implied by the shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE

/-- The key from the primes, from the caller's memory. -/
abbrev resOf (s : State) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  Spec.RsaKeyGen.keyOp (s.gpr .r8).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r8).toNat)

/-- The seven outputs' bytes in `m`. -/
abbrev outBytes (s : State) (m : Mem) : List (List Byte) :=
  [Spec.Rsa.bytesAt m (s.gpr .r3) (s.gpr .r4).toNat, Spec.Rsa.bytesAt m (s.gpr .r5) (s.gpr .r4).toNat,
    Spec.Rsa.bytesAt m (s.gpr .r7) (s.gpr .r8).toNat, Spec.Rsa.bytesAt m (s.gpr .r9) (s.gpr .r8).toNat,
    Spec.Rsa.bytesAt m (stackArg s 0) (s.gpr .r8).toNat, Spec.Rsa.bytesAt m (stackArg s 2) (s.gpr .r8).toNat,
    Spec.Rsa.bytesAt m (stackArg s 4) (s.gpr .r8).toNat]

/-- Zeros at the seven outputs in `m`. -/
abbrev outZero (s : State) (m : Mem) : Prop :=
  Spec.Rsa.bytesAt m (s.gpr .r3) (s.gpr .r4).toNat = List.replicate (s.gpr .r4).toNat 0 ∧
    Spec.Rsa.bytesAt m (s.gpr .r5) (s.gpr .r4).toNat = List.replicate (s.gpr .r4).toNat 0 ∧
    Spec.Rsa.bytesAt m (s.gpr .r7) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0 ∧
    Spec.Rsa.bytesAt m (s.gpr .r9) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0 ∧
    Spec.Rsa.bytesAt m (stackArg s 0) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0 ∧
    Spec.Rsa.bytesAt m (stackArg s 2) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0 ∧
    Spec.Rsa.bytesAt m (stackArg s 4) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0

/-- `vg_rsa_keygen_key` on the registers and the stack. -/
def keyP : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let d : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let p : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let q : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let dp : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dq : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let qi : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let e : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let scr : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    s.sp.toNat + 32 + 8 * 18 ≤ 2 ^ 64 ∧
      s.rd = [e, args] ∧ s.wr = [n, d, p, q, dp, dq, qi, scr] ∧
      n.Disjoint d ∧ n.Disjoint p ∧ n.Disjoint q ∧ n.Disjoint dp ∧ n.Disjoint dq ∧ n.Disjoint qi ∧
      n.Disjoint e ∧ n.Disjoint scr ∧ n.Disjoint args ∧
      d.Disjoint p ∧ d.Disjoint q ∧ d.Disjoint dp ∧ d.Disjoint dq ∧ d.Disjoint qi ∧ d.Disjoint e ∧
      d.Disjoint scr ∧ d.Disjoint args ∧
      p.Disjoint q ∧ p.Disjoint dp ∧ p.Disjoint dq ∧ p.Disjoint qi ∧ p.Disjoint e ∧ p.Disjoint scr ∧
      p.Disjoint args ∧
      q.Disjoint dp ∧ q.Disjoint dq ∧ q.Disjoint qi ∧ q.Disjoint e ∧ q.Disjoint scr ∧ q.Disjoint args ∧
      dp.Disjoint dq ∧ dp.Disjoint qi ∧ dp.Disjoint e ∧ dp.Disjoint scr ∧ dp.Disjoint args ∧
      dq.Disjoint qi ∧ dq.Disjoint e ∧ dq.Disjoint scr ∧ dq.Disjoint args ∧
      qi.Disjoint e ∧ qi.Disjoint scr ∧ qi.Disjoint args ∧
      e.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧ (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.RsaKeyGen.primeLenValid (s.gpr .r8).toNat ∧ (s.gpr .r4).toNat = 2 * (s.gpr .r8).toNat ∧
      (s.gpr .r6).toNat = (s.gpr .r4).toNat ∧ (s.gpr .r10).toNat = (s.gpr .r8).toNat ∧
      (stackArg s 1).toNat = (s.gpr .r8).toNat ∧ (stackArg s 3).toNat = (s.gpr .r8).toNat ∧
      (stackArg s 5).toNat = (s.gpr .r8).toNat ∧ 1 ≤ (stackArg s 7).toNat ∧ (stackArg s 7).toNat ≤ 8 ∧
      Spec.Rsa.scratchWords (s.gpr .r4).toNat ≤ (stackArg s 9).toNat
  post s s' :=
    ((s'.gpr .r3).setWidth 32).toNat = Spec.RsaKeyGen.keyStatus (resOf s) ∧
      match resOf s with
      | .inl (.ok ys) => outBytes s s'.mem = ys
      | _ => outZero s s'.mem
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 10).map (stackArg s₁) = (List.range 10).map (stackArg s₂)

end VG.Proof.RsaKeyGen.PPC64LE.Key
