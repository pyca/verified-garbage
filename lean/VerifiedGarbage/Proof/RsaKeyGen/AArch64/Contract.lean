import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# A candidate for an RSA prime on AArch64: the contract the proofs use

Untrusted: everything here is checked by Lean. `candContract` states
`Spec.RsaKeyGen.candidateContract` on the registers and the stack:
`vg_rsa_keygen_candidate(out = x0, out_len = x1, used = x2, e = x3,
e_len = x4, p = x5, p_len = x6, rand = x7, rand_len = [sp],
scratch = [sp + 8], scratch_len = [sp + 16])`. The shared contract implies
it (`Implies.lean`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.RsaKeyGen (candidateOp candidateStatus candidateLeak primeLenValid)

/-- The arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The precondition. -/
def candPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let used : Region := ⟨s.gpr .x2, 8⟩
  let e : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let p : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let rand : Region := ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  s.sp.toNat + 24 ≤ 2 ^ 64 ∧
    s.rd = [e, p, rand, args s] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint e ∧ out.Disjoint p ∧ out.Disjoint rand ∧ out.Disjoint scr ∧
    out.Disjoint (args s) ∧ used.Disjoint e ∧ used.Disjoint p ∧ used.Disjoint rand ∧ used.Disjoint scr ∧
    used.Disjoint (args s) ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ rand.Disjoint scr ∧ scr.Disjoint (args s) ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    primeLenValid (s.gpr .x1).toNat ∧ 1 ≤ (s.gpr .x4).toNat ∧ (s.gpr .x4).toNat ≤ 8 ∧
    ((s.gpr .x6).toNat = 0 ∨ (s.gpr .x6).toNat = (s.gpr .x1).toNat) ∧
    Spec.Rsa.scratchWords (s.gpr .x1).toNat ≤ (stackArg s 2).toNat

/-- The specification's result, from the state on entry. -/
def candRes (s : State) : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand) :=
  candidateOp (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) (bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)

/-- The postcondition. -/
def candPost (s s' : State) : Prop :=
  ((s'.gpr .x0).setWidth 32).toNat = candidateStatus (candRes s) ∧
    bytesAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat =
      (match candRes s with
        | some (.prime c, _) => Spec.Rsa.i2osp c (s.gpr .x1).toNat
        | _ => List.replicate (s.gpr .x1).toNat 0) ∧
    wordsAt s'.mem (s.gpr .x2) 1 =
      [BitVec.ofNat 64 (match candRes s with
        | some (_, rest) => (stackArg s 0).toNat - rest.length
        | none => 0)]

/-- What timing may depend on, beyond the arguments: `e` and
`candidateLeak`. -/
def candLeak (s : State) : List Nat :=
  (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).map (·.toNat) ++
    candidateLeak (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
      (bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat) (bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat)

/-- The arguments agree, and so does the leak. -/
def candPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧ (∀ i < 3, stackArg s₁ i = stackArg s₂ i) ∧
    candLeak s₁ = candLeak s₂

/-- `vg_rsa_keygen_candidate`. -/
def candContract : Contract isa where
  pre := candPre
  post := candPost
  pub := candPub

end VG.Proof.RsaKeyGen.AArch64
