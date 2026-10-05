import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# A candidate for an RSA prime on x86-64: the contract the proofs use

Untrusted: everything here is checked by Lean. `candContract` states
`Spec.RsaKeyGen.candidateContract` on the registers and the stack:
`vg_rsa_keygen_candidate(out = rdi, out_len = rsi, used = rdx, e = rcx,
e_len = r8, p = r9, p_len = [rsp + 8], rand = [rsp + 16],
rand_len = [rsp + 24], scratch = [rsp + 32], scratch_len = [rsp + 40])`.
The shared contract implies it (`Verified.lean`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Spec.RsaKeyGen (candidateOp candidateStatus candidateLeak primeLenValid)

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The precondition. -/
def candPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let used : Region := ⟨s.gpr .rdx, 8⟩
  let e : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let p : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let rand : Region := ⟨arg s 1, (arg s 2).toNat⟩
  let scr : Region := ⟨arg s 3, (arg s 4).toNat * 8⟩
  (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
    s.rd = [e, p, rand, args s] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint e ∧ out.Disjoint p ∧ out.Disjoint rand ∧ out.Disjoint scr ∧
    out.Disjoint (args s) ∧ used.Disjoint e ∧ used.Disjoint p ∧ used.Disjoint rand ∧ used.Disjoint scr ∧
    used.Disjoint (args s) ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ rand.Disjoint scr ∧ scr.Disjoint (args s) ∧
    (ret s).Disjoint out ∧ (ret s).Disjoint used ∧ (ret s).Disjoint e ∧ (ret s).Disjoint p ∧
    (ret s).Disjoint rand ∧ (ret s).Disjoint scr ∧ (ret s).Disjoint (args s) ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧
    (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 64 ∧ (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 64 ∧
    primeLenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .r8).toNat ∧ (s.gpr .r8).toNat ≤ 8 ∧
    ((arg s 0).toNat = 0 ∨ (arg s 0).toNat = (s.gpr .rsi).toNat) ∧
    Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (arg s 4).toNat

/-- The specification's result, from the state on entry. -/
def candRes (s : State) : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand) :=
  candidateOp (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
    (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat) (bytesAt s.mem (arg s 1) (arg s 2).toNat)

/-- The postcondition. -/
def candPost (s s' : State) : Prop :=
  ((s'.gpr .rax).setWidth 32).toNat = candidateStatus (candRes s) ∧
    bytesAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      (match candRes s with
        | some (.prime c, _) => Spec.Rsa.i2osp c (s.gpr .rsi).toNat
        | _ => List.replicate (s.gpr .rsi).toNat 0) ∧
    wordsAt s'.mem (s.gpr .rdx) 1 =
      [BitVec.ofNat 64 (match candRes s with
        | some (_, rest) => (arg s 2).toNat - rest.length
        | none => 0)]

/-- What timing may depend on, beyond the arguments: `e` and
`candidateLeak`. -/
def candLeak (s : State) : List Nat :=
  (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).map (·.toNat) ++
    candidateLeak (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (bytesAt s.mem (s.gpr .r9) (arg s 0).toNat) (bytesAt s.mem (arg s 1) (arg s 2).toNat)

/-- The arguments agree, and so does the leak. -/
def candPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (∀ i < 5, arg s₁ i = arg s₂ i) ∧ candLeak s₁ = candLeak s₂

/-- `vg_rsa_keygen_candidate`. -/
def candContract : Contract isa where
  pre := candPre
  post := candPost
  pub := candPub

end VG.Proof.RsaKeyGen.X86_64
