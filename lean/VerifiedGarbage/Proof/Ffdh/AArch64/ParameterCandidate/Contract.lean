module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# An FFDH parameter candidate on AArch64: the contract the proofs use

`pcContract` states `Proof.Ffdh.sievedParameterCandidateContract` (with no stack of
its own) on the registers and the stack:
`vg_ffdh_parameter_candidate_sieved(out = x0, out_len = x1, used = x2, bits = x3,
generator = w4, rand = x5, rand_len = x6, scratch = x7, scratch_len = [sp])`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)

def pcPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let used : Region := ⟨s.gpr .x2, 8⟩
  let rnd : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let scr : Region := ⟨s.gpr .x7, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  s.sp.toNat + 8 ≤ 2 ^ 64 ∧ s.rd = [rnd, args] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint rnd ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    used.Disjoint rnd ∧ used.Disjoint scr ∧ used.Disjoint args ∧ rnd.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    512 ≤ (s.gpr .x3).toNat ∧ (s.gpr .x3).toNat ≤ 8192 ∧ (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 ∧
    (((s.gpr .x4).setWidth 32).toNat = 2 ∨ ((s.gpr .x4).setWidth 32).toNat = 5) ∧
    Spec.Rsa.scratchWords (s.gpr .x1).toNat ≤ (stackArg s 0).toNat

/-- The random octets on entry. -/
abbrev pcRand (s : State) : List Byte := bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat

/-- The specification's result, from the state on entry. -/
def pcResult (s : State) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  sievedParameterCandidate (s.gpr .x3).toNat ((s.gpr .x4).setWidth 32).toNat (pcRand s)

def pcPost (s t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = candidateStatus (pcResult s) ∧
    bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
      (match pcResult s with
        | some (some p, _) => i2osp p (s.gpr .x1).toNat
        | _ => List.replicate (s.gpr .x1).toNat 0) ∧
    wordsAt t.mem (s.gpr .x2) 1 =
      [BitVec.ofNat 64 (match pcResult s with
        | some (_, rest) => (s.gpr .x6).toNat - rest.length
        | none => 0)]

/-- The arguments agree, and so do the random octets. -/
def pcPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (pcRand s).map (·.toNat) = (pcRand t).map (·.toNat) ∧
    s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    (s.gpr .x4).setWidth 32 = (t.gpr .x4).setWidth 32 ∧ s.gpr .x5 = t.gpr .x5 ∧ s.gpr .x6 = t.gpr .x6 ∧
    s.gpr .x7 = t.gpr .x7 ∧ stackArg s 0 = stackArg t 0

def pcContract : Contract isa where
  pre := pcPre
  post := pcPost
  pub := pcPub

end VG.Proof.Ffdh.AArch64.ParameterCandidate
