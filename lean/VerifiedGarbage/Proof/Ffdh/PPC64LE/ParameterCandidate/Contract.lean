module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.Contract

/-!
# An FFDH parameter candidate on PPC64LE: the callable contract

`vg_ffdh_parameter_candidate(out = r3, out_len = r4, used = r5, bits = r6,
generator = r7, rand = r8, rand_len = r9, scratch = r10, scratch_len)`, the
last on the stack (`pcContract`), with 176 bytes of stack below `sp` for the
round it calls.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)

def pcPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
  let used : Region := ⟨s.gpr .r5, 8⟩
  let rand : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let scr : Region := ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  let below : Region := ⟨s.sp - BitVec.ofNat 64 176, 176⟩
  176 ≤ s.sp.toNat ∧ s.sp.toNat + 32 + 8 * 9 ≤ 2 ^ 64 ∧
    s.rd = [rand, args] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint rand ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    used.Disjoint rand ∧ used.Disjoint scr ∧ used.Disjoint args ∧
    rand.Disjoint scr ∧ scr.Disjoint args ∧
    below.Disjoint out ∧ below.Disjoint used ∧ below.Disjoint rand ∧ below.Disjoint scr ∧ below.Disjoint args ∧
    (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r10).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    512 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat ≤ 8192 ∧
    (s.gpr .r4).toNat = ((s.gpr .r6).toNat + 7) / 8 ∧
    (((s.gpr .r7).setWidth 32).toNat = 2 ∨ ((s.gpr .r7).setWidth 32).toNat = 5) ∧
    Spec.Rsa.scratchWords (s.gpr .r4).toNat ≤ (stackArg s 0).toNat

abbrev pcRand (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat

def pcResult (s : State) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  parameterCandidate (s.gpr .r6).toNat ((s.gpr .r7).setWidth 32).toNat (pcRand s)

def pcPost (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = candidateStatus (pcResult s) ∧
    bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat =
      (match pcResult s with
        | some (some p, _) => i2osp p (s.gpr .r4).toNat
        | _ => List.replicate (s.gpr .r4).toNat 0) ∧
    wordsAt t.mem (s.gpr .r5) 1 =
      [BitVec.ofNat 64 (match pcResult s with
        | some (_, rest) => (s.gpr .r9).toNat - rest.length
        | none => 0)]

def pcPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (pcRand s).map (·.toNat) = (pcRand t).map (·.toNat) ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧
    s.gpr .r6 = t.gpr .r6 ∧ (s.gpr .r7).setWidth 32 = (t.gpr .r7).setWidth 32 ∧ s.gpr .r8 = t.gpr .r8 ∧
    s.gpr .r9 = t.gpr .r9 ∧ s.gpr .r10 = t.gpr .r10 ∧ stackArg s 0 = stackArg t 0

def pcContract : Contract isa where
  pre := pcPre
  post := pcPost
  pub := pcPub

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

/-- A state meeting the precondition: a 64-byte p of 512 bits, no randomness,
the working space at `0xA000`, its length on the stack at `0x9060`. -/
def pcSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 512 | .r7 => 2 | .r8 => 0x3000
    | .r10 => 0xA000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9060 then 0x20 else bif Nat.beq a.toNat 0x9061 then 0x04 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0xA000, 1056 * 8⟩]

theorem pc_implies : pcContract.Implies (parameterCandidateContract abi 176) where
  pre := by
    intro s h
    sig_pre [parameterCandidateContract, parameterCandidateSig, abi, argRegs, stackBelow,
      pcContract, pcPre, stackArgs_one, List.append_eq] at h
    sig_pre [parameterCandidateContract, parameterCandidateSig, abi, argRegs, stackBelow,
      pcContract, pcPre, stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [parameterCandidateContract, parameterCandidateSig, abi, argRegs, stackBelow,
      pcContract, pcPre, stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    sig_implies_post [parameterCandidateContract, parameterCandidateSig, abi, argRegs, pcContract,
      pcPost, pcResult, pcRand, stackArgs_one, List.append_eq]
  pub := by
    intro s t _ _ h
    sig_pub [parameterCandidateContract, parameterCandidateSig, abi, argRegs, stackArgs_one,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sig_implies_sat [parameterCandidateContract, parameterCandidateSig, abi, argRegs, stackBelow,
      pcContract, pcPre, stackArgs_one, List.append_eq]
      [pcSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using pcSat

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
