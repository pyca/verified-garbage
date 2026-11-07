module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # FFDH parameter generation on x86-64: the callable contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)

def pcPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let used : Region := ⟨s.gpr .rdx, 8⟩
  let rand : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let below : Region := ⟨s.gpr .rsp - 128#64, 128⟩
  (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ 128 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [rand, args] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint rand ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    used.Disjoint rand ∧ used.Disjoint scr ∧ used.Disjoint args ∧
    rand.Disjoint scr ∧ scr.Disjoint args ∧
    ret.Disjoint out ∧ ret.Disjoint used ∧ ret.Disjoint rand ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
    below.Disjoint out ∧ below.Disjoint used ∧ below.Disjoint rand ∧ below.Disjoint scr ∧ below.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    512 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ 8192 ∧
    (s.gpr .rsi).toNat = ((s.gpr .rcx).toNat + 7) / 8 ∧
    (((s.gpr .r8).setWidth 32).toNat = 2 ∨ ((s.gpr .r8).setWidth 32).toNat = 5) ∧
    Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (stackArg s 2).toNat

abbrev pcRand (s : State) : List Byte := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat

def pcResult (s : State) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  sievedParameterCandidate (s.gpr .rcx).toNat ((s.gpr .r8).setWidth 32).toNat (pcRand s)

def pcPost (s t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = candidateStatus (pcResult s) ∧
    bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      (match pcResult s with
        | some (some p, _) => i2osp p (s.gpr .rsi).toNat
        | _ => List.replicate (s.gpr .rsi).toNat 0) ∧
    wordsAt t.mem (s.gpr .rdx) 1 =
      [BitVec.ofNat 64 (match pcResult s with
        | some (_, rest) => (stackArg s 0).toNat - rest.length
        | none => 0)]

def pcPub (s t : State) : Prop :=
  s.gpr .rsp = t.gpr .rsp ∧ (pcRand s).map (·.toNat) = (pcRand t).map (·.toNat) ∧
    s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx ∧ (s.gpr .r8).setWidth 32 = (t.gpr .r8).setWidth 32 ∧ s.gpr .r9 = t.gpr .r9 ∧
    stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧ stackArg s 2 = stackArg t 2

def pcContract : Contract isa where
  pre := pcPre
  post := pcPost
  pub := pcPub

end VG.Proof.Ffdh.X86_64.ParameterCandidate
