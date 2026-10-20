module
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Contract
public import VerifiedGarbage.Spec.Ffdh.Generation
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.TCB.X86_64.Target


/-! # The complete parameter-search controller: layout and observable result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Ffdh.X86_64.ParameterCandidate

def inputRand (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
def inputArgs (s : State) : Region := ⟨stackArgAddr s 0, 32⟩
def inputControl (s : State) : Region := ⟨stackArg s 3, 128⟩
def inputBuffers (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]

def candidateState (s : State) : State :=
  s.withRegions [inputRand s, ⟨stackArgAddr s 0, 24⟩] (inputBuffers s)

def searchPre (s : State) : Prop :=
  pcPre (candidateState s) ∧ (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
    s.rd = [inputRand s, inputArgs s] ∧
    s.wr = inputBuffers s ++ [inputControl s] ∧
    (stackArg s 3).toNat + 128 ≤ 2 ^ 64 ∧
    (∀ r ∈ inputBuffers s ++ [inputRand s, inputArgs s, ⟨s.gpr .rsp, 8⟩,
      below (s.gpr .rsp) 160], (inputControl s).Disjoint r) ∧
    (∀ r ∈ inputBuffers s, r.Disjoint (inputArgs s)) ∧
    160 ≤ (s.gpr .rsp).toNat ∧
    (∀ r ∈ inputBuffers s ++ [inputRand s, inputControl s],
      (below (s.gpr .rsp) 160).Disjoint r) ∧
    (s.mem.readW (stackArg s 3) 64).toNat ≤ Spec.Ffdh.parameterAttempts (s.gpr .rcx).toNat ∧
    s.mem.readW (stackArg s 3 + 8) 64 = s.gpr .rsi ∧
    s.mem.readW (stackArg s 3 + 16) 64 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat) ∧
    (stackArg s 0).toNat ≤ Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat

def searchResult (s : State) : Spec.Ffdh.ParameterSearchResult :=
  Spec.Ffdh.parameterSearch (s.gpr .rcx).toNat ((s.gpr .r8).setWidth 32).toNat
    (s.mem.readW (stackArg s 3) 64).toNat (pcRand s)

def searchPost (s t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = (searchResult s).status ∧
    Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      (match searchResult s with
        | .accepted p _ => Spec.Rsa.i2osp p (s.gpr .rsi).toNat
        | _ => List.replicate (s.gpr .rsi).toNat 0) ∧
    Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = [BitVec.ofNat 64 (searchResult s).used] ∧
    Spec.Rsa.wordsAt t.mem (stackArg s 3) 4 =
      [BitVec.ofNat 64 (searchResult s).remaining, s.gpr .rsi,
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat),
        BitVec.ofNat 64 (searchResult s).requested]

def searchPub (s t : State) : Prop :=
  pcPub s t ∧ stackArg s 3 = stackArg t 3 ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 3) 4 = Spec.Rsa.wordsAt t.mem (stackArg t 3) 4

def searchContract : Contract isa where
  pre := searchPre
  post := searchPost
  pub := searchPub

end VG.Proof.Ffdh.X86_64.Generation
