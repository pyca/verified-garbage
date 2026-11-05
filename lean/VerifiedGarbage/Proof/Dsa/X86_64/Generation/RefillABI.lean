module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega

/-! # The refillable-tape search's precondition, as facts about the machine

`vg_dsa_parameter_search(out, out_len, used, rand, rand_len, scratch,
scratch_len, state)` for one width: six arguments in registers and two on
the stack. Its stack is 568 octets: the saved registers' 48, the
controller's 32, the attempts' 296 and the 192 below them that the attempts'
calls use. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack the search uses below its return address. -/
abbrev stackUse : Nat := 568

def inOut (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .rdx, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat * 8⟩
def inState (s : State) : Region := ⟨stackArg s 1, 32⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The modulus's width, `state[1]`. -/
abbrev refillPLen (s : State) : Nat := (s.mem.readW (stackArg s 1 + 8) 64).toNat

structure RefillABI (pBytes : Nat) (s : State) : Prop where
  stackLower : stackUse ≤ (s.gpr .rsp).toNat
  stackUpper : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [inRand s, inArgs s]
  wr : s.wr = [inOut s, inUsed s, inScr s, inState s]
  outUsed : (inOut s).Disjoint (inUsed s)
  outRand : (inOut s).Disjoint (inRand s)
  outScr : (inOut s).Disjoint (inScr s)
  outState : (inOut s).Disjoint (inState s)
  outArgs : (inOut s).Disjoint (inArgs s)
  usedRand : (inUsed s).Disjoint (inRand s)
  usedScr : (inUsed s).Disjoint (inScr s)
  usedState : (inUsed s).Disjoint (inState s)
  usedArgs : (inUsed s).Disjoint (inArgs s)
  randScr : (inRand s).Disjoint (inScr s)
  randState : (inRand s).Disjoint (inState s)
  scrState : (inScr s).Disjoint (inState s)
  scrArgs : (inScr s).Disjoint (inArgs s)
  stateArgs : (inState s).Disjoint (inArgs s)
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inOut s)
  retUsed : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inUsed s)
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inRand s)
  retScr : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inScr s)
  retState : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inState s)
  retArgs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inArgs s)
  stackOut : (below (s.gpr .rsp) stackUse).Disjoint (inOut s)
  stackUsed : (below (s.gpr .rsp) stackUse).Disjoint (inUsed s)
  stackRand : (below (s.gpr .rsp) stackUse).Disjoint (inRand s)
  stackScr : (below (s.gpr .rsp) stackUse).Disjoint (inScr s)
  stackState : (below (s.gpr .rsp) stackUse).Disjoint (inState s)
  stackArgs : (below (s.gpr .rsp) stackUse).Disjoint (inArgs s)
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64
  randBound : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  scrBound : (s.gpr .r9).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64
  stateBound : (stackArg s 1).toNat + 32 ≤ 2 ^ 64
  width : refillPLen s = pBytes
  valid : Spec.Dsa.generationPLenValid (refillPLen s)
  outLength : (s.gpr .rsi).toNat = 2 * refillPLen s + Spec.Dsa.generationQLen (refillPLen s)
  scratchLength : Spec.Dsa.generationScratchWords (refillPLen s) ≤ (stackArg s 0).toNat
  seeds : (s.mem.readW (stackArg s 1) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (refillPLen s))
  randLength : (s.gpr .r8).toNat ≤ Spec.Dsa.parameterEntropy (refillPLen s)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem refillABI_of {pBytes : Nat} {s : State} (h : (contract pBytes abi stackUse).pre s) :
    RefillABI pBytes s := by
  sig_pre [contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two, stackBelow, List.range, List.range.loop,
    inOut, inUsed, inRand, inScr, inState, inArgs] at h
  sig_pre [contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two, stackBelow, List.range, List.range.loop,
    inOut, inUsed, inRand, inScr, inState, inArgs] at h
  sig_split h
  constructor
  all_goals simp only [inOut, inUsed, inRand, inScr, inState, inArgs]
  all_goals first | with_reducible assumption | skip
  all_goals trace_state
  all_goals sorry

end VG.Proof.Dsa.X86_64.Generation.Refill
