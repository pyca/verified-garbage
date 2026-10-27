module

public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Sig

/-! # The probable-prime test's arguments, from its contract's precondition -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64

/-- The stack the test uses: its frame and the round's calls. -/
abbrev stack : Nat := 184

/-- The test's contract on x86-64. -/
abbrev contract (bits : Nat) : Contract isa :=
  Spec.Dsa.ProbablePrime.contract (Impl.Dsa.X86_64.ProbablePrime.layout bits) abi stack

structure PrimeABI (bits : Nat) (s : State) : Prop where
  stackLower : stack ≤ (s.gpr .rsp).toNat
  rd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩, ⟨s.gpr .r8, 8⟩]
  wsRand : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  wsUsed : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8⟩
  randUsed : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, 8⟩
  retWs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  retUsed : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8⟩
  stackWs : (below (s.gpr .rsp) stack : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
  stackRand : (below (s.gpr .rsp) stack : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  stackUsed : (below (s.gpr .rsp) stack : Region).Disjoint ⟨s.gpr .r8, 8⟩
  wsBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64
  randBound : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .r8).toNat + 8 ≤ 2 ^ 64
  size : Impl.Dsa.Generation.Layout.domainCheck ≤ 8 * (s.gpr .rsi).toNat
  odd : Spec.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits) s.mem (s.gpr .rdi) % 2 = 1
  bits : Spec.Dsa.bitLength
    (Spec.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits) s.mem (s.gpr .rdi)) = bits

theorem primeABI_of {bits : Nat} {s : State} (h : (contract bits).pre s) : PrimeABI bits s := by
  sig_pre [contract, Spec.Dsa.ProbablePrime.contract, Spec.Dsa.ProbablePrime.sig, abi, argRegs] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86_64.ProbablePrime
