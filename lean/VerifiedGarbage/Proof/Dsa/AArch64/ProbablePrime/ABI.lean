module

public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The probable-prime test's arguments, from its contract's precondition -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64

/-- The stack the test uses: its frame (the round is a leaf). -/
abbrev stack : Nat := 272

/-- The test's contract on AArch64. -/
abbrev contract (bits : Nat) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract (Impl.Dsa.AArch64.ProbablePrime.layout bits) abi stack

structure PrimeABI (bits : Nat) (s : State) : Prop where
  stackLower : stack ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩, ⟨s.gpr .x4, 8⟩]
  wsRand : (⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  wsUsed : (⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .x4, 8⟩
  randUsed : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, 8⟩
  stackWs : (below s.sp stack : Region).Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩
  stackRand : (below s.sp stack : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  stackUsed : (below s.sp stack : Region).Disjoint ⟨s.gpr .x4, 8⟩
  wsBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat * 8 ≤ 2 ^ 64
  randBound : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .x4).toNat + 8 ≤ 2 ^ 64
  size : Impl.Dsa.Generation.Layout.domainCheck ≤ 8 * (s.gpr .x1).toNat
  odd : Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.AArch64.ProbablePrime.layout bits) s.mem (s.gpr .x0) % 2 = 1
  bits : Spec.Dsa.bitLength
    (Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.AArch64.ProbablePrime.layout bits) s.mem (s.gpr .x0)) = bits

theorem primeABI_of {bits : Nat} {s : State} (h : (contract bits).pre s) : PrimeABI bits s := by
  sig_pre [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.AArch64.ProbablePrime
