module

public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The probable-prime test's arguments, from its contract's precondition -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64

/-- The stack the test uses: its frame and the round's calls. -/
abbrev stack : Nat := 184

/-- The test's contract on x86-64. -/
abbrev contract : Contract isa :=
  Proof.Dsa.ProbablePrime.sizedContract Impl.Dsa.X86_64.ProbablePrime.layout
    Impl.Dsa.X86_64.ProbablePrime.sizes abi stack

/-- The candidate widths parameter generation tests. -/
def Supported (bits : Nat) : Prop :=
  bits = 160 ∨ bits = 256 ∨ bits = 1024 ∨ bits = 2048 ∨ bits = 3072

theorem Supported.of_mem {bits : Nat} (h : bits ∈ Impl.Dsa.X86_64.ProbablePrime.sizes) :
    Supported bits := by
  simpa only [Supported, Impl.Dsa.X86_64.ProbablePrime.sizes, List.mem_cons, List.not_mem_nil,
    or_false] using h

theorem Supported.mem {bits : Nat} (h : Supported bits) : bits ∈ Impl.Dsa.X86_64.ProbablePrime.sizes := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem Supported.le {bits : Nat} (hb : Supported bits) : 160 ≤ bits ∧ bits ≤ 3072 := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

structure PrimeABI (bits : Nat) (s : State) : Prop where
  width : s.gpr .r9 = BitVec.ofNat 64 bits
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
  odd : Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits) s.mem (s.gpr .rdi) % 2 = 1
  bits : Spec.Dsa.bitLength
    (Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits) s.mem (s.gpr .rdi)) = bits

theorem primeABI_of {s : State} (h : contract.pre s) :
    Supported (s.gpr .r9).toNat ∧ PrimeABI (s.gpr .r9).toNat s := by
  sig_pre [contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi,
    argRegs] at h
  sig_split h
  refine ⟨Supported.of_mem (by with_reducible assumption), ?_⟩
  constructor <;> first | with_reducible assumption | exact (BitVec.ofNat_toNat 64 _ |>.trans (BitVec.setWidth_eq _)).symm

end VG.Proof.Dsa.X86_64.ProbablePrime
