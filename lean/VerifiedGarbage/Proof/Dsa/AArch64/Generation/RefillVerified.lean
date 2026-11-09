module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Verified
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashVariants
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCorrect
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCT
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_dsa_parameter_search` on AArch64, verified

`refill_correct` and `refill_ct` for the hash backends and Miller–Rabin
variants, and a state that meets the contract's precondition; and the pairs
of a SHA-1 and a SHA-256 implementation that the search is emitted for
(`hashPairs`). -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.MillerRabin.AArch64 VG.Proof.Dsa.AArch64.Generation

/-- `state`'s words `[0, 128, 32769 · 128, 0]` at `0x4000`. -/
def satMem : Mem :=
  Mem.writeW (Mem.writeW (fun _ => 0) (0x4008 : Addr) (128 : BitVec 64)) (0x4010 : Addr)
    (BitVec.ofNat 64 (Spec.Dsa.parameterEntropy 128))

/-- A search for width 128 with an empty tape. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 276 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x10000 | .x6 => 9216
    | .x7 => 0x4000 | _ => 0
  sp := 0x1000000000000
  mem := satMem
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x2000, 8⟩, ⟨0x10000, 73728⟩, ⟨0x4000, 32⟩]

theorem refill_satisfiable : ∃ s, (Spec.Dsa.parameterSearchContract abi 768).pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel

theorem backend_verified (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (Impl.Dsa.AArch64.Generation.code v1.H v256.H (Generator.generatorStage v).run
      (ProbablePrime.primeTest v).run)
      (Spec.Dsa.parameterSearchContract abi 768) :=
  ⟨refill_correct (generationHashes v1 v256 h1 h256) (Generator.generatorStage v) (ProbablePrime.primeTest v),
    refill_ct (generationHashes v1 v256 h1 h256) (Generator.generatorStage v) (ProbablePrime.primeTest v),
    refill_satisfiable⟩

/-- A SHA-1 and a SHA-256 implementation, as the parameter search takes
them, and that they are SHA-1 and SHA-256. -/
structure Hashes where
  sha1 : MdHash
  sha256 : MdHash
  h1 : sha1.mgf.G.rust = "sha1"
  h256 : sha256.mgf.G.rust = "sha256"

open VG.Proof.Variants.MdHash.AArch64 (sha1Variants sha256Variants)

theorem sha1Variants_rust : ∀ v ∈ sha1Variants, v.mgf.G.rust = "sha1" := by
  intro v hv
  simp only [sha1Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl

theorem sha256Variants_rust : ∀ v ∈ sha256Variants, v.mgf.G.rust = "sha256" := by
  intro v hv
  simp only [sha256Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl

/-- The pairs the parameter search is emitted for, best first: a SHA-1 and
a SHA-256 implementation for the same CPUs (both baselines or both SHA-2
extensions). Either other pair needs the features of one of these, which
runs both hashes with them. -/
def hashPairs : List Hashes :=
  sha1Variants.attach.flatMap fun ⟨v1, h1⟩ => sha256Variants.attach.filterMap fun ⟨v256, h256⟩ =>
    if v1.suffix == v256.suffix then some ⟨v1, v256, sha1Variants_rust v1 h1, sha256Variants_rust v256 h256⟩
    else none

end VG.Proof.Dsa.AArch64.Generation.Refill
