module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Verified
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashVariants
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCorrect
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCT
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_dsa_parameter_search` on AArch64, verified

`refill_correct` and `refill_ct` for the hash backends and Miller–Rabin
variants, and a state that meets the contract's precondition. -/

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

end VG.Proof.Dsa.AArch64.Generation.Refill
