module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessSample
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessUniform
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFallback
import VerifiedGarbage.Proof.RsaKeyGen.WitnessSample
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Native witness sampling computes the exact reviewed value and uniform flag -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessSample
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessSample

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {s : State} {base : Addr} {size w src modulus c x : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (srcFit : src + 8 * w ≤ size) (modFit : modulus + 8 * w ≤ size)
    (apart : src + 8 * w ≤ modulus ∨ modulus + 8 * w ≤ src)
    (candidate : val32 s.mem base modulus (2 * w) = c) (witness : val32 s.mem base src (2 * w) = x)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w) :
    WP isa (code w src modulus) s fun t =>
      val32 t.mem base src (2 * w) = (Spec.RsaKeyGen.witness (c - 1) x).1 ∧
      t.gpr .eax = cmask (Spec.RsaKeyGen.witness (c - 1) x).2 ∧
      Outside base src (8 * w) s.mem t.mem ∧ Keeps clob s t := by
  have bound : x < 2 ^ (64 * w) := by
    have H := val32_lt s.mem base src (2 * w)
    rw [witness, show 32 * (2 * w) = 64 * w by omega] at H
    exact H
  have sample := VG.Proof.RsaKeyGen.witness_sample shape bound
  refine WP.seq (WP.mono (WitnessUniform.code_ok scratch positive srcFit modFit apart
    (by rw [candidate]; exact odd)) fun a ⟨uniform, Va, Oa, Ka⟩ => ?_)
  rw [candidate, witness] at uniform
  rw [witness] at Va
  refine WP.mono (WitnessFallback.code_ok (uniform := decide (2 ≤ x ∧ x < c - 1))
    (scratch.of_keeps Ka (by unfold WitnessUniform.clob; decide)) positive srcFit uniform)
    fun t ⟨V, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, (Oa.mono (by omega) (by omega)).trans Ot, ?_⟩
  · rw [Va] at V
    rw [sample]
    exact V
  · rw [Kt.1 .eax (by decide), uniform, sample]
  · exact (Ka.mono (by unfold clob WitnessUniform.clob; decide)).widen Kt

end VG.Proof.RsaKeyGen.X86.WitnessSample
