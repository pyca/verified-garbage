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

theorem codeAt_ok {s : State} {base : Addr} {size w k src modulus c x : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (two : 2 ≤ k) (narrow : k ≤ 2 * w) (srcFit : src + 8 * w ≤ size) (modFit : modulus + 8 * w ≤ size)
    (apart : src + 8 * w ≤ modulus ∨ modulus + 8 * w ≤ src)
    (candidate : val32 s.mem base modulus (2 * w) = c) (witness : val32 s.mem base src (2 * w) = x)
    (odd : c % 2 = 1) (shape : Spec.RsaKeyGen.bitLength (c - 1) = 32 * k) (bound : x < 2 ^ (32 * k)) :
    WP isa (codeAt k w src modulus) s fun t =>
      val32 t.mem base src (2 * w) = (Spec.RsaKeyGen.witness (c - 1) x).1 ∧
      t.gpr .eax = cmask (Spec.RsaKeyGen.witness (c - 1) x).2 ∧
      Outside base src (8 * w) s.mem t.mem ∧ Keeps clob s t := by
  have sample := VG.Proof.RsaKeyGen.witness_sampleAt shape bound
  -- The words above the `k` low ones are zero.
  have split (m : Mem) : val32 m base src (2 * w) = val32 m base src k + 2 ^ (32 * k) * val32 m base (src + 4 * k) (2 * w - k) := by
    rw [← VG.Proof.Mont.val32_append, Nat.add_sub_cancel' narrow]
  have parts {lo hi v : Nat} (h : v = lo + 2 ^ (32 * k) * hi) (hv : v < 2 ^ (32 * k)) : lo = v ∧ hi = 0 := by
    rcases Nat.eq_zero_or_pos hi with e | e
    · subst e; rw [Nat.mul_zero, Nat.add_zero] at h; exact ⟨h.symm, rfl⟩
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * k)) e; omega
  have lowX : val32 s.mem base src k = x ∧ val32 s.mem base (src + 4 * k) (2 * w - k) = 0 :=
    parts (by rw [← witness]; exact split s.mem) bound
  unfold codeAt
  refine WP.seq (WP.mono (WitnessUniform.code_ok scratch positive srcFit modFit apart
    (by rw [candidate]; exact odd)) fun a ⟨uniform, Va, Oa, Ka⟩ => ?_)
  rw [candidate, witness] at uniform
  have lowA : val32 a.mem base src k = x ∧ val32 a.mem base (src + 4 * k) (2 * w - k) = 0 :=
    parts (by rw [← (Va.trans witness)]; exact split a.mem) bound
  refine WP.mono (WitnessFallback.codeAt_ok (uniform := decide (2 ≤ x ∧ x < c - 1))
    (scratch.of_keeps Ka (by unfold WitnessUniform.clob; decide)) two (by omega) uniform)
    fun t ⟨V, Ot, Kt⟩ => ?_
  have high : val32 t.mem base (src + 4 * k) (2 * w - k) = 0 := by
    rw [← lowA.2]
    apply val32_congr
    intro j hj
    exact Ot.w32 (by omega) (by have := scratch.nowrap; omega)
  refine ⟨?_, ?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), ?_⟩
  · rw [split t.mem, high, Nat.mul_zero, Nat.add_zero, V, lowA.1, sample]
  · rw [Kt.1 .eax (by decide), uniform, sample]
  · exact (Ka.mono (by unfold clob WitnessUniform.clob; decide)).widen Kt

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
