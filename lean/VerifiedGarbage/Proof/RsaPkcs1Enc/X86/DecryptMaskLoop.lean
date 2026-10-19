module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMaskStep

/-! # The public mask loop computes exactly the candidate bit mask -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc
open VG.Spec.RsaPkcs1Enc (bitLength)

theorem maskLoop_ok {s : State} {x : Nat} (positive : 1 ≤ x) (bound : x ≤ 1024)
    (ax : s.gpr .eax = 0) (cx : s.gpr .ecx = BitVec.ofNat 32 x) :
    WP isa maskLoop s fun t => t.mem = s.mem ∧ Keeps [.eax, .edx] s t ∧
      t.gpr .eax = BitVec.ofNat 32 (bitMask x) := by
  have nonzero : x ≠ 0 := by omega
  have Bpositive : 0 < bitLength x := by
    simp only [bitLength, nonzero, ite_false]
    omega
  refine WP.loop (M := isa) (fun n t => ∃ j, n = bitLength x - j ∧ j < bitLength x ∧
    t.mem = s.mem ∧ Keeps [.eax, .edx] s t ∧ t.gpr .eax = BitVec.ofNat 32 (2 ^ j - 1) ∧
      t.gpr .ecx = BitVec.ofNat 32 x) ?_ (bitLength x) s
        ⟨0, rfl, Bpositive, rfl, Keeps.refl _ _, ax, cx⟩
  rintro n t ⟨j, rfl, jBound, M, K, axT, cxT⟩
  have step := bitMask_step positive (bitMask_lt nonzero jBound)
  have power : 2 ^ (j + 1) - 1 ≤ bitMask x :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j + 1 ≤ bitLength x)) 1
  have maskBound : 2 * (2 ^ j - 1) + 1 < 2 ^ 31 := by
    rw [step.1]
    have := bitMask_le nonzero
    omega
  refine WP.mono (maskBody_ok axT cxT maskBound (by omega : x < 2 ^ 31)) ?_
  rintro u ⟨Mu, Ku, axU, zf⟩
  rw [step.1] at axU zf
  by_cases done : j + 1 = bitLength x
  · have stop : ¬2 ^ (j + 1) - 1 < x := by
      have := bitMask_ge nonzero
      rw [← done] at this
      omega
    refine Or.inl ⟨?_, Mu.trans M, K.trans Ku, ?_⟩
    · simp only [eval, zf, decide_eq_false stop, Bool.not_false, Option.map_some, Bool.not_true]
    · rw [done] at axU
      exact axU
  · have again := bitMask_lt nonzero (by omega : j + 1 < bitLength x)
    refine Or.inr ⟨?_, bitLength x - (j + 1), by omega, j + 1, rfl, by omega,
      Mu.trans M, K.trans Ku, axU, ?_⟩
    · simp only [eval, zf, decide_eq_true again, Bool.not_true, Option.map_some, Bool.not_false]
    · exact (Ku.1 .ecx (by decide)).trans cxT

end VG.Proof.RsaPkcs1Enc.X86.Dec
