module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The same native mask loop covers partial bytes and full 32-bit limbs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem maskStep_ok (s : State) {n i : Nat} (bound : n ≤ 32) (more : i < n)
    (mask : s.gpr .r7 = BitVec.ofNat 32 (2 ^ i - 1))
    (count : s.gpr .r6 = BitVec.ofNat 32 (n - i)) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep) s fun t =>
      (t.gpr .r7 = BitVec.ofNat 32 (2 ^ (i + 1) - 1) ∧
        t.gpr .r6 = BitVec.ofNat 32 (n - (i + 1)) ∧
        t.z = decide (i + 1 = n) ∧ t.mem = s.mem) ∧ Rest [.r6, .r7] s t := by
  have inc : BitVec.ofNat 32 (2 ^ i - 1) + BitVec.ofNat 32 (2 ^ i - 1) + 1 =
      BitVec.ofNat 32 (2 ^ (i + 1) - 1) := by
    change BitVec.ofNat 32 (2 ^ i - 1) + BitVec.ofNat 32 (2 ^ i - 1) + BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
    congr 1
    have positive := Nat.two_pow_pos i
    rw [Nat.pow_succ]
    omega
  have dec : BitVec.ofNat 32 (n - i) - 1 = BitVec.ofNat 32 (n - (i + 1)) := by
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  have zero : (BitVec.ofNat 32 (n - (i + 1)) == (0 : BitVec 32)) = decide (i + 1 = n) := by
    rw [ofNat_beq_zero (k := n - (i + 1)) (by omega)]
    simp only [show n - (i + 1) = 0 ↔ i + 1 = n by omega]
  refine withRest [.r6, .r7] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep
  ffrun [mask, count, inc, dec, zero]

/-- Construct a low-bit mask without a shift by the register width. -/
theorem maskLoop_ok (s : State) {n : Nat} (positive : 0 < n) (bound : n ≤ 32)
    (mask : s.gpr .r7 = 0) (count : s.gpr .r6 = BitVec.ofNat 32 n) :
    WP isa (.loop (.block VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep) .ne) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (2 ^ n - 1) ∧
      t.gpr .r6 = 0 ∧ t.mem = s.mem ∧ Rest [.r6, .r7] s t := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧
    t.gpr .r7 = BitVec.ofNat 32 (2 ^ i - 1) ∧
    t.gpr .r6 = BitVec.ofNat 32 (n - i) ∧ t.mem = s.mem ∧ Rest [.r6, .r7] s t
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hm, hc, mem, rest⟩ := h
    refine WP.mono (maskStep_ok t bound (by omega) hm hc) ?_
    rintro u ⟨⟨um, uc, uz, umem⟩, ur⟩
    by_cases last : i + 1 = n
    · left
      refine ⟨?_, ?_⟩
      · change some (!u.z) = some false
        simp only [uz, last, decide_true, Bool.not_true]
      · exact ⟨last ▸ um, by simpa [last] using uc,
          umem.trans mem, rest.trans ur⟩
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega,
        um, uc, umem.trans mem, rest.trans ur⟩
      change some (!u.z) = some true
      simp only [uz, last, decide_false, Bool.not_false]
  · exact ⟨0, by omega, positive, by simpa using mask,
      by simpa using count, rfl, Rest.refl _ _⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
