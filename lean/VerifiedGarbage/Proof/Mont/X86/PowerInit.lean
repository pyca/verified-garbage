module

public import VerifiedGarbage.Impl.Mont.X86.Power
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Initializing powers for runtime-modulus arithmetic -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The initialization writes exactly one, including when the buffer previously
contained nonzero high words. -/
theorem one_ok {s : State} {base : Addr} {size n out : Nat} (hs : Scr s base size)
    (hn : 0 < n) (ho : out + 8 * n ≤ size) :
    WP isa (VG.Impl.Mont.X86.Dynamic.one n out) s fun t =>
      Outside base out (8 * n) s.mem t.mem ∧ wordsVal t.mem base out n = 1 ∧ Keeps [.eax, .ebp, .edx] s t := by
  unfold VG.Impl.Mont.X86.Dynamic.one
  have hz : out + 4 * (2 * n) ≤ size := by omega
  refine WP.seq (WP.mono (zerosW_ok hs (by omega) hz) fun s₁ ⟨O, V, K⟩ => ?_)
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  have ks : Keeps [.eax, .ebp, .edx] s s₂ := K.widen u₂.keeps
  have hs₂ := hs.of_keeps ks (by decide)
  have hw := writeW32_outside s₂.mem base (d := out) (s₂.gpr .eax) (by have := hs.nowrap; omega)
  refine wp_storeS (hs₂.ea (d := out) (by omega)) (hs₂.write (d := out) (n := 4) (by omega))
    fun t mt => WP.block_nil ⟨?_, ?_, ks.trans (mt.keeps _)⟩
  · rw [mt.mem, u₂.mem]
    exact (O.mono (Nat.le_refl _) (by omega)).trans
      ((writeW32_outside s₁.mem base (d := out) (s₂.gpr .eax) (by have := hs.nowrap; omega)).mono
        (Nat.le_refl _) (by omega))
  · obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega⟩
    rw [hk, val32] at V
    have tail : val32 s₁.mem base (out + 4) k = 0 := by omega
    rw [wordsVal_eq_val32, hk, val32, mt.mem, w32_write_self]
    have keep := hw.val32 (d := out + 4) (k := k) (by omega) (by have := hs.nowrap; omega)
    rw [keep, u₂.mem, tail, u₂.gpr]
    rfl

/-- The public countdown does not wrap. -/
theorem counter_sub {k : Nat} (hk : k < 2 ^ 32) (hpos : 0 < k) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

theorem counter_zero {k : Nat} (hk : k < 2 ^ 32) (hpos : 0 < k) :
    (BitVec.ofNat 32 (k - 1) - 0 == 0) = decide (k = 1) := by
  have z : ∀ x : BitVec 32, x - 0 = x := BitVec.sub_zero
  rw [z]
  have e : BitVec.ofNat 32 (k - 1) = 0 ↔ k = 1 := by
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at h'
      omega
    · rintro rfl; rfl
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using e

end VG.Proof.Mont.X86.Dynamic
