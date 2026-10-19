module

public import VerifiedGarbage.Impl.Bignum.X86.SmallConstant
public import VerifiedGarbage.Proof.Mont.X86.DynamicFrame

/-! # Initializing zero-extended constants for private RSA -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The initialization writes exactly the requested word, including when the buffer previously
contained nonzero high words. -/
theorem smallConstant_ok {s : State} {base : Addr} {size n out value : Nat} (hs : Scr s base size)
    (hn : 0 < n) (hv : value < 2 ^ 32) (ho : out + 8 * n ≤ size) :
    WP isa (VG.Impl.Bignum.X86.smallConstant n out value) s fun t =>
      Outside base out (8 * n) s.mem t.mem ∧ wordsVal t.mem base out n = value ∧ Keeps [.eax, .ebp, .edx] s t := by
  unfold VG.Impl.Bignum.X86.smallConstant
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
    simp only [BitVec.toNat_ofNat, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hv]


end VG.Proof.Bignum.X86
