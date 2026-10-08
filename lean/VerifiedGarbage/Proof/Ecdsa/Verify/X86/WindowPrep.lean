import VerifiedGarbage.Impl.Ecdsa.Verify.X86
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Mont.X86.Chain

/-! # Scalar recoding for the x86 P-256 variable-base window -/

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86
variable {c : Impl.Ecdsa.X86.Cfg}

/-- Recoding preserves the original scalar and all existing arithmetic slots. -/
theorem windowPrepAt_ok (h4 : c.n = 4) {i : Nat} (hi : i < 45) {s : State} {base : Addr}
    (hs : Scr s base size) :
    WP isa (Impl.Ecdh.X86.Cfg.windowPrep c (c.sl i)) s fun u =>
      (∀ t < 260, u.mem (off base (Impl.Ecdh.X86.Cfg.windowBits + t)) =
        if (sv c base s i + WinCfg.offset 65).testBit t then 1 else 0) ∧
      Keeps [.eax, .ebx, .edx, .esi] s u ∧
      Unch base [(3520, 120), (Impl.Ecdh.X86.Cfg.windowBits, 320)] s.mem u.mem := by
  have hn := hs.nowrap
  have hv : c.sl i + 32 ≤ 3520 := by rw [sl_eq, h4]; omega
  have hvsize : c.sl i + 32 ≤ size := by change _ ≤ 8192; omega
  unfold Impl.Ecdh.X86.Cfg.windowPrep
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copy_ok 8 hs (o := 3520) (by decide) hvsize (Or.inr hv))
    fun s₁ ⟨v₁, k₁, O₁⟩ => ?_))
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₁ (n := 1) (o := 3552) (x := 0)
    (by decide) (by decide)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  have padded : wordsVal s₂.mem base 3520 5 = sv c base s i := by
    rw [wordsVal_succ_top]
    have top : (word s₂.mem base 3552).toNat = 0 := by
      simpa only [wordsVal, Nat.mul_zero, Nat.add_zero] using v₂
    change wordsVal s₂.mem base 3520 4 + 2 ^ 256 * (word s₂.mem base 3552).toNat = _
    rw [top, Nat.mul_zero, Nat.add_zero, wordsVal_eq_val32,
      O₂.val32 (by omega) (by decide), v₁]
    change _ = wordsVal s.mem base (c.sl i) c.n
    rw [wordsVal_eq_val32, h4]
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₂ (n := 5) (o := 3560) (x := WinCfg.offset 65)
    (by decide) (by decide +kernel)) fun s₄ ⟨vb, k₃, O₃⟩ => ?_)
  have va : wordsVal s₄.mem base 3520 5 = sv c base s i :=
    (O₃.wordsVal (by omega) (by decide)).trans padded
  have k₄ := (k₁.trans k₂).trans k₃
  have O₄ : Outside base 3520 120 s.mem s₄.mem :=
    ((O₁.mono (by decide) (by decide)).trans (O₂.mono (by decide) (by decide))).trans
      (O₃.mono (by decide) (by decide))
  have hs₄ := hs.of_keeps k₄ (by decide)
  rw [chain_eq]
  refine WP.mono (chainAdd_ok hs₄ (acc := 3600) (a := 3520) (b := 3560) 9
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨O₅, ⟨carry, _, v₅⟩, k₅⟩ => ?_
  have ha : val32 s₄.mem base 3520 10 = sv c base s i := by
    rw [← wordsVal_eq_val32 (n := 5)]; exact va
  have hb : val32 s₄.mem base 3560 10 = WinCfg.offset 65 := by
    rw [← wordsVal_eq_val32 (n := 5)]; exact vb
  rw [ha, hb] at v₅
  have hvlt : sv c base s i < 2 ^ 256 := by
    have := wordsVal_lt s.mem base (c.sl i) c.n
    change wordsVal s.mem base (c.sl i) c.n < 2 ^ 256
    rw [h4] at *
    exact this
  have hoff : WinCfg.offset 65 < 2 ^ 261 := by decide +kernel
  have value : wordsVal s₅.mem base 3600 5 = sv c base s i + WinCfg.offset 65 := by
    rw [wordsVal_eq_val32]
    have hsum : sv c base s i + WinCfg.offset 65 < 2 ^ (32 * (9 + 1)) :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add hvlt hoff) (by decide +kernel)
    have radix : (2 : Nat) ^ (32 * (9 + 1)) = 2 ^ 256 * 2 ^ 64 := by decide +kernel
    simp only [radix] at v₅ hsum
    cases carry with
    | false => simpa only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] using v₅
    | true =>
      simp only [Bool.toNat_true, Nat.mul_one] at v₅
      rw [← v₅] at hsum
      exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left _ _) hsum)
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  refine WP.mono (bits_ok hs₅ (n := 5) (src := 3600) (dst := Impl.Ecdh.X86.Cfg.windowBits)
    (by decide) (by decide) (by decide) (by decide)) fun u ⟨bits, ku, Ou⟩ => ?_
  refine ⟨fun t ht => ?_, (k₄.trans k₅).mono (by decide) |>.trans ku,
    ((O₄.trans (O₅.mono (by decide) (by decide))).unch).trans (Ou.unch)⟩
  rw [bits t (by omega), value]
theorem windowPrep_ok (h4 : c.n = 4) {s : State} {base : Addr}
    (hs : Scr s base size) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.windowPrep c) s fun u =>
      (∀ t < 260, u.mem (off base (Impl.Ecdh.X86.Cfg.windowBits + t)) =
        if (sv c base s V + WinCfg.offset 65).testBit t then 1 else 0) ∧
      Keeps [.eax, .ebx, .edx, .esi] s u ∧
      Unch base [(3520, 120), (Impl.Ecdh.X86.Cfg.windowBits, 320)] s.mem u.mem :=
  windowPrepAt_ok h4 (by decide) hs

end VG.Proof.Ecdsa.Verify.X86
