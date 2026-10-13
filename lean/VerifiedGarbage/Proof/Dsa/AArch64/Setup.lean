module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.R2
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Montgomery setup for DSA, including leading-zero modulus limbs -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- `x12 := w`, `x9 := 1`, `x13 := 0` before `setWord`. -/
theorem smallHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [ldh .x12 sW, movi .x9 1, movi .x13 0]) s fun u =>
      (u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x9 = BitVec.ofNat 64 1 ∧
        u.gpr .x13 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) ∧ Keep [.x9, .x12, .x13] s u := by
  refine WP.keep [.x9, .x12, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  brun [hg.x0, hdr_enc (show sW < 32 by decide), hg.hdr.hw,
    hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)]

/-- Initialize an array to 1, without relying on its previous contents. -/
theorem one_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {a : Nat} (ha : a < 8) :
    WP isa (Arithmetic.small a 1) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w a) w = 1 ∧
      Arrays B w [a] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.small
  refine WP.seq (WP.mono (smallHead_ok hg hZ) fun u ⟨⟨hu12, hu9, hu13, hum⟩, hku⟩ => ?_)
  have hud : u.gpr .x0 = B := (hku.gpr _ (by decide)).trans hg.x0
  have huh : Hdr u.mem B w minv := by rw [hum]; exact hg.hdr
  refine WP.mono (setWord_ok (hg.scr.congr hku.wr) hud huh hZ hu12 hw' ha (show 0 < w by omega) hu13)
    fun t ⟨hval, hf, hk⟩ => ?_
  have hfa : Arrays B w [a] u.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self a) hf (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨⟨hg.scr.congr ((hku.trans hk).wr), (hk.gpr _ (by decide)).trans hud,
      hfa.hdr huh⟩, ?_, ?_, (hku.trans hk).mono (by decide)⟩
  · rw [hval, hu9]; rfl
  · rw [hum] at hfa
    exact hfa

/-- Computing the public doubling count preserves memory and the header. -/
theorem r2Count_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : w < 2 ^ 31) :
    WP isa (.block Arithmetic.r2Count) s fun t =>
      Good t B Z w minv ∧ t.gpr .x13 = BitVec.ofNat 64 (128 * w) ∧
      t.mem = s.mem ∧ Keep [.x13] s t := by
  refine WP.mono (WP.keep [.x13] (Q := fun t =>
    t.gpr .x13 = BitVec.ofNat 64 (128 * w) ∧ t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨hc, hm⟩, hk⟩ => ⟨⟨hg.scr.congr hk.wr,
      (hk.gpr _ (by decide)).trans hg.x0, by rw [hm]; exact hg.hdr⟩, hc, hm, hk⟩
  unfold Arithmetic.r2Count
  brun [hg.x0, hdr_enc (show sW < 32 by decide), hg.hdr.hw,
    hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega),
    shl_ofNat (show w * 2 ^ 7 < 2 ^ 64 by omega)]
  rw [Nat.mul_comm]; rfl

/-- R² initialization, with no condition on the top limb of the modulus. -/
theorem doublingR2_ok {s : State} {B : Addr} {Z w m : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw48 : w ≤ 48)
    (hn : wv s.mem B (slot w aN) w = m) (hm : 1 < m) :
    WP isa Arithmetic.doublingR2 s fun t =>
      Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % m ∧
      Frm B (r2Ranges w) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  unfold Arithmetic.doublingR2 seqs
  refine WP.seq (WP.mono (one_ok hg hZ hw hw' (by decide)) fun v ⟨hv, hv1, hfv, hkv⟩ => ?_)
  have vn : wv v.mem B (slot w aN) w = m :=
    (hfv.wv_of_not_mem (by decide) (by decide) hnZ).trans hn
  refine WP.seq (WP.mono (r2Count_ok hv hZ hw') fun v' ⟨hv', hvc, hvm, hkc⟩ => ?_)
  have v'n : wv v'.mem B (slot w aN) w = m := by rw [hvm]; exact vn
  have v'r2 : wv v'.mem B (slot w aR2) w = 1 := by rw [hvm]; exact hv1
  refine WP.mono (doubles_ok hv'.scr hv'.x0 hv'.hdr hZ hw hw'
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (show 1 ≤ 128 * w by omega) (show 128 * w < 2 ^ 31 by omega)
    hvc (by rw [v'r2, v'n]; exact hm)) fun t ⟨htv, hft, hht, hkt⟩ => ?_
  have ft : Frm B (r2Ranges w) v'.mem t.mem := hft
  refine ⟨⟨hg.scr.congr (((hkv.trans hkc).trans hkt).wr),
      (hkt.gpr _ (by decide)).trans hv'.x0, hht⟩, ?_, ?_,
      ((hkv.trans hkc).trans hkt).mono (by decide)⟩
  · simpa only [v'r2, v'n, Nat.mul_one] using htv
  · have f1 : Frm B (r2Ranges w) s.mem v.mem :=
      Frm.of_arrays hfv (by intro j hj; simp only [List.mem_singleton] at hj; subst j; simp [r2Ranges])
    rw [hvm] at ft
    exact f1.trans ft

end VG.Proof.Dsa.AArch64
