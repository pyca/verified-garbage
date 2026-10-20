module
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.AArch64.OneScan
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask

/-! # Testing a byte-encoded DSA subgroup result against one -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem loadOne_ok {s : State} {B p : Addr} {Z o w wx m sp sl : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hsp : sp < 32) (hsl : sl < 32) {bytes : List Byte}
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx) :
    WP isa (.seq (Arithmetic.load aX sp sl) (.seq Checks.oneScan (.block (Checks.zeroMask .x15)))) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      t.gpr .x3 = mask (decide (Spec.Dsa.decodeBE bytes = 1)) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (load_mod_ok hc hm hw2 hwx hw30 (by decide) (by decide) hsp hsl
    hp hl hs h1 (by omega) hfit) fun u ⟨hcu, hmu, hv, _, hf, hk⟩ => ?_)
  refine WP.seq (WP.mono (oneScan_ok hcu.good (Nat.le_refl _) hw2 (by omega))
    fun v ⟨hv15, hvm, hkv⟩ => ?_)
  rw [hv] at hv15
  refine WP.mono (zeroMask_ok .x15 false) fun t ⟨ht, htm, hkt⟩ => ?_
  change t.gpr .x3 = mask (decide (v.gpr .x15 = 0)) at ht
  rw [decide_eq_decide.mpr hv15] at ht
  have hmem : t.mem = u.mem := htm.trans hvm
  have hft : Frm (off B o) (workRanges wx) u.mem t.mem := by rw [hmem]; exact Frm.refl _ _ _
  have hku : Keep mmRegs u t := (hkv.trans hkt).mono (by decide)
  have hct := hcu.of_frmT hft (workRanges_ok wx) hku.wr (hku.gpr .x0 (by decide))
  have hn : wv t.mem (off B o) (slot wx aN) wx = m := by rw [hmem]; exact hmu.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmem]; exact hmu.inverse
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, hf.trans hft, (hk.trans hku).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
