module
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! # Scalar range checks on caller or scratch byte buffers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem loadRange_ok {s : State} {B p : Addr} {Z o w wx m sp sl : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hsp : sp < 32) (hsl : sl < 32) {bytes : List Byte}
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    (aboveOne : Bool) :
    WP isa (.seq (Arithmetic.load aX sp sl) (Checks.rangeMask aboveOne)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      t.gpr .rax = mask (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < m)) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (load_mod_ok hc hm hw2 hwx hw30 (by decide) (by decide) hsp hsl
    hp hl hs h1 (by omega) hfit) fun u ⟨hcu, hmu, hv, _, hf, hk⟩ => ?_)
  refine WP.mono (rangeMask_ok hcu.good (Nat.le_refl _) hw2 (by omega) aboveOne)
    fun t ⟨ht, hmem, hkt⟩ => ?_
  have hft : Frm (off B o) (workRanges wx) u.mem t.mem := by rw [hmem]; exact Frm.refl _ _ _
  have hct := hcu.of_frmT hft (workRanges_ok wx) hkt.2.2 (hkt.gpr (by decide))
  have hn : wv t.mem (off B o) (slot wx aN) wx = m := by rw [hmem]; exact hmu.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmem]; exact hmu.inverse
  rw [hv, hmu.modulus] at ht
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
