module
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindow
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Dsa.X86_64.JointBuildContext

import VerifiedGarbage.Proof.Dsa.X86_64.JointEncode
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs

/-! # Loading and preparing both bases for joint DSA exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem jointPrepare_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {gp yp : Addr} {gb yb : List Byte}
    (hg : word s.mem B (8 * arg) = gp)
    (hgl : word s.mem B (8 * argLen) = BitVec.ofNat 64 gb.length)
    (hgs : Src s B Z gp gb) (hg1 : 1 ≤ gb.length) (hgw : (gb.length + 7) / 8 ≤ wx)
    (hy : word s.mem B (8 * arg2) = yp)
    (hyl : word s.mem B (8 * arg2Len) = BitVec.ofNat 64 yb.length)
    (hys : Src s B Z yp yb) (hy1 : 1 ≤ yb.length) (hyw : (yb.length + 7) / 8 ≤ wx) :
    WP isa (Joint.prepare M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ JointCtx t (off B o) wx m minv ∧
      JointTab t.mem (off B o) wx m (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE yb) ∧
      wv t.mem (off B o) (slot wx aY) wx = 2 ^ (64 * wx) % m ∧
      wv t.mem (off B o) (slot wx aOne) wx = 1 ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Joint.prepare seqs
  refine WP.seq (WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv)
    fun s1 ⟨hc1, hm1, ho1, hr1, hf1, hk1⟩ => ?_)
  refine WP.seq (WP.mono (load_mod_ok hc1 hm1 hw2 hwx hw30 (by decide) (by decide)
    (by decide) (by decide) ((work_parent hc hf1 (by decide)).trans hg)
    ((work_parent hc hf1 (by decide)).trans hgl) (work_source hc hf1 hk1 hgs)
    hg1 (by omega) hgw) fun s2 ⟨hc2, hm2, hg2, ha2, hf2, hk2⟩ => ?_)
  have hf12 := hf1.trans hf2
  have hk12 := (hk1.trans hk2).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  have ho2 := (ha2 aOne (by decide) (by decide)).trans ho1
  have hr2 := (ha2 aR2 (by decide) (by decide)).trans hr1
  refine WP.seq (WP.mono (load_mod_ok hc2 hm2 hw2 hwx hw30 (by decide) (by decide)
    (by decide) (by decide) ((work_parent hc hf12 (by decide)).trans hy)
    ((work_parent hc hf12 (by decide)).trans hyl) (work_source hc hf12 hk12 hys)
    hy1 (by omega) hyw) fun s3 ⟨hc3, hm3, hy3, ha3, hf3, hk3⟩ => ?_)
  have hg3 := (ha3 aX (by decide) (by decide)).trans hg2
  have ho3 := (ha3 aOne (by decide) (by decide)).trans ho2
  have hr3 := (ha3 aR2 (by decide) (by decide)).trans hr2
  have hr3' : wv s3.mem (off B o) (slot wx aR2) wx =
      (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [hr3, ← Nat.pow_add, show 64 * wx + 64 * wx = 128 * wx by omega]
  have hR := coprime_pow2 hodd (64 * wx)
  refine WP.seq (WP.mono (jointEncode_ok M ⟨hm3, hc3.scrT⟩ hw2 (by omega) hm hR hg3 hy3 ho3 hr3')
    fun s4 ⟨hc4, hv4, hf4, hk4⟩ => ?_)
  have hsub4 := arrays_context hc3 hf4 (by decide) hk4
  refine WP.mono (jointBuild_ok M hc4 hw2 (by omega) (by omega) hR hv4)
    fun t ⟨hct, ht, hyt, hot, hft, hkt⟩ => ?_
  exact ⟨hsub4.of_frmT hft (workRanges_ok wx) hkt.2.2 (hkt.gpr (by decide)),
    hct, ht, hyt, hot, (((hf12.trans hf3).trans (arrays_work hf4 (by decide))).trans hft),
    ((((hk12.trans hk3).trans hk4).trans hkt).mono (by decide))⟩

end VG.Proof.Dsa.X86_64
