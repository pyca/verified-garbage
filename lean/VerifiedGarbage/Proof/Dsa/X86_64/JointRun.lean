module

import VerifiedGarbage.Proof.Dsa.X86_64.JointInit
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Proof.Dsa.X86_64.JointBuildContext
public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindow
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.JointByte
import VerifiedGarbage.Proof.Bignum.Math

/-! # Joint exponentiation and conversion out of Montgomery representation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem joint_source_out {s : State} {B p : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {bs : List Byte} (hs : Src s B Z p bs) :
    ∀ i < bs.length, slot wx 8 + tabBytes wx ≤ ofs (off B o) (p + BitVec.ofNat 64 i) := by
  intro i hi
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have := hc.hi
  have := hc.scr.nowrap
  have := hs.out i hi
  rcases ofs_rebase B (p + BitVec.ofNat 64 i) (o := o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega

theorem jointRun_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx n g y : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hmctx : JointCtx s (off B o) wx n minv)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hn : 1 < n) (hodd : n % 2 = 1)
    (htab : JointTab s.mem (off B o) wx n g y)
    (hy : wv s.mem (off B o) (slot wx aY) wx = 2 ^ (64 * wx) % n)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    {eb fb : List Byte} (he : Src s B Z (off B u) eb) (hf : Src s B Z (off B v) fb)
    (hlen : fb.length = eb.length) (hL0 : 0 < eb.length) (hL' : eb.length < 2 ^ 31)
    (hfield : 344 ≤ Z) (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length) :
    WP isa (Joint.run Sq.mm M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv n ∧
      wv t.mem (off B o) (slot wx aY) wx =
        (g ^ Spec.Dsa.decodeBE eb * y ^ Spec.Dsa.decodeBE fb) % n ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Joint.run seqs
  refine WP.seq (WP.mono (jointInit_ok hc hmctx htab hfield hl)
    fun s1 ⟨hc1, hm1, ht1, ha1, he1, hf1, hl1, hi1, hfrm1, hk1⟩ => ?_)
  have hsrc1 := work_source hc hfrm1 hk1 he
  have fsrc1 := work_source hc hfrm1 hk1 hf
  have hy1 := (ha1 aY (by decide)).trans hy
  have ho1 := (ha1 aOne (by decide)).trans hone
  have hR := coprime_pow2 hodd (64 * wx)
  have hI : JointByteInv s1 (off B o) wx minv n
      (wv s1.mem (off B o) (slot wx Crt.aXc) wx) g y (off B u) (off B v)
      eb.length eb fb 0 s1 := by
    refine ⟨hm1.exp, ht1, ?_, ?_, hi1, he1, hf1, hl1, Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hy1]; exact Nat.mod_lt _ (by omega)
    · rw [hy1, Nat.mod_mod, pre_zero, pre_zero, Nat.pow_zero, Nat.pow_zero, Nat.one_mul]
  refine WP.seq (WP.mono (jointBytes_ok M Sq hw hw' hR rfl hlen hL0 hL'
    hsrc1.rd hsrc1.val (joint_source_out hc1 hsrc1)
    (by simpa only [hlen] using fsrc1.rd) (by simpa only [hlen] using fsrc1.val)
    (by simpa only [hlen] using joint_source_out hc1 fsrc1) hI) fun s2 h2 => ?_)
  have hc2 := hc1.of_frmT h2.frm (crtExpRanges_ok wx) h2.keep.2.2 (h2.keep.gpr (by decide))
  have hm2 : ModCtx s2 (off B o) (slot wx 8) wx minv n := ⟨h2.ctx.good, h2.ctx.n, h2.ctx.inv⟩
  have hnow := hc1.good.scr.nowrap
  have honeSep := crtExpRanges_arr wx (j := aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
  have honeSlot := slot_le (w := wx) (show aOne < 8 by decide)
  have ho2 : wv s2.mem (off B o) (slot wx aOne) wx = 1 :=
    (h2.frm.wv_eq (fun r h => by have := honeSep r h; omega) (by omega)).trans ho1
  refine WP.mono (mont_step M hm2 (Nat.le_refl _) hw (by omega) (by unfold MmUse; decide)
    (by rw [ho2]; exact hn)) fun t ⟨hmt, hlt, hv, hft, hkt⟩ => ?_
  have hv2 := h2.val
  rw [← hlen, pre_len] at hv2
  rw [hlen, pre_len] at hv2
  rw [ho2] at hv
  have hresult := VG.Proof.Dsa.mont_decode hR hv2 hv
  rw [Nat.mod_eq_of_lt hlt] at hresult
  refine ⟨arrays_context hc2 hft (by decide) hkt, hmt, ?_,
    (hfrm1.trans (exp_work h2.frm)).trans (arrays_work hft (by decide)),
    ((hk1.trans h2.keep).trans hkt).mono (by decide)⟩
  simpa only [VG.Proof.Dsa.decodeBE_os2ip] using hresult

end VG.Proof.Dsa.X86_64
