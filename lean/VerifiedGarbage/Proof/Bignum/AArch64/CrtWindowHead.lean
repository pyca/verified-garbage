module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.Math

/-! Prepare the wider table within the existing RSA workspace allocation. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem expHead_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : SubCtx s B Z o w wx minv) (hT : Scr s (off B o) (slot wx 8 + CrtWindowFive.tabBytes32 wx)) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.expHead M.mm sp sl) s
      (PrefixInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) Q x ep eb 0 0) := by
  have hPn := hT.nowrap
  have hBn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc₀ : TableCtx s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) :=
    ⟨hc.good, hT, hn, hinv, rfl⟩
  unfold VG.Impl.Rsa.AArch64.WindowFive.expHead
  refine WP.seq (WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep) (off B o) (d := 8 * Crt.sExpLen)
    (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW
    (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off B o) (d := 8 * Crt.sI)
    (BitVec.ofNat 64 0) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off B o) (CrtWindowFive.crtExpRanges wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [CrtWindowFive.crtExpRanges])).trans (Frm.of_outside o2 (by simp [CrtWindowFive.crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [CrtWindowFive.crtExpRanges]))
  have hc₁ := hc₀.of_frm f₁ k₁.wr (k₁.gpr .x0 (by decide))
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have hYe₁ : wv t₁.mem (off B o) (slot wx aY) wx = wv s.mem (off B o) (slot wx aY) wx := by
    rw [o3.wv (by unfold Crt.sI sFn at *; omega_arith) (by omega_arith),
      o2.wv (by unfold Crt.sExpLen sFn at *; omega_arith) (by omega_arith),
      o1.wv (by unfold Crt.sExp sFn at *; omega_arith) (by omega_arith)]
  refine WP.seq (WP.mono (tabBuild_ok M (Q := Q) (x := x) hc₁ hw2 (by omega) hR hxl hxc
    (by rw [hYe₁]; exact hyl) (fun hq => by rw [hYe₁]; exact hyc hq))
    fun t₂ ⟨hc₂,ht₂,ye₂,hh₂,f₂,k₂⟩ => ?_)
  refine WP.mono (resetWindow_ok hc₂) fun t₃ ⟨hc₃,ye₃,nb₃,bc₃,f₃,k₃,hh₃⟩ => ?_
  refine ⟨hc₃,ht₂.of_win f₃ hc₂.scrT.nowrap,?_,?_,?_,?_,
    (f₁.trans f₂).trans (f₃.mono (CrtWindowFive.crtWinRanges_sub wx)),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ⟨0,0,by decide,by decide,by simp [pre_zero],?_,?_,nb₃,bc₃⟩
    · rw [ye₃,ye₂,hYe₁]; exact hyl
    · intro hq
      rw [ye₃,ye₂,hYe₁,hyc hq,Nat.pow_zero,Nat.one_mul]
  · rw [hh₃ _ (by decide) (by decide) (by decide),hh₂ _ (by decide) (by decide) (by decide) (by decide),
      hm₁,word_writeW_self]
  · rw [hh₃ _ (by decide) (by decide) (by decide),hh₂ _ (by decide) (by decide) (by decide) (by decide),hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := Crt.sExpLen) _ _ _ (by decide) (by decide) (by decide),word_writeW_self]
  · rw [hh₃ _ (by decide) (by decide) (by decide),hh₂ _ (by decide) (by decide) (by decide) (by decide),hm₁,
      hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),word_writeW_self]

end VG.Proof.Bignum.AArch64.WindowFive
