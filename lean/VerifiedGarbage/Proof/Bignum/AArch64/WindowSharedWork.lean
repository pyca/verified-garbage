module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle

import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedCore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

theorem init_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) :
    WP isa (.block [movi .x3 5, sth .x3 Crt.sBit]) s fun t =>
      (t.mem = s.mem.writeW (off P (8*Crt.sBit)) (BitVec.ofNat 64 5)) ∧ Keep [.x3] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [hc.good.x0,hdr_enc (show Crt.sBit < 32 by decide),hc.st (i := Crt.sBit) (by decide)]
  rfl

theorem work_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0)
    (hv : v < 32) (hnib : word s.mem P (8*Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.work s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2^(64*w))^32 % X =
        wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8+v)) w % X ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep WindowRaw.regs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sBit →
        word t.mem P (8*k) = word s.mem P (8*k)) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.work
  refine WP.seq (WP.mono (init_ok hc) fun u ⟨hm,ku⟩ => ?_)
  have hout := writeW_outside s.mem P (d := 8*Crt.sBit) (BitVec.ofNat 64 5) (by decide)
  rw [← hm] at hout
  have fu : Frm P (crtWinRanges w) s.mem u.mem := Frm.of_outside hout (by simp [crtWinRanges])
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  have tu := ht.of_win fu hc.scrT.nowrap
  have read (j : Nat) (hj : slot w j+8*w ≤ slot w 8+CrtWindowFive.tabBytes32 w) :
      wv u.mem P (slot w j) w = wv s.mem P (slot w j) w :=
    hout.wv (by have := hdr_lt_slot w j (show Crt.sBit < 32 by decide); omega)
      (by have := hc.scrT.nowrap; omega)
  refine WP.mono (core_ok cu tu hw hw' hmod (by rw [hm,word_writeW_self]) hv
    (by rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hnib))
    fun t ⟨ct,yt,vt,ft,kt,hh⟩ => ?_
  rw [read aY (by have := slot_le (w := w) (show aY < 8 by decide); omega),
    read (8+v) (by have := CrtWindowFive.ent32_le w hv; omega)] at vt
  refine ⟨ct,yt,vt,fu.trans ft,(ku.trans kt).mono (by decide),?_⟩
  intro k hk he hj hb
  rw [hh k hk he hj hb,hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hb)]

end VG.Proof.Bignum.AArch64.WindowShared
