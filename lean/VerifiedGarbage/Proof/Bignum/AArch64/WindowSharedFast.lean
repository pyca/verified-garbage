module

import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedSave
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
public import VerifiedGarbage.Proof.Bignum.CrtWindowFrame
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

theorem fast_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0)
    (hv : v < 32) (hnib : word s.mem P (8*Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.fast s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2^(64*w))^32 % X =
        wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8+v)) w % X ∧
      word t.mem P (8*Crt.sNib) = 0 ∧ word t.mem P (8*Crt.sBit) = 0 ∧
      Frm P (rawWindowRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.fast
  refine WP.seq (WP.mono (save_ok s) fun u ⟨⟨hm,hSaved⟩,ku⟩ => ?_)
  have fu : Frm P (crtWinRanges w) s.mem u.mem := by rw [hm]; exact Frm.refl _ _ _
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  obtain ⟨tr,v',ex,cv,yv,vv,fv,kv,hhv⟩ := work_ok cu (hm ▸ ht) hw hw' hmod hv (hm ▸ hnib)
  apply WP.seq
  refine ⟨tr,v',ex,?_⟩
  refine WP.seq (WP.mono (restore_ok v') fun d ⟨⟨hdm,hRestored⟩,kd⟩ => ?_)
  have fd : Frm P (crtWinRanges w) v'.mem d.mem := by rw [hdm]; exact Frm.refl _ _ _
  have cd := cv.of_win fd kd.wr (kd.gpr .x0 (by decide))
  have kpre : Keep mmRegs s d := BlockedRedc.keep_restored
    (((ku.trans kv).trans kd).mono (by decide)) (by
      intro r hr
      obtain ⟨vr,hvr⟩ := saved_lane_exists r hr
      have hr' := hRestored (r,vr,0) hvr
      have hs' := hSaved (r,vr,0) hvr
      have hv' := Exec.vec (work_keeps_vectors (r,vr,0) hvr) ex
      change d.gpr r = s.gpr r
      change d.gpr r = laneOf v' vr 0 at hr'
      rw [hr',laneOf,hv']
      exact hs')
  refine WP.mono (WindowFive.resetWindow_ok cd) fun t ⟨ct,yt,nt,bt,ft,kt,hht⟩ => ?_
  have fpre := (fu.trans fv).trans fd
  have ydt : wv d.mem P (slot w aY) w = wv v'.mem P (slot w aY) w := by rw [hdm]
  refine ⟨ct,by rw [yt,ydt]; exact yv,?_,nt,bt,(fpre.trans ft).window_tight ?_,
    (kpre.trans kt).mono (by decide)⟩
  · rw [yt,ydt,hm] at *
    exact vv
  · rw [hht _ (by decide) (by decide) (by decide),hdm,
      hhv _ (by decide) (by decide) (by decide) (by decide),hm]

end VG.Proof.Bignum.AArch64.WindowShared
