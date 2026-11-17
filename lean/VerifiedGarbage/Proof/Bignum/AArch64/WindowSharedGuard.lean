module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorGuard
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawBody
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcGuard
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedWork
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedSave
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore

/-! ### `Bignum.AArch64.WindowSharedFast`, which this module and modules that import it used -/

section

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

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

def code : Prog isa := VG.Impl.Rsa.AArch64.WindowShared.code
  (VG.Impl.Rsa.AArch64.WindowFive.windowBody Mont.productEight.mm WindowVector.selector.code)

def Post (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc v : Nat) (t : State) : Prop :=
  TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
  wv t.mem P (slot w aY) w * (2^(64*w))^32 % X =
    wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8+v)) w % X ∧
  word t.mem P (8*Crt.sNib) = 0 ∧ word t.mem P (8*Crt.sBit) = 0 ∧
  Frm P (rawWindowRanges w) s.mem t.mem ∧ Keep mmRegs s t

theorem guarded_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 2 ≤ w) (hw' : w < 2^30) (hy : wv s.mem P (slot w aY) w < X)
    (hv : v < 32) (hnib : word s.mem P (8*Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa code s (Post s P w mi X Xc v) := by
  unfold code VG.Impl.Rsa.AArch64.WindowShared.code
  refine WP.seq (WP.mono (BlockedRedc.guard_ok hc.good.scr hc.good.x0 hc.good.hdr
    (Nat.le_refl _) (by omega_using [hw'])) fun u ⟨⟨hm,h3,h4⟩,ku⟩ => ?_)
  have cu := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have lift {c : Prog isa} (hp : WP isa c u (Post u P w mi X Xc v)) :
      WP isa c u (Post s P w mi X Xc v) := WP.mono hp fun t ⟨ct,yt,vt,nt,bt,ft,kt⟩ => by
    rw [hm] at vt ft
    exact ⟨ct,yt,vt,nt,bt,ft,(ku.trans kt).mono (by decide)⟩
  have slow := lift (WP.mono (WindowFive.windowBody_raw_ok Mont.productEight WindowVector.selector
    cu (hm ▸ ht) hw hw' (hm ▸ hy) hv (hm ▸ hnib))
    (fun _ ⟨ct,yt,vt,nt,bt,ft,kt,_⟩ => ⟨ct,yt,vt,nt,bt,ft,kt⟩))
  by_cases hfast : 16 ≤ w
  · refine WP.ite true (by rw [eval_nonzero,h3,ne_zero_iff,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show w/16 < 2^64 by omega_using [hw']),decide_eq_true (show w/16 ≠ 0 by omega_using [hfast])])
      (fun _ => ?_) (by simp)
    by_cases hd : w % 8 = 0
    · exact WP.ite true (by rw [eval_zero,h4,hd]; rfl)
        (fun _ => lift (fast_ok cu (hm ▸ ht) hfast hw' hd hv (hm ▸ hnib))) (by simp)
    · exact WP.ite false (by rw [eval_zero,h4,eq_zero_iff,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show w%8 < 2^64 by omega_using []),decide_eq_false hd]) (by simp) (fun _ => slow)
  · exact WP.ite false (by rw [eval_nonzero,h3,show w/16 = 0 by omega_using [hfast]]; rfl) (by simp) (fun _ => slow)

end VG.Proof.Bignum.AArch64.WindowShared
