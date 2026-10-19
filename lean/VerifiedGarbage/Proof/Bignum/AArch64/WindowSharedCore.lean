module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowShared
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowRawTriangle

import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedLoop
import VerifiedGarbage.Proof.Bignum.CrtWindowRelation
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.WindowOperations
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

theorem core_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 16 ≤ w) (hw' : w < 2^30) (hmod : w % 8 = 0)
    (hb : word s.mem P (8*Crt.sBit) = BitVec.ofNat 64 5)
    (hv : v < 32) (hnib : word s.mem P (8*Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa VG.Impl.Rsa.AArch64.WindowShared.core s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2^(64*w))^32 % X =
        wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8+v)) w % X ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep WindowRaw.regs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sBit →
        word t.mem P (8*k) = word s.mem P (8*k)) := by
  unfold VG.Impl.Rsa.AArch64.WindowShared.core
  refine WP.seq (WP.mono (squares_ok hc hw hw' hmod hb) fun a ⟨ca,va,ha,fa,ka⟩ => ?_)
  have ta := ht.of_win fa hc.scrT.nowrap
  have et : wv a.mem P (slot w (8+v)) w = wv s.mem P (slot w (8+v)) w :=
    fa.wv_eq (fun r hr => by have := crtWinRanges_ent w v r hr; omega)
      (by have := CrtWindowFive.ent32_le w hv; have := hc.scrT.nowrap; omega)
  refine WP.seq (WP.mono (WindowVector.blocked_ok ca (by omega) hw' hmod hv ta.tab
    (by rw [ha _ (by decide) (by decide)]; exact hnib)) fun b ⟨cb,tb,fb,kb⟩ => ?_)
  have ey := WindowFive.selection_keeps_y fb ca.good.scr.nowrap
  refine WP.mono (WindowArithmetic.product_ok (o := aY) (a := aY) (b := Crt.aT)
    cb.good.scr cb.good.x0 cb.good.hdr (Nat.le_refl _) hw (by omega) hmod
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) cb.inv (by rw [cb.n,tb]; exact ta.lt v hv))
    fun t ⟨yt,vt,hat,kt⟩ => ?_
  rw [cb.n] at yt vt
  have ft : Frm P (crtWinRanges w) b.mem t.mem := Frm.of_arrays hat (by simp [crtWinRanges])
  have vb : wv b.mem P (slot w aY) w * (2^(64*w))^31 % X = wv s.mem P (slot w aY) w ^ 32 % X := by
    rw [ey]; exact va
  have result := CrtWindowFive.product_scale vt vb
  rw [tb,et] at result
  refine ⟨cb.of_win ft kt.wr (kt.gpr .x0 (by decide)),yt,result,
    (fa.trans (fb.mono (selRanges_sub w))).trans ft,
    ((ka.trans kb).trans kt).mono (by decide),?_⟩
  intro k hk he hj hb'
  rw [hat.hslot hk, fb.word_eq (fun r hr => by
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := hdr_lt_slot w Crt.aT hk; simp only; omega
    · simp only; omega
    · simp only; omega) (by
      have := hdr_lt_slot w 8 hk
      have := ca.good.scr.nowrap
      omega), ha k hk hb']

end VG.Proof.Bignum.AArch64.WindowShared
