module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl

/-! Advancing the public byte index leaves the table and exponent unchanged. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (advance)

theorem advance_pending (n : Nat) (hn : n < 4096) {s : State} {P : Addr} {w i b K : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hp : Pending s P w X Q x b K)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) :
    WP isa (.block (advance n)) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      Pending t P w X Q x b K ∧ word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 (i+n) ∧
      Frm P (CrtWindowFive.crtExpRanges w) s.mem t.mem ∧ Keep [.x3] s t ∧
      (∀ k < 32, k ≠ Crt.sI → word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  refine WP.mono (advance_ok n hn hc hidx) fun t ⟨hm,kt⟩ => ?_
  have out := writeW_outside s.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i+n)) (by decide)
  rw [← hm] at out
  have ft : Frm P (CrtWindowFive.crtExpRanges w) s.mem t.mem :=
    Frm.of_outside out (by simp [CrtWindowFive.crtExpRanges])
  have hh : ∀ k < 32, k ≠ Crt.sI → word t.mem P (8*k) = word s.mem P (8*k) := by
    intro k hk he
    rw [hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm he)]
  have ea : ∀ j < 40, wv t.mem P (slot w j) w = wv s.mem P (slot w j) w := by
    intro j hj
    exact out.wv (by have := hdr_lt_slot w j (show Crt.sI < 32 by decide); omega) (by
      have := hc.scrT.nowrap
      have hb := slot_mono w (show j+1 ≤ 40 by omega)
      rw [slot_succ] at hb
      unfold slot hdrBytes CrtWindowFive.tabBytes32 at *
      omega)
  refine ⟨hc.of_frm ft kt.wr (kt.gpr .x0 (by decide)),?_,?_,?_,ft,kt,hh⟩
  · exact ⟨(hh _ (by decide) (by decide)).trans ht.tab,
      fun j hj => (ea (8+j) (by omega)).symm ▸ ht.lt j hj,
      fun hQ j hj => (ea (8+j) (by omega)).symm ▸ ht.val hQ j hj⟩
  · obtain ⟨E,v,hb,hv,hK,hy,hyv,hv',hb'⟩ := hp
    exact ⟨E,v,hb,hv,hK,(ea aY (by decide)).symm ▸ hy,
      by simpa only [ea aY (by decide)] using hyv,
      (hh _ (by decide) (by decide)).trans hv',(hh _ (by decide) (by decide)).trans hb'⟩
  · rw [hm,word_writeW_self]

end VG.Proof.Bignum.AArch64.WindowFive
