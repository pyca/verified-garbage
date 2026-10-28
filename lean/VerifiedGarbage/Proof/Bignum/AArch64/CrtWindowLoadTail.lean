module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv

import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Loading a trailing byte preserves its pending exponent and table. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (loadTailByte)

theorem loadTailByte_ok {s : State} {P ep : Addr} {w i b K : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {v : Byte}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hp : Pending s P w X Q x b K)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hep : word s.mem P (8 * Crt.sExp) = ep)
    (hread : InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbyte : s.mem (ep + BitVec.ofNat 64 i) = v) :
    WP isa (.block loadTailByte) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧ Pending t P w X Q x b K ∧
      word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 v.toNat ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep [.x3,.x4] s t ∧
      (∀ k < 32, k ≠ Crt.sV → word t.mem P (8*k) = word s.mem P (8*k)) := by
  refine WP.mono (WP.keep [.x3,.x4] (Q := fun t =>
    t.mem = s.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 v.toNat)) ?_ rfl rfl rfl)
    fun t ⟨hm,kt⟩ => ?_
  · brun [loadTailByte,hc.good.x0,hdr_enc (show Crt.sExp < 32 by decide),
      hdr_enc (show Crt.sI < 32 by decide),hdr_enc (show Crt.sV < 32 by decide),
      hc.ld (i := Crt.sExp) (by decide),hc.ld (i := Crt.sI) (by decide),
      hc.st (i := Crt.sV) (by decide),hidx,hep,hread,zext_byte,hbyte]
  have out := writeW_outside s.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 v.toNat) (by decide)
  rw [← hm] at out
  have ft : Frm P (crtWinRanges w) s.mem t.mem := Frm.of_outside out (by simp [crtWinRanges])
  have hh : ∀ k < 32, k ≠ Crt.sV → word t.mem P (8*k) = word s.mem P (8*k) := by
    intro k hk he
    rw [hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm he)]
  have ey : wv t.mem P (slot w aY) w = wv s.mem P (slot w aY) w :=
    out.wv (by have := hdr_lt_slot w aY (show Crt.sV < 32 by decide); omega) (by
      have := hc.good.scr.nowrap
      have := slot_le (w := w) (show aY < 8 by decide)
      omega)
  refine ⟨hc.of_win ft kt.wr (kt.gpr .x0 (by decide)),ht.of_win ft hc.scrT.nowrap,?_,?_,ft,kt,hh⟩
  · obtain ⟨E,d,hb,hd,hK,hy,hyv,hn,bc⟩ := hp
    exact ⟨E,d,hb,hd,hK,ey.symm ▸ hy,by simpa only [ey] using hyv,
      (hh _ (by decide) (by decide)).trans hn,(hh _ (by decide) (by decide)).trans bc⟩
  · rw [hm,word_writeW_self]

end VG.Proof.Bignum.AArch64.WindowFive
