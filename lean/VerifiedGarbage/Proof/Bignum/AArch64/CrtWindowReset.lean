module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Reset the pending digit and bit count while preserving arithmetic arrays. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (resetWindow)

theorem resetWindow_mem {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) :
    WP isa (.block resetWindow) s fun t =>
      t.mem = (s.mem.writeW (off P (8 * Crt.sNib)) (0#64)).writeW (off P (8 * Crt.sBit)) (0#64) ∧
      Keep [.x3] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [resetWindow,hc.good.x0,hdr_enc (show Crt.sNib < 32 by decide),
    hdr_enc (show Crt.sBit < 32 by decide),hc.st (i := Crt.sNib) (by decide),
    hc.st (i := Crt.sBit) (by decide)]
  rfl

theorem resetWindow_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) :
    WP isa (.block resetWindow) s fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w = wv s.mem P (slot w aY) w ∧
      word t.mem P (8 * Crt.sNib) = 0 ∧ word t.mem P (8 * Crt.sBit) = 0 ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep [.x3] s t ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  refine WP.mono (resetWindow_mem hc) fun t ⟨hm,kt⟩ => ?_
  have oa := writeW_outside s.mem P (d := 8 * Crt.sNib) (0#64) (by decide)
  have ob := writeW_outside (s.mem.writeW (off P (8 * Crt.sNib)) (0#64)) P
    (d := 8 * Crt.sBit) (0#64) (by decide)
  rw [← hm] at ob
  have fa : Frm P (crtWinRanges w) _ _ := Frm.of_outside oa (by simp [crtWinRanges])
  have fb : Frm P (crtWinRanges w) _ _ := Frm.of_outside ob (by simp [crtWinRanges])
  have hf := fa.trans fb
  have hny : slot w aY + 8 * w ≤ 2 ^ 64 := by
    have := hc.good.scr.nowrap
    have := slot_le (w := w) (show aY < 8 by decide)
    omega
  refine ⟨hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),?_,?_,?_,hf,kt,?_⟩
  · rw [ob.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega) hny,
      oa.wv (by have := hdr_lt_slot w aY (show Crt.sNib < 32 by decide); omega) hny]
  · rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),word_writeW_self]
    rfl
  · rw [hm,word_writeW_self]
    rfl
  · intro k hk hn hb
    rw [hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hb),hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hn)]

theorem resetWindow_ct : RelCT isa (Two fun (P : Addr) s => s.gpr .x0 = P)
    (.block resetWindow) (fun _ _ => True) := by
  apply two_taint [.x0] (hc := .block [])
  · intro P s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm
  · rfl

end VG.Proof.Bignum.AArch64.WindowFive
