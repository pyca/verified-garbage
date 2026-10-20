module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDigit
import Mathlib.Data.Int.ModEq

/-! A fixed-position digit followed by its complete arithmetic window. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (groupDigit windowCore)

/-- Consuming a digit keeps the packed exponent group available for the
remaining fixed-position windows. No exponent-dependent access is used. -/
theorem windowStep_ok (M : Mont) (S : Selector) {t : State} {P : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x E V shift : Nat} {Q : Prop}
    (hc : TableCtx t P w mi X Xc) (ht : CrtWindowFive.CTab t.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv t.mem P (slot w aY) w < X)
    (hyv : Q → wv t.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V)
    (hV' : V < 2 ^ 64) (hshift : shift < 64) :
    WP isa (.seq (.block (groupDigit shift)) (windowCore M.mm S.code)) t fun u =>
      TableCtx u P w mi X Xc ∧ CrtWindowFive.CTab u.mem P w X Q x ∧
      wv u.mem P (slot w aY) w < X ∧
      (Q → wv u.mem P (slot w aY) w % X =
        x ^ (32 * E + V / 2 ^ shift % 32) * 2 ^ (64 * w) % X) ∧
      word u.mem P (8 * Crt.sV) = BitVec.ofNat 64 V ∧
      Frm P (crtWinRanges w) t.mem u.mem ∧ Keep mmRegs t u := by
  refine WP.seq (WP.mono (groupDigit_ok hc.base hV hV' hshift)
    fun a ⟨hm, ka⟩ => ?_)
  have oa := writeW_outside t.mem P (d := 8 * Crt.sNib)
    (BitVec.ofNat 64 (V / 2 ^ shift % 32)) (by decide)
  rw [← hm] at oa
  have fa : Frm P (crtWinRanges w) t.mem a.mem :=
    Frm.of_outside oa (by simp [crtWinRanges])
  have ca := hc.of_win fa ka.wr (ka.gpr .x0 (by decide))
  have ta := ht.of_win fa hc.scrT.nowrap
  have ya : wv a.mem P (slot w aY) w = wv t.mem P (slot w aY) w :=
    oa.wv (by have := hdr_lt_slot w aY (show Crt.sNib < 32 by decide); omega)
      (by have := hc.good.scr.nowrap; have := slot_le (w := w) (show aY < 8 by decide); omega)
  refine WP.mono (windowCore_ok M S (Q := Q) (x := x) (E := E) (v := V / 2 ^ shift % 32) ca ta hw hw' hR (ya.symm ▸ hy)
    (fun hQ => by rw [ya]; exact hyv hQ) (Nat.mod_lt _ (by decide))
    (by rw [hm, word_writeW_self])) fun u ⟨cu, tu, yu, vu, fu, ku, hu⟩ => ?_
  refine ⟨cu, tu, yu, vu, ?_, fa.trans fu, (ka.trans ku).mono (by decide)⟩
  rw [hu _ (by decide) (by decide) (by decide), hm,
    hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
  exact hV

end VG.Proof.Bignum.AArch64.WindowFive
