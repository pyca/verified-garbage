module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedGroup
import Mathlib.Data.Int.ModEq

/-! A complete five-byte group contributes exactly its 40 exponent bits. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (appliedBatch)

theorem appliedBatch_ok (W : Window) {s : State} {P src : Addr} {w i : Nat}
    {mi : BitVec 64} {X Xc x E : Nat} {Q : Prop} {bs : List Byte}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hbit : word s.mem P (8 * Crt.sBit) = 0)
    (hnib : word s.mem P (8 * Crt.sNib) = 0)
    (hbs : 5 ≤ bs.length) (hp : word s.mem P (8 * Crt.sExp) = src)
    (hi : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hld : ∀ j < 5, InRegions (s.rd ++ s.wr) ((src + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) 1)
    (hb : ∀ j (hj : j < 5), s.mem ((src + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) = bs[j]'(by omega)) :
    WP isa (appliedBatch W.code) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ (E * 256 ^ 5 + pre bs 5) * 2 ^ (64 * w) % X) ∧
      word t.mem P (8 * Crt.sBit) = 0 ∧ word t.mem P (8 * Crt.sNib) = 0 ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold appliedBatch
  refine WP.seq (WP.mono (loadGroup_ok hc hbs hp hi hld hb) fun u ⟨hm,ku⟩ => ?_)
  have ho := writeW_outside s.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (pre bs 5)) (by decide)
  rw [← hm] at ho
  have fu : Frm P (crtWinRanges w) s.mem u.mem := Frm.of_outside ho (by simp [crtWinRanges])
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  have tu := ht.of_win fu hc.scrT.nowrap
  have yu : wv u.mem P (slot w aY) w = wv s.mem P (slot w aY) w :=
    ho.wv (by have := hdr_lt_slot w aY (show Crt.sV < 32 by decide); omega)
      (by have := hc.good.scr.nowrap; have := slot_le (w := w) (show aY < 8 by decide); omega)
  have hV := pre_lt bs hbs
  refine WP.mono (appliedGroup_ok W 8 (Q := Q) (x := x) (E := E) (V := pre bs 5)
    (by decide) cu tu hw hw' hR (yu.symm ▸ hy) (fun hQ => by rw [yu]; exact hyv hQ)
    (by rw [hm,word_writeW_self]) (by omega)
    (by rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hbit)
    (by rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hnib)) fun t ⟨ct,tt,yt,vt,_,bt,nt,ft,kt⟩ => ?_
  refine ⟨ct,tt,yt,?_,bt,nt,fu.trans ft,(ku.trans kt).mono (by decide)⟩
  intro hQ
  simpa only [show 32 ^ 8 = 256 ^ 5 from rfl, Nat.mod_eq_of_lt hV] using vt hQ

end VG.Proof.Bignum.AArch64.WindowFive
