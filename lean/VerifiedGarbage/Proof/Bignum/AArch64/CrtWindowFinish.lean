module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinishSquare
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingMath
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! A final partial window consumes exactly the pending exponent bits. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (finish)

theorem selectProduct_ok (M : Mont) (S : Selector) {s : State} {P : Addr} {w E v : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hv : v < 32) (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.seq S.code (M.mm aY aY Crt.aT)) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ (E + v) * 2 ^ (64 * w) % X) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (S.ok hc hw hw' hv ht.tab hn)
    fun u ⟨cu,tu,fu,ku⟩ => ?_)
  have fu' := fu.mono (selRanges_sub w)
  have tabu := ht.of_win fu' hc.scrT.nowrap
  have ey := selection_keeps_y fu hc.good.scr.nowrap
  refine WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := E) (v := v) cu.base hw hw' hR
    (by rw [tu]; exact ht.lt v hv)
    (by intro hQ; rw [ey]; exact hyv hQ)
    (by intro hQ; rw [tu]; exact ht.val hQ v hv))
    fun t ⟨_,yt,vt,_,ft,kt⟩ => ?_
  exact ⟨cu.of_win ft kt.wr (kt.gpr .x0 (by decide)),tabu.of_win ft cu.scrT.nowrap,
    yt,vt,fu'.trans ft,(ku.trans kt).mono (by decide)⟩

theorem finishLoad_ok {s : State} {P : Addr} {w b : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (bc : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) :
    WP isa (.block [ldh .x3 Crt.sBit]) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 b) ∧ Keep [.x3] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [hc.good.x0,hdr_enc (show Crt.sBit < 32 by decide),hc.ld (i := Crt.sBit) (by decide),bc]

/-- No padding: the final exponent is precisely the completed prefix and
its pending `b` bits, including the empty-tail case. -/
theorem finish_ok (M : Mont) (S : Selector) {s : State} {P : Addr} {w b K : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hp : Pending s P w X Q x b K) :
    WP isa (finish M.mm S.code) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ K * 2 ^ (64 * w) % X) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain ⟨E,v,hb,hv,hK,hy,hyv,hn,bc⟩ := hp
  unfold finish
  refine WP.seq (WP.mono (finishLoad_ok hc bc) fun u ⟨⟨hm,h3⟩,ku⟩ => ?_)
  have fu : Frm P (crtWinRanges w) s.mem u.mem := hm.symm ▸ Frm.refl _ _ _
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  have tu := ht.of_win fu hc.scrT.nowrap
  by_cases hz : b = 0
  · subst b
    have vv : v = 0 := by simpa using hv
    have ek : E = K := by simpa [vv] using hK
    refine WP.ite false ?_ (by simp) (fun _ => ?_)
    · change some (!(u.gpr .x3 == 0)) = some false
      rw [h3]; rfl
    · apply WP.block_nil
      exact ⟨cu,tu,hm.symm ▸ hy,by simpa [hm,← ek] using hyv,fu,ku.mono (by decide)⟩
  · refine WP.ite true ?_ (fun _ => ?_) (by simp)
    · change some (!(u.gpr .x3 == 0)) = some true
      rw [h3]
      have nz : BitVec.ofNat 64 b ≠ 0 := by
        intro h
        have he := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)] at he
        exact hz he
      rw [beq_eq_false_iff_ne.mpr nz]
      rfl
    · refine WP.seq (WP.mono (finishSquares_ok M (E := E) cu tu hw hw' hR (hm.symm ▸ hy)
        (by simpa [hm] using hyv) (by omega) hb (by simpa [hm] using bc))
        fun a ⟨ca,ta,_,va,_,fa,ka,ha⟩ => ?_)
      refine WP.mono (selectProduct_ok M S (E := 2 ^ b * E) (v := v) ca ta hw hw' hR va
        (by have := pending_lt16 hb hv; omega)
        (by rw [ha _ (by decide) (by decide),hm]; exact hn))
        fun t ⟨ct,tt,yt,vt,ft,kt⟩ => ?_
      refine ⟨ct,tt,yt,?_,(fu.trans fa).trans ft,((ku.trans ka).trans kt).mono (by decide)⟩
      intro hQ
      simpa only [Nat.mul_comm (2 ^ b) E,hK] using vt hQ

end VG.Proof.Bignum.AArch64.WindowFive
