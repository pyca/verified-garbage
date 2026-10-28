module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp

/-! Final pending bits need exactly their own count of squares, without padding. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (finishSquare)

theorem finishSquare_ok (M : Mont) {s : State} {P : Addr} {w b E : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hb : 1 ≤ b) (bc : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) :
    WP isa (finishSquare M.mm) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ (2 * E) * 2 ^ (64 * w) % X) ∧
      word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t.gpr .x3 = BitVec.ofNat 64 (b - 1) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ k < 32, k ≠ Crt.sBit → word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  unfold finishSquare
  refine WP.seq (WP.mono (crtSq_ok M hc.base hw hw' hR hy hyv)
    fun u ⟨_,yu,vu,hu,fu,ku⟩ => ?_)
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  have tu := ht.of_win fu hc.scrT.nowrap
  refine WP.mono (crtBitEnd_ok cu (b := b) (by rw [hu _ (by decide)]; exact bc) hb)
    fun t ⟨⟨hm,h3⟩,kt⟩ => ?_
  have out := writeW_outside u.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b - 1)) (by decide)
  rw [← hm] at out
  have ft : Frm P (crtWinRanges w) u.mem t.mem := Frm.of_outside out (by simp [crtWinRanges])
  have ey : wv t.mem P (slot w aY) w = wv u.mem P (slot w aY) w :=
    out.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega) (by
      have := cu.good.scr.nowrap
      have := slot_le (w := w) (show aY < 8 by decide)
      omega)
  refine ⟨cu.of_win ft kt.wr (kt.gpr .x0 (by decide)),tu.of_win ft cu.scrT.nowrap,
    ey.symm ▸ yu,?_,?_,h3,fu.trans ft,(ku.trans kt).mono (by decide),?_⟩
  · intro hQ; rw [ey]; exact vu hQ
  · rw [hm,word_writeW_self]
  · intro k hk he
    rw [hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm he),hu k hk]

/-- State after `i` of the final `b` squarings. -/
def FinishInv (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc : Nat)
    (Q : Prop) (x E b i : Nat) (t : State) : Prop :=
  TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
  wv t.mem P (slot w aY) w < X ∧
  (Q → wv t.mem P (slot w aY) w % X = x ^ (2 ^ i * E) * 2 ^ (64 * w) % X) ∧
  word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - i) ∧
  Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
  (∀ k < 32, k ≠ Crt.sBit → word t.mem P (8 * k) = word s.mem P (8 * k))

theorem finishSquares_ok (M : Mont) {s : State} {P : Addr} {w b E : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hb : 1 ≤ b) (hb' : b < 5) (bc : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) :
    WP isa (.loop (finishSquare M.mm) (.nonzero .x .x3)) s
      (FinishInv s P w mi X Xc Q x E b b) := by
  apply count_loop (cr := .x3) (n := b) hb (FinishInv s P w mi X Xc Q x E b)
  · intro i hi u hu
    obtain ⟨cu,tu,yu,vu,bc,fu,ku,hh⟩ := hu
    refine WP.mono (finishSquare_ok M cu tu hw hw' hR yu vu (by omega) bc)
      fun t ⟨ct,tt,yt,vt,bt,h3,ft,kt,hh'⟩ => ⟨?_,?_⟩
    · refine ⟨ct,tt,yt,?_,?_,fu.trans ft,(ku.trans kt).mono (by decide),
        fun k hk he => (hh' k hk he).trans (hh k hk he)⟩
      · intro hQ
        rw [vt hQ]
        congr 3
        simp only [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      · simpa only [Nat.sub_sub] using bt
    · rw [h3,cnt_ne (by omega)]
      omega
  · exact ⟨hc,ht,hy,by simpa using hyv,by simpa using bc,Frm.refl _ _ _,Keep.refl _ _,fun _ _ _ => rfl⟩

end VG.Proof.Bignum.AArch64.WindowFive
