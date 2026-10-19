module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCopy

/-! The blocked selector's exact instruction shape and selected byte sequence. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

theorem blocked_eq : VG.Impl.Rsa.AArch64.WindowSelectVector.blocked 32 =
    .seq (.block setup) (.seq (.loop rawStep (.nonzero .x .x13)) (.block finish)) := rfl

theorem body_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 8 ≤ w) (hw' : w < 2 ^ 30) (hv : v < 32)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.seq (.block setup) (.loop rawStep (.nonzero .x .x13))) s fun t =>
      ∃ s₀, s₀.mem = s.mem ∧ Keep mmRegs s s₀ ∧ LoopInv s₀ P w mi X Xc v (w / 8) t := by
  apply WP.seq
  refine WP.mono (setup_ok hc hw' hN) fun u ⟨⟨h6,h13,h17,h22,h24,hm⟩,ku⟩ => ?_
  have ctx : TableCtx u P w mi X Xc := hc.of_win
    (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have h0 : LoopInv u P w mi X Xc v 0 u := ⟨ctx, by rw [hm]; exact ht,
    h6, by simpa using h17, h22, h24, Outside.refl _ _ _ _,
    fun k hk => by omega, Keep.refl _ _⟩
  exact WP.mono (blocks_ok hw hw' hv h0 h13) fun t hI =>
    ⟨u,hm,ku.mono (by decide),hI⟩

theorem blocked_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 8 ≤ w) (hw' : w < 2 ^ 30) (hd : w % 8 = 0)
    (hv : v < 32) (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked 32) s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hcount : 64 * (w / 8) = 8 * w := by omega
  have he : slot w 8 + 8 * (w + 2) * v = slot w (8 + v) := by
    simp only [slot, Nat.add_mul, Nat.mul_comm v, Nat.add_assoc]
  rw [blocked_eq]
  apply WP.assoc
  apply WP.seq
  refine WP.mono (body_ok hc hw hw' hv ht hN) fun u ⟨s₀,hm₀,k₀,hI⟩ => ?_
  have hn := hI.ctx.scrT.nowrap
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  have hval : wv u.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w := by
    apply wv_copy
    simpa only [hcount,he,hm₀] using hI.bytes
  have fb : Frm P (selRanges w) s.mem u.mem := by
    have ho := hI.frame
    rw [hm₀,hcount] at ho
    exact Frm.of_outside (ho.mono (o' := slot w Crt.aT) (n' := 8 * (w + 2))
      (by omega) (by omega)) (by simp [selRanges])
  refine WP.mono (finish_ok hI.ctx hw' hI.tab hI.stride) fun t ⟨hm,kt⟩ => ?_
  have o₁ := writeW_outside u.mem P (d := 8 * Crt.sEnt)
    (off P (slot w 8 + 32 * (8 * (w + 2)))) (by decide)
  have o₂ := writeW_outside (u.mem.writeW (off P (8 * Crt.sEnt))
    (off P (slot w 8 + 32 * (8 * (w + 2))))) P (d := 8 * Crt.sJ) (BitVec.ofNat 64 32) (by decide)
  rw [← hm] at o₂
  have ff : Frm P (selRanges w) u.mem t.mem :=
    (Frm.of_outside o₁ (by simp [selRanges])).trans (Frm.of_outside o₂ (by simp [selRanges]))
  refine ⟨hI.ctx.of_win (ff.mono (selRanges_sub w)) kt.wr (kt.gpr .x0 (by decide)), ?_,
    fb.trans ff, ((k₀.trans hI.keep).trans kt).mono (by decide)⟩
  rw [o₂.wv (by have := hdr_lt_slot w Crt.aT (show Crt.sJ < 32 by decide); omega) (by omega),
    o₁.wv (by have := hdr_lt_slot w Crt.aT (show Crt.sEnt < 32 by decide); omega) (by omega)]
  exact hval

end VG.Proof.Bignum.AArch64.WindowVector
