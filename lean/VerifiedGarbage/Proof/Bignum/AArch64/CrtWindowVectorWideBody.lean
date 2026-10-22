module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWideLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCopy
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The 128-byte selector's setup, exact instruction shape and selected bytes. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

def wsetup : List Instr :=
  [ldh .x12 sW, .addImm .x .x6 .x12 2, .lsl .x .x6 .x6 3, .lsr .x .x13 .x12 4,
   ldh .x5 Crt.sNib, movi .x2 32, .sub .x .x5 .x2 .x5, movi .x8 0, .subImm .x .x7 .x8 1,
   ldh .x17 (sArr Crt.aT)]

theorem shr4_width {w : Nat} (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w >>> 4 = BitVec.ofNat 64 (w / 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show w / 16 < 2 ^ 64 by omega)]

theorem sub_digit {v : Nat} (hv : v < 32) :
    (BitVec.ofNat 16 32).setWidth 64 - BitVec.ofNat 64 v = BitVec.ofNat 64 (32 - v) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

theorem wsetup_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc v : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : w < 2 ^ 30) (hv : v < 32)
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.block wsetup) s fun t =>
      (t.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2)) ∧
       t.gpr .x13 = BitVec.ofNat 64 (w / 16) ∧
       t.gpr .x17 = off P (slot w Crt.aT) ∧
       t.gpr .x5 = BitVec.ofNat 64 (32 - v) ∧ t.gpr .x7 = BitVec.allOnes 64 ∧
       t.gpr .x8 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x12,.x6,.x13,.x5,.x2,.x8,.x7,.x17] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [wsetup, hc.good.x0, hdr_enc (show sW < 32 by decide),
    hdr_enc (show Crt.sNib < 32 by decide), hdr_enc (sArr_lt (show Crt.aT < 8 by decide)),
    hc.ld (i := sW) (by decide), hc.ld (i := Crt.sNib) (by decide),
    hc.ld (i := sArr Crt.aT) (by decide), hc.good.hdr.hw, hN,
    hc.good.hdr.harr Crt.aT (by decide), ofNat_add_ofNat,
    shl3_ofNat (show 8 * (w + 2) < 2 ^ 64 by omega), shr4_width (show w < 2 ^ 64 by omega),
    sub_digit hv]

theorem wbody_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 16 ≤ w) (hw' : w < 2 ^ 30) (hv : v < 32)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.seq (.block wsetup) (.loop rawWide (.nonzero .x .x13))) s fun t =>
      ∃ s₀, s₀.mem = s.mem ∧ Keep mmRegs s s₀ ∧ WLoopInv s₀ P w mi X Xc v (w / 16) t := by
  apply WP.seq
  refine WP.mono (wsetup_ok hc hw' hv hN) fun u ⟨⟨h6,h13,h17,h5,h7,h8,hm⟩,ku⟩ => ?_
  have ctx : TableCtx u P w mi X Xc := hc.of_win
    (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have h0 : WLoopInv u P w mi X Xc v 0 u := ⟨ctx, by rw [hm]; exact ht,
    h6, by simpa using h17, h5, h7, h8, Outside.refl _ _ _ _,
    fun k hk => by omega, Keep.refl _ _⟩
  exact WP.mono (wblocks_ok hw hw' hv h0 h13) fun t hI =>
    ⟨u,hm,ku.mono (by decide),hI⟩

theorem wide_eq : VG.Impl.Rsa.AArch64.WindowSelectVector.wide 32 =
    .seq (.block wsetup) (.seq (.loop rawWide (.nonzero .x .x13)) (.block finish)) := rfl

theorem wide_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 16 ≤ w) (hw' : w < 2 ^ 30) (hd : w % 16 = 0)
    (hv : v < 32) (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hN : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowSelectVector.wide 32) s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hcount : 128 * (w / 16) = 8 * w := by omega
  have he : slot w 8 + 8 * (w + 2) * v = slot w (8 + v) := by
    simp only [slot, Nat.add_mul, Nat.mul_comm v, Nat.add_assoc]
  rw [wide_eq]
  apply WP.assoc
  apply WP.seq
  refine WP.mono (wbody_ok hc hw hw' hv ht hN) fun u ⟨s₀,hm₀,k₀,hI⟩ => ?_
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
