module
public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
import VerifiedGarbage.Proof.Bignum.AArch64.SquareMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)

def guard : List Instr := [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7,
  .logic .and .x .x4 .x12 .x4]

theorem shr4_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self n 16) hn)]

theorem mask7_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& (7 : BitVec 64) = BitVec.ofNat 64 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n % 8 < 2 ^ 64 by omega)]

theorem guard_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : w < 2 ^ 64) :
    WP isa (.block guard) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (w / 16) ∧
        t.gpr .x4 = BitVec.ofNat 64 (w % 8)) ∧ Keep [.x12, .x3, .x4] s t := by
  refine WP.keep [.x12, .x3, .x4] ?_ rfl rfl rfl
  brun [guard, h0, hs.ld (show 8 * sW + 8 ≤ Z by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega), hH.hw, shr4_ofNat hw]
  exact mask7_ofNat hw

structure GuardCtx (L : Ws) (s : State) : Prop where
  good : GoodW L s
  width : s.gpr .x3 = BitVec.ofNat 64 (L.w / 16)
  rem : s.gpr .x4 = BitVec.ofNat 64 (L.w % 8)

theorem guard_ctx (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block guard) s (GuardCtx L) := by
  have hw := Square.goodW_width h
  obtain ⟨mi, hg, hz⟩ := h
  refine WP.mono (guard_ok hg.scr hg.x0 hg.hdr hz (by omega)) fun t ⟨⟨hm, h3, h4⟩, kt⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩, h3, h4⟩

theorem guard_width {L : Ws} {s : State} (h : GuardCtx L s)
    (ht : isa.eval (.nonzero .x .x3) s = some true) : 16 ≤ L.w := by
  have hw := Square.goodW_width h.good
  rw [eval_nonzero, h.width, ne_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show L.w / 16 < 2 ^ 64 by omega)] at ht
  have hn := of_decide_eq_true (Option.some.inj ht)
  omega

theorem guard_rem {L : Ws} {s : State} (h : GuardCtx L s)
    (ht : isa.eval (.zero .x .x4) s = some true) : L.w % 8 = 0 := by
  rw [eval_zero, h.rem, eq_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show L.w % 8 < 2 ^ 64 by omega)] at ht
  exact of_decide_eq_true (Option.some.inj ht)

theorem guarded_ct {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hu : MmUse o a a)
    {hs hf hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) hs).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.finishBases o)) hf).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr o)]) hh).isSome = true) :
    RelCT isa (Two GoodW) (.seq (.block guard)
      (.ite (.nonzero .x .x3) (.ite (.zero .x .x4)
        (VG.Impl.Bignum.AArch64.BlockedRedc.square o a)
        (VG.Impl.Bignum.AArch64.Square.montMul o a a))
        (VG.Impl.Bignum.AArch64.Square.montMul o a a))) (fun _ _ => True) := by
  refine RelCT.seq (two_piece _ pins_goodW (by taint_decide) guard_ctx) ?_
  refine two_ite (Φ := GuardCtx) ?_ ?_ ?_
  · intro L s t hs ht
    rw [eval_nonzero, eval_nonzero, hs.width, ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro L s t hs ht
      rw [eval_zero, eval_zero, hs.1.rem, ht.1.rem]
    · exact two_map id (fun _ _ h => ⟨h.1.1.good, guard_width h.1.1 h.1.2,
        guard_rem h.1.1 h.2⟩) (square_ct ho ha ha1 ha2 hS hF hH)
    · exact two_map id (fun _ _ h => h.1.1.good) (Mont.square.ct hu)
  · exact two_map id (fun _ _ h => h.1.good) (Mont.square.ct hu)

end VG.Proof.Bignum.AArch64.BlockedRedc
