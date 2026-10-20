module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Impl.Bignum.AArch64
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! The size dispatch reads only the public width and preserves the header. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)

theorem shr3_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n/8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self n 8) hn)]

theorem guard_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : w < 2 ^ 64) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.guard) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x3 = BitVec.ofNat 64 (w/8)) ∧
      Keep [.x12, .x3] s t := by
  refine WP.keep [.x12, .x3] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.guard
  brun [h0, hs.ld (show 8*sW+8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega),
    hH.hw, shr3_ofNat hw]

structure GuardCtx (L : Ws) (s : State) : Prop where
  good : GoodW L s
  test : s.gpr .x3 = BitVec.ofNat 64 (L.w/8)

theorem guard_ctx (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.guard) s (GuardCtx L) := by
  have hw := goodW_width h
  obtain ⟨mi, hg, hz⟩ := h
  refine WP.mono (guard_ok hg.scr hg.x0 hg.hdr hz (by omega)) fun t ⟨⟨hm, _, h3⟩, k⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩, h3⟩

theorem guard_width {L : Ws} {s : State} (h : GuardCtx L s)
    (ht : isa.eval (.nonzero .x .x3) s = some true) : 8 ≤ L.w := by
  have hw := goodW_width h.good
  rw [eval_nonzero, h.test, ne_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show L.w/8 < 2 ^ 64 by omega)] at ht
  have hn := of_decide_eq_true (Option.some.inj ht)
  omega

theorem guarded_ct {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hu : MmUse o a a)
    {hs hf : VG.Taint.Hint VG.AArch64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) hs).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.Square.finishBases o)) hf).isSome = true) :
    RelCT isa (Two GoodW)
      (.seq (.block VG.Impl.Bignum.AArch64.Square.guard)
        (.ite (.nonzero .x .x3) (VG.Impl.Bignum.AArch64.Square.square o a) (Public.basicMm o a a)))
      (fun _ _ => True) := by
  refine RelCT.seq (two_piece [.x0] pins_goodW (by taint_decide) guard_ctx) ?_
  refine two_ite (Φ := GuardCtx) ?_ ?_ ?_
  · intro L s₁ s₂ h₁ h₂
    rw [eval_nonzero, h₁.test, eval_nonzero, h₂.test]
  · exact two_map id (fun L s h => ⟨h.1.good, guard_width h.1 h.2⟩)
      (square_ct ho ha ha1 ha2 hS hF)
  · exact two_map id (fun _ _ h => h.1.good) (Mont.basic.ct hu)

end VG.Proof.Bignum.AArch64.Square
