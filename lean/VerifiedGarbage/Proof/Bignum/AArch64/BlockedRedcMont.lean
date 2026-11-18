module

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Impl.Bignum.AArch64.Square

/-! ### `Bignum.AArch64.BlockedRedcGuard`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.SquareMont`, which this module and modules that import it used -/

section

/-! The optimized implementation satisfies the unchanged Montgomery interface. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)

theorem guarded_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block VG.Impl.Bignum.AArch64.Square.guard)
      (.ite (.nonzero .x .x3) (VG.Impl.Bignum.AArch64.Square.square o a) (Public.basicMm o a a))) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w*2 ^ (64*w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w*wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (guard_ok hg.scr hg.x0 hg.hdr hZ (by omega_using [hw]))
    fun u ⟨⟨hm, _, h3⟩, ku⟩ => ?_)
  have hgu : Good u B Z w minv :=
    ⟨hg.scr.congr ku.wr, (ku.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩
  have invu : ((word u.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0 := by rw [hm]; exact hinv
  have au : wv u.mem B (slot w a) w < wv u.mem B (slot w aN) w := by rw [hm]; exact hA
  have hdiv : w/8 < 2 ^ 64 := by omega_using [hw]
  by_cases hfast : 8 ≤ w
  · have hn : w/8 ≠ 0 := by omega_using [hfast]
    refine WP.ite true (by rw [eval_nonzero, h3, ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdiv, decide_eq_true hn]) (fun _ => ?_) (by simp)
    refine WP.mono (square_ok hgu.scr hgu.x0 hgu.hdr hZ hw1 hw ho ha ho1 ho2 ha1 ha2 invu au)
      fun t ⟨ht, hv, hf, kt⟩ => ?_
    rw [hm] at ht hv hf
    exact ⟨⟨hg.scr.congr (kt.wr.trans ku.wr), ((ku.trans kt).gpr .x0 (by decide)).trans hg.x0,
      hf.hdr hg.hdr⟩, ht, hv, hf, (ku.trans kt).mono (by decide)⟩
  · have hn : w/8 = 0 := by omega_using [hfast]
    refine WP.ite false (by rw [eval_nonzero, h3, hn]; rfl) (by simp) (fun _ => ?_)
    refine WP.mono (Mont.basic.mm_ok hgu hZ hw1 hw ho ha ha ho1 ho2 ha1 ha1 invu au ha2 ha2)
      fun t ⟨hg', ht, hv, hf, kt⟩ => ?_
    rw [hm] at ht hv hf
    exact ⟨hg', ht, hv, hf, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.Square

namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum

def Mont.square : Mont where
  mm := VG.Impl.Bignum.AArch64.Square.montMul
  ok := by
    intro s B Z w minv hg hz hw hw' o a b ho ha hb d1 d2 d3 d4 d5 d6 hinv hB
    by_cases heq : a = b
    · subst b
      simpa only [VG.Impl.Bignum.AArch64.Square.montMul, ite_eq_left rfl, ite_true] using
        (Square.guarded_ok hg hz hw hw' ho ha d1 d2 d3 d4 hinv hB)
    · simpa only [VG.Impl.Bignum.AArch64.Square.montMul, ite_eq_right heq, Mont.basic] using
        (Mont.basic.ok hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals
      unfold VG.Impl.Bignum.AArch64.Square.montMul
      first
      | rw [ite_eq_left rfl]
        exact Square.guarded_ct (by decide) (by decide) (by decide) (by decide)
          (by simp [MmUse]) (by taint_decide) (by taint_decide)
      | rw [ite_eq_right (by decide)]
        exact Mont.basic.ct (by simp [MmUse])

end VG.Proof.Bignum.AArch64

end

end

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
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n % 8 < 2 ^ 64 by omega_using [])]

theorem guard_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : w < 2 ^ 64) :
    WP isa (.block guard) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (w / 16) ∧
        t.gpr .x4 = BitVec.ofNat 64 (w % 8)) ∧ Keep [.x12, .x3, .x4] s t := by
  refine WP.keep [.x12, .x3, .x4] ?_ rfl rfl rfl
  brun [guard, h0, hs.ld (show 8 * sW + 8 ≤ Z by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hZ, this]), hH.hw, shr4_ofNat hw]
  exact mask7_ofNat hw

structure GuardCtx (L : Ws) (s : State) : Prop where
  good : GoodW L s
  width : s.gpr .x3 = BitVec.ofNat 64 (L.w / 16)
  rem : s.gpr .x4 = BitVec.ofNat 64 (L.w % 8)

theorem guard_ctx (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block guard) s (GuardCtx L) := by
  have hw := Square.goodW_width h
  obtain ⟨mi, hg, hz⟩ := h
  refine WP.mono (guard_ok hg.scr hg.x0 hg.hdr hz (by omega_using [hw])) fun t ⟨⟨hm, h3, h4⟩, kt⟩ => ?_
  exact ⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩, h3, h4⟩

theorem guard_width {L : Ws} {s : State} (h : GuardCtx L s)
    (ht : isa.eval (.nonzero .x .x3) s = some true) : 16 ≤ L.w := by
  have hw := Square.goodW_width h.good
  rw [eval_nonzero, h.width, ne_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show L.w / 16 < 2 ^ 64 by omega_using [hw])] at ht
  have hn := of_decide_eq_true (Option.some.inj ht)
  omega_using [hn]

theorem guard_rem {L : Ws} {s : State} (h : GuardCtx L s)
    (ht : isa.eval (.zero .x .x4) s = some true) : L.w % 8 = 0 := by
  rw [eval_zero, h.rem, eq_zero_iff, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show L.w % 8 < 2 ^ 64 by omega_using [])] at ht
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

end

end

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)

theorem guarded_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hoN : o ≠ aN) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block guard)
      (.ite (.nonzero .x .x3) (.ite (.zero .x .x4)
        (VG.Impl.Bignum.AArch64.BlockedRedc.square o a)
        (VG.Impl.Bignum.AArch64.Square.montMul o a a))
        (VG.Impl.Bignum.AArch64.Square.montMul o a a))) s fun t =>
      Good t B Z w minv ∧ wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (guard_ok hg.scr hg.x0 hg.hdr hZ (by omega_using [hw]))
    fun u ⟨⟨hm, h3, h4⟩, ku⟩ => ?_)
  have hgu : Good u B Z w minv :=
    ⟨hg.scr.congr ku.wr, (ku.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩
  have invu : ((word u.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hm]; exact hinv
  have au : wv u.mem B (slot w a) w < wv u.mem B (slot w aN) w := by rw [hm]; exact hA
  have hSlow := WP.mono (Mont.square.mm_ok hgu hZ hw1 hw ho ha ha ho1 ho2 ha1 ha1 invu au ha2 ha2)
    fun t ⟨hgt, ht, hv, hf, kt⟩ =>
      (show Good t B Z w minv ∧ wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
        wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
          wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
        Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t from by
        rw [hm] at ht hv hf
        exact ⟨hgt, ht, hv, hf, (ku.trans kt).mono (by decide)⟩)
  have hdiv : w / 16 < 2 ^ 64 := by omega_using [hw]
  have hrem : w % 8 < 2 ^ 64 := by omega_using []
  by_cases hfast : 16 ≤ w
  · refine WP.ite true (by rw [eval_nonzero, h3, ne_zero_iff, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdiv, decide_eq_true (show w / 16 ≠ 0 by omega_using [hfast])]) (fun _ => ?_) (by simp)
    by_cases hmod : w % 8 = 0
    · refine WP.ite true (by rw [eval_zero, h4, hmod]; rfl) (fun _ => ?_) (by simp)
      refine WP.mono (square_ok hgu.scr hgu.x0 hgu.hdr hZ hfast hw hmod
        ho ha ho1 ho2 hoN ha1 ha2 invu au) fun t ⟨ht, hv, hf, kt⟩ => ?_
      rw [hm] at ht hv hf
      exact ⟨⟨hg.scr.congr (kt.wr.trans ku.wr), ((ku.trans kt).gpr .x0 (by decide)).trans hg.x0,
        hf.hdr hg.hdr⟩, ht, hv, hf, (ku.trans kt).mono (by decide)⟩
    · exact WP.ite false (by rw [eval_zero, h4, eq_zero_iff, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hrem, decide_eq_false hmod]) (by simp) (fun _ => hSlow)
  · exact WP.ite false (by rw [eval_nonzero, h3, show w / 16 = 0 by omega_using [hfast]]; rfl)
      (by simp) (fun _ => hSlow)

end VG.Proof.Bignum.AArch64.BlockedRedc

namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum

def Mont.blocked : Mont where
  mm := VG.Impl.Bignum.AArch64.BlockedRedc.mm
  ok := by
    intro s B Z w minv hg hz hw hw' o a b ho ha hb d1 d2 d3 d4 d5 d6 hinv hB
    by_cases heq : a = b ∧ o ≠ aN
    · obtain ⟨rfl, hon⟩ := heq
      unfold VG.Impl.Bignum.AArch64.BlockedRedc.mm
      rw [ite_eq_left (show a = a ∧ o ≠ aN from ⟨rfl, hon⟩)]
      exact BlockedRedc.guarded_ok hg hz hw hw' ho hb d1 d2 hon d5 d6 hinv hB
    · simpa only [VG.Impl.Bignum.AArch64.BlockedRedc.mm, ite_eq_right heq, Mont.square] using
        (Mont.square.ok hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
  ct := by
    have slow (o a b : Nat) (h : MmUse o a b) :
        RelCT isa (Two GoodW) (VG.Impl.Bignum.AArch64.Square.montMul o a b) (fun _ _ => True) :=
      Mont.square.ct (o := o) (a := a) (b := b) h
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals
      unfold VG.Impl.Bignum.AArch64.BlockedRedc.mm
      first
      | rw [ite_eq_left (by decide)]
        exact BlockedRedc.guarded_ct (by decide) (by decide) (by decide) (by decide)
          (by simp [MmUse]) (by taint_decide) (by taint_decide) (by taint_decide)
      | rw [ite_eq_right (by decide)]
        exact slow _ _ _ (by simp [MmUse])

end VG.Proof.Bignum.AArch64
