module

import VerifiedGarbage.Proof.X448.Wide.UnpackRegs
public import VerifiedGarbage.Proof.X448.Wide.Memory
public import VerifiedGarbage.Impl.X448.AArch64.Wide
import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.X448.Wide.Word
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `X448.Wide.CarryRegs`, which this module and modules that import it used -/

section

/-! Untrusted: extracting a radix-2⁵⁶ digit and one-word carry. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64 (read_x)

theorem carryRegs_ok (s : State) (hz : s.gpr .x11 = 0)
    (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : pair (s.gpr .x4) (s.gpr .x5) + (s.gpr .x6).toNat < 2 ^ 119) :
    let v := pair (s.gpr .x4) (s.gpr .x5) + (s.gpr .x6).toNat
    WP isa (.block carryRegs) s fun t =>
      (t.gpr .x4).toNat = v % radix ∧ (t.gpr .x6).toNat = v / radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  let lo := addCarry (s.gpr .x4) (s.gpr .x6) false
  let hi := addCarry (s.gpr .x5) 0 (carryOut (s.gpr .x4) (s.gpr .x6) false)
  have hv : pair lo hi = v := add128 _ _ _ (Nat.lt_trans hb (by decide))
  have hd := low56 lo hi
  have hc := high56 lo hi (by rw [hv]; exact hb)
  rw [hv] at hd hc
  apply WP.of_runBlock
  simp only [carryRegs, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, hm,
    show 56 < Size.x.bits from by decide, show 8 < Size.x.bits from by decide,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · dsimp only [lo, hi, addCarry, carryOut, Size.bits] at hd ⊢
    exact hd
  · dsimp only [lo, hi, addCarry, carryOut, Size.bits] at hc ⊢
    exact hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

end VG.Proof.X448.Wide

end

end

/-! Untrusted: one wide carry step and its optional interface conversion. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

def encoded (v : Nat) (unpack : Bool) : Nat :=
  if unpack then v % VG.Proof.X448.radix + 2 ^ 64 * (v / VG.Proof.X448.radix) else v

theorem carryStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0) (hi : i < 8) (unpack : Bool)
    (hz : s.gpr .x11 = 0) (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : coeff s.mem base TMP i + (s.gpr .x6).toNat < 2 ^ 119) :
    let v := coeff s.mem base TMP i + (s.gpr .x6).toNat
    WP isa (.block (carryStep o i unpack)) s fun t =>
      (t.gpr .x6).toNat = v / radix ∧ coeff t.mem base o i = encoded (v % radix) unpack ∧
      Outside base (o + 16 * i) 16 s.mem t.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  rw [carryStep, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadAt_ok hs (o := TMP) (k := i) (by simp only [TMP]; omega_using [hi]) (by decide))
    fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uz : u.gpr .x11 = 0 := (uk.1 _ (by decide)).trans hz
  have u9 : u.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) := (uk.1 _ (by decide)).trans hm
  have raw : pair (u.gpr .x4) (u.gpr .x5) + (u.gpr .x6).toNat = v := by
    rw [uv, uk.1 .x6 (by decide)]
  refine WP.mono (carryRegs_ok u uz u9 (by rw [raw]; exact hb)) fun w ⟨w4, w6, wm, wk⟩ => ?_
  rw [raw] at w4 w6
  have ws := (hs.of_keeps uk (by decide)).of_keeps wk (by decide)
  have wkeep : Keeps [.x4, .x5, .x6] s w := (uk.mono (by decide)).trans (wk.mono (by decide))
  cases unpack with
  | false =>
    rw [ite_eq_right (by decide)]
    refine WP.mono (storeAt_ok ws (k := i) (by omega_using [ho, hi]) ho8 .x4 .x11) fun t ⟨tm, tk⟩ => ?_
    have wz : w.gpr .x11 = 0 := (wk.1 _ (by decide)).trans uz
    refine ⟨?_, ?_, ?_, wkeep.trans (tk.mono (by decide))⟩
    · rw [tk.1 .x6 (by decide)]; exact w6
    · rw [tm, coeff_put _ base _ _ (by omega_using [ho, hi]) (by omega_using [ho, hi]), ite_eq_left rfl, wz]
      simp only [pair, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
        encoded, Bool.false_eq_true, ite_false]
      exact w4
    · rw [tm, wm, um]
      exact putCoeff_outside _ _ _ _ (by omega_using [ho, hi])
  | true =>
    rw [ite_eq_left (by decide), show
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12, st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] =
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12] ++
        [st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] from rfl, WP.block_append_iff]
    refine WP.mono (unpackRegs_ok ws) fun z ⟨z4, z5, zm, zk⟩ => ?_
    have zs := ws.of_keeps zk (by decide)
    refine WP.mono (storeAt_ok zs (k := i) (by omega_using [ho, hi]) ho8) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, wkeep.trans ((zk.mono (by decide)).trans (tk.mono (by decide)))⟩
    · rw [tk.1 .x6 (by decide), zk.1 .x6 (by decide)]; exact w6
    · rw [tm, coeff_put _ base _ _ (by omega_using [ho, hi]) (by omega_using [ho, hi]), ite_eq_left rfl]
      simp only [pair, encoded, ite_true]
      rw [z4, z5, w4]
    · rw [tm, zm, wm, um]
      exact putCoeff_outside _ _ _ _ (by omega_using [ho, hi])

end VG.Proof.X448.Wide
