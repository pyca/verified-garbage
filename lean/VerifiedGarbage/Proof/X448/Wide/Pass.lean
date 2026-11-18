module

public import VerifiedGarbage.Proof.X448.Wide.Column
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.X448.AArch64.Tail
public import VerifiedGarbage.Proof.X448.Wide.Limbs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
public import VerifiedGarbage.Proof.X448.Wide.Word
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.X448.Wide.Memory
public import VerifiedGarbage.Impl.X448.AArch64.Wide
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.X448.AArch64.Step
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `X448.Wide.TailStep`, which this module and modules that import it used -/

section

/-! ### `X448.Wide.CarryStep`, which this module and modules that import it used -/

section

/-! ### `X448.Wide.UnpackRegs`, which this module and modules that import it used -/

section

/-! Untrusted: split a wide digit into two normalized interface limbs. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem unpackRegs_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12]) s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x4).toNat % VG.Proof.X448.radix ∧
      (t.gpr .x5).toNat = (s.gpr .x4).toNat / VG.Proof.X448.radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, hs.mask, Option.some.injEq, exists_eq_left']
  refine ⟨and28 _, shr28 _, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide

end

end

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

end

end

/-! ### `X448.Wide.TailRegs`, which this module and modules that import it used -/

section

/-! Untrusted: a one-word carry step after wide reduction. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

theorem pair_low64 (lo hi : BitVec 64) (h : pair lo hi < 2 ^ 64) :
    hi.toNat = 0 ∧ lo.toNat = pair lo hi := by
  simp only [pair] at h ⊢
  omega_using [h]

theorem tailRegs_ok (s : State) (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : (s.gpr .x4).toNat + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := (s.gpr .x4).toNat + (s.gpr .x6).toNat
    WP isa (.block Impl.X448.AArch64.Tail.regs) s fun t =>
      (t.gpr .x4).toNat = v % radix ∧ (t.gpr .x6).toNat = v / radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x6] s t := by
  intro v
  have hv : (s.gpr .x4 + s.gpr .x6).toNat = v := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  have hd := low56 (s.gpr .x4 + s.gpr .x6) 0
  simp only [pair, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, hv] at hd
  have hc : ((s.gpr .x4 + s.gpr .x6) >>> 56).toNat = v / radix := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hv]
    rfl
  apply WP.of_runBlock
  simp only [Impl.X448.AArch64.Tail.regs, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, Size.bits, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, Nat.reduceLT, hm, Option.some.injEq, exists_eq_left']
  refine ⟨hd, hc, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide

end

end

/-! Untrusted: narrow carry steps whose input coefficient already fits in one word. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)
open VG.Proof.X448.AArch64

theorem loadLow_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8)
    (hb : coeff s.mem base TMP i < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 16 * i)]) s fun t =>
      (t.gpr .x4).toNat = coeff s.mem base TMP i ∧ t.mem = s.mem ∧ Keeps [.x4] s t := by
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega_using [hi]
  have al := hs.read (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega_using [hi])
  have low := (pair_low64 _ _ hb).2
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.load, hs.x3, al, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨low, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem storeLow_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8) :
    WP isa (.block [st .x4 (TMP + 16 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 16 * i)) (s.gpr .x4) ∧ Keeps [] s t := by
  have ae : (TMP + 16 * i) % 8 = 0 ∧ TMP + 16 * i < 32768 := by simp only [TMP]; omega_using [hi]
  have aw := hs.write (d := TMP + 16 * i) (n := 8) (by simp only [TMP]; omega_using [hi])
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, and_self, State.read, State.store, hs.x3, aw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, (fun _ _ => rfl), rfl, rfl⟩

theorem tailStep_ok {s : State} {base : Addr} (hs : Scr s base) {o i : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0) (hi : i < 8) (unpack : Bool)
    (hfalse : unpack = false → o = TMP)
    (hm : s.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1))
    (hb : coeff s.mem base TMP i + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := coeff s.mem base TMP i + (s.gpr .x6).toNat
    WP isa (.block (Impl.X448.AArch64.Tail.step o i unpack)) s fun t =>
      (t.gpr .x6).toNat = v / radix ∧ coeff t.mem base o i = encoded (v % radix) unpack ∧
      Outside base (o + 16 * i) 16 s.mem t.mem ∧ Keeps [.x4, .x5, .x6] s t := by
  intro v
  have hb' : coeff s.mem base TMP i < 2 ^ 64 := by omega_using [hb]
  have high := (pair_low64 _ _ hb').1
  rw [Impl.X448.AArch64.Tail.step, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadLow_ok hs hi hb') fun u ⟨uv, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  have u9 := (uk.1 .x9 (by decide)).trans hm
  have raw : (u.gpr .x4).toNat + (u.gpr .x6).toNat = v := by
    rw [uv, uk.1 .x6 (by decide)]
  refine WP.mono (tailRegs_ok u u9 (by rw [raw]; exact hb)) fun w ⟨w4, w6, wm, wk⟩ => ?_
  rw [raw] at w4 w6
  have ws := (hs.of_keeps uk (by decide)).of_keeps wk (by decide)
  have keep : Keeps [.x4, .x5, .x6] s w := (uk.mono (by decide)).trans (wk.mono (by decide))
  cases unpack with
  | false =>
    have e := hfalse rfl
    subst o
    rw [ite_eq_right (by decide)]
    refine WP.mono (storeLow_ok ws hi) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, keep.trans (tk.mono (by decide))⟩
    · rw [tk.1 .x6 (by decide)]; exact w6
    · rw [tm]
      have out := writeW_outside w.mem base (w.gpr .x4) (d := TMP + 16 * i) (by simp only [TMP]; omega_using [hi])
      have lo : word (w.mem.writeW (off base (TMP + 16 * i)) (w.gpr .x4)) base (TMP + 16 * i) = w.gpr .x4 :=
        Mem.readW_writeW_self64 _ _ _
      have eh := out.word (d := TMP + 16 * i + 8) (Or.inr (by omega_using [])) (by simp only [TMP]; omega_using [hi])
      change pair (word _ base (TMP + 16 * i)) (word _ base (TMP + 16 * i + 8)) = _
      rw [lo, eh, wm, um]
      simp only [pair, high, Nat.mul_zero, Nat.add_zero, encoded, Bool.false_eq_true, ite_false]
      exact w4
    · rw [tm, wm, um]
      exact (writeW_outside _ _ _ (by simp only [TMP]; omega_using [hi])).mono (by omega_using []) (by omega_using [])
  | true =>
    rw [ite_eq_left (by decide), show
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12, st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] =
      [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12] ++
        [st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)] from rfl, WP.block_append_iff]
    refine WP.mono (unpackRegs_ok ws) fun z ⟨z4, z5, zm, zk⟩ => ?_
    have zs := ws.of_keeps zk (by decide)
    refine WP.mono (storeAt_ok zs (k := i) (by omega_using [ho, hi]) ho8) fun t ⟨tm, tk⟩ => ?_
    refine ⟨?_, ?_, ?_, keep.trans ((zk.mono (by decide)).trans (tk.mono (by decide)))⟩
    · rw [tk.1 .x6 (by decide), zk.1 .x6 (by decide)]; exact w6
    · rw [tm, coeff_put _ base _ _ (by omega_using [ho, hi]) (by omega_using [ho, hi]), ite_eq_left rfl]
      simp only [pair, encoded, ite_true]
      rw [z4, z5, w4]
    · rw [tm, zm, wm, um]
      exact putCoeff_outside _ _ _ _ (by omega_using [ho, hi])

end VG.Proof.X448.Wide

end

end

/-! ### `X448.Wide.PassInit`, which this module and modules that import it used -/

section

/-! Untrusted: initialize the carry, zero register, and 56-bit mask. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem passInit_ok (s : State) :
    WP isa (.block passInit) s fun t =>
      t.gpr .x6 = 0 ∧ t.gpr .x11 = 0 ∧ t.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) ∧
      t.mem = s.mem ∧ Keeps colRegs s t := by
  apply WP.of_runBlock
  simp only [passInit, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceMul, Nat.reduceLT, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · decide
  · simp only [colRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.X448.Wide

end

end

/-! ### `X448.Wide.TailPass`, which the modules that import this one used -/

section

/-! ### `X448.Wide.TailBounds`, which this module and modules that import it used -/

section

/-! Untrusted: tighter carry bounds for coefficients after the first fold. -/

@[expose] public section

namespace VG.Proof.X448.Wide

theorem carry_small {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i < 2 ^ 63 + radix) :
    carry f n < 2 ^ 8 := by
  induction n with
  | zero => simp only [carry]; decide
  | succ n ih =>
    have hi := ih (fun i hi => h i (by omega_using [hi]))
    have hn := h n (by omega_using [])
    simp only [carry, radix]
    simp only [radix] at hn
    omega_using [hi, hn]

theorem folded_small {f : Nat → Nat} (h : ∀ i < 8, f i < 2 ^ 118) :
    ∀ i < 8, folded f i < 2 ^ 63 + radix := by
  have hc := carry_bound h
  intro i _
  have hd := digit_lt f i
  simp only [folded]
  split <;> omega_arith

end VG.Proof.X448.Wide

end

end

/-! Untrusted: in-place or disjoint wide carry propagation. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem tailPass_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0)
    (hsep : o = TMP ∨ o + 128 ≤ TMP ∨ TMP + 128 ≤ o) (unpack : Bool)
    (hfalse : unpack = false → o = TMP)
    {f : Nat → Nat} (hf : ∀ i < 8, coeff s.mem base TMP i = f i)
    (hb : ∀ i < 8, f i < 2 ^ 63 + radix) :
    WP isa (.block (Impl.X448.AArch64.Tail.pass o unpack)) s fun t =>
      (∀ i < 8, coeff t.mem base o i = encoded (digit f i) unpack) ∧
      (t.gpr .x6).toNat = carry f 8 ∧ Outside base o 128 s.mem t.mem ∧ Keeps colRegs s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, coeff t.mem base o i = encoded (digit f i) unpack) ∧
    (∀ i, k ≤ i → i < 8 → coeff t.mem base TMP i = f i) ∧
    (t.gpr .x6).toNat = carry f k ∧ t.gpr .x11 = 0 ∧
    t.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps colRegs s t
  have step : ∀ k t, k < 8 → inv k t → WP isa (.block (Impl.X448.AArch64.Tail.step o k unpack)) t (inv (k + 1)) := by
    intro k t hk ⟨tl, th, tc, tz, t9, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have te := th k (by omega_using []) hk
    have cap : coeff t.mem base TMP k + (t.gpr .x6).toNat < 2 ^ 64 := by
      rw [te, tc]
      have c := carry_small (n := k) (fun i hi => hb i (by omega_using [hk, hi]))
      have h := hb k hk
      simp only [radix] at h
      omega_using [c, h]
    refine WP.mono (tailStep_ok ts ho ho8 hk unpack hfalse t9 cap) fun u ⟨uc, uv, um, uk⟩ => ?_
    rw [te, tc] at uc uv
    refine ⟨?_, ?_, uc, (uk.1 _ (by decide)).trans tz, (uk.1 _ (by decide)).trans t9,
      tm.trans (um.mono (by omega_using []) (by omega_using [hk])), tk.trans (uk.mono (by decide))⟩
    · intro i hi
      by_cases h : i = k
      · subst i
        exact uv
      · have eq : coeff u.mem base o i = coeff t.mem base o i :=
          outside_coeff um (by omega_using [h]) (by omega_using [ho, hk, hi])
        rw [eq]
        exact tl i (by omega_using [hi, h])
    · intro i hi hi'
      have sep : TMP + 16 * i + 16 ≤ o + 16 * k ∨ o + 16 * k + 16 ≤ TMP + 16 * i := by
        rcases hsep with h | h | h <;> omega_arith
      have eq : coeff u.mem base TMP i = coeff t.mem base TMP i :=
        outside_coeff um sep (by simp only [TMP]; omega_using [hi'])
      rw [eq]
      exact th i (by omega_using [hi]) hi'
  rw [Impl.X448.AArch64.Tail.pass, WP.block_append_iff]
  refine WP.mono (passInit_ok s) fun u ⟨u6, uz, u9, um, uk⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) u ?_)
    fun t ⟨tl, _, tc, _, _, tm, tk⟩ => ⟨tl, tc, tm, tk⟩
  refine ⟨fun _ hi => by omega, ?_, ?_, uz, u9, ?_, uk⟩
  · intro i _ hi; rw [um]; exact hf i hi
  · rw [u6]; rfl
  · rw [um]; exact Outside.refl _ _ _ _

end VG.Proof.X448.Wide

end

end

/-! Untrusted: in-place or disjoint wide carry propagation. -/

@[expose] public section

namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

theorem pass_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : o + 128 ≤ 8192) (ho8 : o % 8 = 0)
    (hsep : o = TMP ∨ o + 128 ≤ TMP ∨ TMP + 128 ≤ o) (unpack : Bool)
    {f : Nat → Nat} (hf : ∀ i < 8, coeff s.mem base TMP i = f i)
    (hb : ∀ i < 8, f i < 2 ^ 118) :
    WP isa (.block (pass o unpack)) s fun t =>
      (∀ i < 8, coeff t.mem base o i = encoded (digit f i) unpack) ∧
      (t.gpr .x6).toNat = carry f 8 ∧ Outside base o 128 s.mem t.mem ∧ Keeps colRegs s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, coeff t.mem base o i = encoded (digit f i) unpack) ∧
    (∀ i, k ≤ i → i < 8 → coeff t.mem base TMP i = f i) ∧
    (t.gpr .x6).toNat = carry f k ∧ t.gpr .x11 = 0 ∧
    t.gpr .x9 = BitVec.ofNat 64 (2 ^ 56 - 1) ∧
    Outside base o 128 s.mem t.mem ∧ Keeps colRegs s t
  have step : ∀ k t, k < 8 → inv k t → WP isa (.block (carryStep o k unpack)) t (inv (k + 1)) := by
    intro k t hk ⟨tl, th, tc, tz, t9, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have te := th k (by omega_using []) hk
    have cap : coeff t.mem base TMP k + (t.gpr .x6).toNat < 2 ^ 119 := by
      rw [te, tc]
      have c := carry_bound (n := k) (fun i hi => hb i (by omega_using [hk, hi]))
      have h := hb k hk
      omega_using [tc, h]
    refine WP.mono (carryStep_ok ts ho ho8 hk unpack tz t9 cap) fun u ⟨uc, uv, um, uk⟩ => ?_
    rw [te, tc] at uc uv
    refine ⟨?_, ?_, uc, (uk.1 _ (by decide)).trans tz, (uk.1 _ (by decide)).trans t9,
      tm.trans (um.mono (by omega_using []) (by omega_using [hk])), tk.trans (uk.mono (by decide))⟩
    · intro i hi
      by_cases h : i = k
      · subst i
        exact uv
      · have eq : coeff u.mem base o i = coeff t.mem base o i :=
          outside_coeff um (by omega_using [h]) (by omega_using [ho, hk, hi])
        rw [eq]
        exact tl i (by omega_using [hi, h])
    · intro i hi hi'
      have sep : TMP + 16 * i + 16 ≤ o + 16 * k ∨ o + 16 * k + 16 ≤ TMP + 16 * i := by
        rcases hsep with h | h | h <;> omega_arith
      have eq : coeff u.mem base TMP i = coeff t.mem base TMP i :=
        outside_coeff um sep (by simp only [TMP]; omega_using [hi'])
      rw [eq]
      exact th i (by omega_using [hi]) hi'
  rw [pass, WP.block_append_iff]
  refine WP.mono (passInit_ok s) fun u ⟨u6, uz, u9, um, uk⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) u ?_)
    fun t ⟨tl, _, tc, _, _, tm, tk⟩ => ⟨tl, tc, tm, tk⟩
  refine ⟨fun _ hi => by omega, ?_, ?_, uz, u9, ?_, uk⟩
  · intro i _ hi; rw [um]; exact hf i hi
  · rw [u6]; rfl
  · rw [um]; exact Outside.refl _ _ _ _

end VG.Proof.X448.Wide
