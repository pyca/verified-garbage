import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import Mathlib.Tactic.Ring
import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Impl.Ed25519.AArch64.Recover
import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.CombDigit`. -/
section

/-!
# The comb's digits, signs and masks

Step `j` reads the nibbles `2j + 1` and `2j` of the scalar from its bits,
expanded one per byte at byte 768 of the workspace, by Horner's rule;
`combSign` turns each into the magnitude `|n - 8|` and the mask of its sign;
`combMasks` sets the register for `k` to all ones exactly if the magnitude is
`k`, for `k = 1 … 8`, and another to `1` exactly if it is `0`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64

/-! ## The bit index -/

private theorem index_fact : ∀ j < 32, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

theorem combIndex_ok (s : State) {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 32)
    (hb : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block ([.lsl .x .x8 .x19 3, .add .x .x8 .x0 .x8] : List Instr)) s fun t =>
      t.gpr .x8 = off base (8 * j) ∧ Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (3 : Nat) < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    hb, index_fact j hj, hs.x0, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## The nibble -/

private theorem bit_ext : ∀ b < 2, ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 = BitVec.ofNat 64 b := by
  decide

theorem combNibble_ok {s : State} {base : Addr} (hs : Scr s base) {S i p o : Nat} (hi : i < 64)
    (hp : s.gpr .x8 = off base p) (hpo : p + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block (combNibble o)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (nib S i) ∧ Keeps [.x2, .x3] s t := by
  have _hcap : workSize true = 8192 := rfl
  have hr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + j))) 1 := fun j hj =>
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : ∀ j, off base p + BitVec.ofNat 64 (o + j) = off base (768 + (4 * i + j)) :=
    fun j => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (off base) (by omega)
  have hv : ∀ j < 4, ((s.mem (off base (768 + (4 * i + j)))).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 ((S / 2 ^ (4 * i + j)) % 2) := fun j hj => by
    rw [hb _ (by omega)]; exact bit_ext _ (Nat.mod_lt _ (by decide))
  have e0 := he 0
  have e1 := he 1
  have e2 := he 2
  have e3 := he 3
  simp only [Nat.add_zero] at e0
  have v0 := hv 0 (by decide)
  have v1 := hv 1 (by decide)
  have v2 := hv 2 (by decide)
  have v3 := hv 3 (by decide)
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  simp only [Nat.add_zero] at v0 r0
  apply WP.of_runBlock
  simp only [combNibble, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, Nat.mod_one,
    show o + 3 < 4096 * 1 by omega, show o + 2 < 4096 * 1 by omega, show o + 1 < 4096 * 1 by omega,
    show o < 4096 * 1 by omega,
    Nat.reduceMul, and_self, hp, e0, e1, e2, e3,
    r0, r1, r2, r3, read_byte, v0, v1, v2, v3,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [nib_bits]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## Sign and magnitude -/

private theorem sign_fact : ∀ n < 16,
    ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) ^^^
        (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63)) -
      (((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63) =
      BitVec.ofNat 64 (mag n) ∧
    ((0 : BitVec 16).setWidth 32).setWidth 64 - (BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63 =
      mask (decide (n < 8)) := by
  decide +kernel

theorem combSign_ok (s : State) {n : Nat} (hn : n < 16) (hx : s.gpr .x2 = BitVec.ofNat 64 n) :
    WP isa (.block combSign) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (mag n) ∧ t.gpr .x1 = mask (decide (n < 8)) ∧
      Keeps [.x1, .x2, .x3, .x9] s t := by
  apply WP.of_runBlock
  simp only [combSign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (8 : Nat) < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    show 16 * 0 < 32 from by decide, Nat.mul_zero, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(sign_fact n hn).1, (sign_fact n hn).2, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-! ## The masks -/

/-- The bit of `|d| = 0`. -/
def zeroBit (a : Nat) : BitVec 64 := if a = 0 then 1 else 0

private theorem less_fact : ∀ a < 9, ∀ k < 8,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 (k + 1)) >>> 63 -
      (BitVec.ofNat 64 a - BitVec.ofNat 64 (k + 2)) >>> 63 = mask (decide (a = k + 1)) := by
  decide +kernel

private theorem last_fact : ∀ a < 9,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 8) >>> 63 - BitVec.ofNat 64 1 = mask (decide (a = 8)) ∧
    (BitVec.ofNat 64 a - BitVec.ofNat 64 1) >>> 63 = zeroBit a := by
  decide +kernel

theorem masksOdd_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block (combMasks oddRegs .x22)) s fun t =>
      (∀ k, 1 ≤ k → k ≤ 8 → t.gpr (oddReg k) = mask (decide (a = k))) ∧ t.gpr .x22 = zeroBit a ∧
      Keeps [.x22, .x12, .x13, .x14, .x15, .x16, .x17, .x20, .x21] s t := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [combMasks, oddRegs, oddReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk1 hk8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem masksEven_ok (s : State) {a : Nat} (ha : a < 9) (hx : s.gpr .x2 = BitVec.ofNat 64 a) :
    WP isa (.block (combMasks evenRegs .x8)) s fun t =>
      (∀ k, 1 ≤ k → k ≤ 8 → t.gpr (evenReg k) = mask (decide (a = k))) ∧ t.gpr .x8 = zeroBit a ∧
      Keeps [.x8, .x1, .x3, .x6, .x7, .x10, .x11, .x23, .x24] s t := by
  have l := less_fact a ha
  apply WP.of_runBlock
  simp only [combMasks, evenRegs, evenReg, List.range, List.range.loop,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceLT, ↓reduceIte,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (63 : Nat) < 64 from by decide, show ∀ k < 9, k < 4096 from fun k hk => by omega,
    RegUpd.gpr_write, BitVec.setWidth_eq, hx, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk1 hk8 => ?_, (last_fact a ha).2, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, ite_true, ite_false,
        reduceCtorEq] <;>
      first
      | exact (last_fact a ha).1
      | exact l _ (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

/-! ## Both digits -/

/-- What `combDigits` leaves for step `j`'s two digits. -/
structure DigitsOut (s : State) (S j : Nat) (t : State) : Prop where
  oddMask : ∀ k, 1 ≤ k → k ≤ 8 → t.gpr (oddReg k) = mask (decide (mag (nib S (2 * j + 1)) = k))
  oddZero : t.gpr .x22 = zeroBit (mag (nib S (2 * j + 1)))
  evenMask : ∀ k, 1 ≤ k → k ≤ 8 → t.gpr (evenReg k) = mask (decide (mag (nib S (2 * j)) = k))
  evenZero : t.gpr .x8 = zeroBit (mag (nib S (2 * j)))
  keeps : Keeps (clob ++ [.x1]) s t

theorem combDigits_ok {s : State} {base : Addr} (hs : Scr s base) {S j : Nat} (hj : j < 32)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block combDigits) s (DigitsOut s S j) := by
  have no : nib S (2 * j + 1) < 16 := nib_lt _ _
  have ne : nib S (2 * j) < 16 := nib_lt _ _
  simp only [combDigits, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combIndex_ok s hs hj hc) fun a ⟨a8, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (combNibble_ok hsa (S := S) (i := 2 * j + 1) (by omega) a8 (by omega) (by decide)
    (by rw [ka.mem]; exact hb)) fun b ⟨b2, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (combSign_ok b no b2) fun c ⟨c2, _, kc⟩ => ?_
  have hsc := (hsa.of_keeps kb (by decide)).of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (masksOdd_ok _ (mag_lt no) c2) fun e ⟨em, ez, ke⟩ => ?_
  have e8 : e.gpr .x8 = off base (8 * j) := by
    rw [ke.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), a8]
  have hse : Scr e base := hsc.of_keeps ke (by decide)
  have hbe : ∀ q < 256, e.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) := fun q hq => by
    rw [ke.mem, kc.mem, kb.mem, ka.mem]; exact hb q hq
  rw [WP.block_append_iff]
  refine WP.mono (combNibble_ok hse (S := S) (i := 2 * j) (by omega) e8 (by omega) (by decide) hbe)
    fun f ⟨f2, kf⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (combSign_ok f ne f2) fun g ⟨g2, _, kg⟩ => ?_
  refine WP.mono (masksEven_ok _ (mag_lt ne) g2) fun t ⟨tm, tz, kt⟩ => ?_
  refine ⟨fun k h1 h8 => ?_, ?_, tm, tz, ?_⟩
  · have hk : ∀ k < 9, oddReg k ∉ [Reg.x8, .x1, .x3, .x6, .x7, .x10, .x11, .x23, .x24] ∧
        oddReg k ∉ [Reg.x1, .x2, .x3, .x9] ∧ oddReg k ∉ [Reg.x2, .x3] := by
      decide
    obtain ⟨ht, hg, hf⟩ := hk k (by omega)
    rw [kt.gpr _ ht, kg.gpr _ hg, kf.gpr _ hf]
    exact em k h1 h8
  · rw [kt.gpr _ (by decide), kg.gpr _ (by decide), kf.gpr _ (by decide)]
    exact ez
  · have K : Keeps (clob ++ [.x1]) s t := ((((((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans
      (ke.mono (by decide))).trans (kf.mono (by decide))).trans (kg.mono (by decide))).trans
      (kt.mono (by decide))
    exact K

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect`. -/
section

/-!
# The comb's constant-time selection, for two digits at once

With `oddReg k` (`evenReg k`) all ones exactly for `k` the odd (even) digit's
magnitude, and `x22` (`x8`) the bit of a zero magnitude, `selectWord` builds
every candidate's word once, ANDs it with both digits' masks and ORs it into
`x4` and `x5`, so only each digit's candidate survives, and stores them.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 VG.Proof.X25519
open Word64

private theorem odd_regs : ∀ k < 9, oddReg k ∉ [Reg.x9, .x2, .x4, .x5] := by decide
private theorem even_regs : ∀ k < 9, evenReg k ∉ [Reg.x9, .x2, .x4, .x5] := by decide

private theorem ne_of_not_mem {r : Reg} {rs : List Reg} (h : r ∉ rs) {r' : Reg} (hr : r' ∈ rs) :
    r ≠ r' := fun e => h (e ▸ hr)

theorem selectCand_ok (s : State) (v : Spec.X25519.Fe) {k : Nat} (hk : k < 9) (w : Nat) :
    WP isa (.block (selectCand v k w)) s fun t =>
      t.gpr .x4 = s.gpr .x4 ||| (feWord v w &&& s.gpr (oddReg k)) ∧
      t.gpr .x5 = s.gpr .x5 ||| (feWord v w &&& s.gpr (evenReg k)) ∧
      Keeps [.x9, .x2, .x4, .x5] s t := by
  have ho := odd_regs k hk
  have he := even_regs k hk
  have ho9 := ne_of_not_mem ho (r' := .x9) (by decide)
  have he9 := ne_of_not_mem he (r' := .x9) (by decide)
  have he2 := ne_of_not_mem he (r' := .x2) (by decide)
  have he4 := ne_of_not_mem he (r' := .x4) (by decide)
  rw [selectCand, WP.block_append_iff]
  refine WP.mono (const64_ok s .x9 (feWord v w)) fun a ⟨a9, ka⟩ => ?_
  have am : a.gpr (oddReg k) = s.gpr (oddReg k) := ka.gpr _ (by simpa using ho9)
  have ae : a.gpr (evenReg k) = s.gpr (evenReg k) := ka.gpr _ (by simpa using he9)
  have a4 : a.gpr .x4 = s.gpr .x4 := ka.gpr _ (by decide)
  have a5 : a.gpr .x5 = s.gpr .x5 := ka.gpr _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, he2, he4, ite_true, ite_false, reduceCtorEq, a9, am, ae, a4, a5,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  exact ka.gpr _ (by simpa using hr.1)

/-- The words of `vs[a]` after the candidates `k ≤ n`, zero if `a > n`. -/
def selWord (vs : List Spec.X25519.Fe) (a n w : Nat) : BitVec 64 :=
  if a ≤ n then feWord (vs.getD a 0) w else 0

private theorem or_and_zero (x y : BitVec 64) : x ||| (y &&& 0) = x := by ext i; simp

theorem sel_step (vs : List Spec.X25519.Fe) (a n w : Nat) :
    selWord vs a n w ||| (feWord (vs.getD (n + 1) 0) w &&& mask (decide (a = n + 1))) =
      selWord vs a (n + 1) w := by
  unfold selWord
  by_cases h : a ≤ n
  · simp only [h, ↓reduceIte, show a ≤ n + 1 by omega, show ¬ a = n + 1 by omega, decide_false,
      mask, Bool.false_eq_true]
    exact or_and_zero _ _
  · by_cases he : a = n + 1
    · subst he
      simp only [h, ↓reduceIte, Nat.le_refl, decide_true, mask, BitVec.and_allOnes]
      exact BitVec.zero_or
    · simp only [h, he, ↓reduceIte, show ¬ a ≤ n + 1 by omega, decide_false, mask,
        Bool.false_eq_true]
      exact or_and_zero _ _

/-- The masks of both digits, for the magnitudes `ao` and `ae`. -/
def Masks (ao ae : Nat) (s : State) : Prop :=
  (∀ k, 1 ≤ k → k ≤ 8 → s.gpr (oddReg k) = mask (decide (ao = k))) ∧
  (∀ k, 1 ≤ k → k ≤ 8 → s.gpr (evenReg k) = mask (decide (ae = k))) ∧
  s.gpr .x22 = zeroBit ao ∧ s.gpr .x8 = zeroBit ae

theorem Masks.of_keeps {ao ae : Nat} {s t : State} (h : Masks ao ae s)
    (k : Keeps [.x9, .x2, .x4, .x5] s t) : Masks ao ae t := by
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, by rw [k.gpr _ (by decide)]; exact h.2.2.1,
    by rw [k.gpr _ (by decide)]; exact h.2.2.2⟩
  · rw [k.gpr _ (odd_regs j (by omega))]; exact h.1 j h1 h8
  · rw [k.gpr _ (even_regs j (by omega))]; exact h.2.1 j h1 h8

theorem selectCands_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s)
    (vs : List Spec.X25519.Fe) (w n : Nat) (hn : n ≤ 8)
    (h0 : s.gpr .x4 = selWord vs ao 0 w ∧ s.gpr .x5 = selWord vs ae 0 w) :
    WP isa (.block ((List.range n).flatMap fun k => selectCand (vs.getD (k + 1) 0) (k + 1) w)) s
      fun t => t.gpr .x4 = selWord vs ao n w ∧ t.gpr .x5 = selWord vs ae n w ∧
        Keeps [.x9, .x2, .x4, .x5] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨h0.1, h0.2, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t4, t5, kt⟩ => ?_
    have tm := hm.of_keeps kt
    refine WP.mono (selectCand_ok t _ (by omega : n + 1 < 9) w) fun u ⟨u4, u5, ku⟩ =>
      ⟨?_, ?_, kt.trans ku⟩
    · rw [u4, t4, tm.1 (n + 1) (by omega) (by omega), sel_step]
    · rw [u5, t5, tm.2.1 (n + 1) (by omega) (by omega), sel_step]

private theorem movz0 : (((0 : BitVec 16).setWidth 32).setWidth 64) = 0 := by decide

theorem selectStart_ok (s : State) {ao ae : Nat} (hm : Masks ao ae s) (one : Bool)
    (vs : List Spec.X25519.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0) (w : Nat) (hw : w < 4) :
    WP isa (.block (selectStart one w)) s fun t =>
      t.gpr .x4 = selWord vs ao 0 w ∧ t.gpr .x5 = selWord vs ae 0 w ∧
        Keeps [.x9, .x2, .x4, .x5] s t := by
  have hz : ∀ a, (if (one && w == 0) = true then zeroBit a else 0) = selWord vs a 0 w := fun a => by
    unfold selWord zeroBit
    by_cases ha : a = 0
    · subst ha
      have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
      simp only [Nat.le_refl, ↓reduceIte, h0]
      cases one <;> rcases this with rfl | rfl | rfl | rfl <;> decide
    · simp [ha, show ¬ a ≤ 0 by omega]
  rw [← hz ao, ← hz ae]
  unfold selectStart
  by_cases h : (one && w == 0) = true
  · simp only [h, ↓reduceIte]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide),
      read_x, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_true, ite_false, reduceCtorEq,
      hm.2.2.1, hm.2.2.2, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.1, hr.2.2.2, ite_false]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, RegUpd.gpr_write, ite_false, reduceCtorEq,
      Nat.mul_zero, BitVec.shiftLeft_zero, movz0, Option.some.injEq, exists_eq_left']
    refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.2.1, hr.2.2.2, ite_false]

/-- `m'` agrees with `m` but on the `n` bytes at offsets `o` and `e` of `base`. -/
def Frame2 (base : Addr) (o e n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + n ≤ ofs base x) → (ofs base x < e ∨ e + n ≤ ofs base x) → m' x = m x

theorem Frame2.trans {base : Addr} {o e n : Nat} {m₁ m₂ m₃ : Mem} (h : Frame2 base o e n m₁ m₂)
    (k : Frame2 base o e n m₂ m₃) : Frame2 base o e n m₁ m₃ :=
  fun x h1 h2 => (k x h1 h2).trans (h x h1 h2)

theorem Frame2.mono {base : Addr} {o e n o' e' n' : Nat} {m m' : Mem} (h : Frame2 base o e n m m')
    (h1 : o' ≤ o) (h2 : o + n ≤ o' + n') (h3 : e' ≤ e) (h4 : e + n ≤ e' + n') :
    Frame2 base o' e' n' m m' := fun x a b => h x (by omega) (by omega)

theorem Frame2.word {base : Addr} {o e n : Nat} {m m' : Mem} (h : Frame2 base o e n m m') {d : Nat}
    (h1 : d + 8 ≤ o ∨ o + n ≤ d) (h2 : d + 8 ≤ e ∨ e + n ≤ d) (hd : d + 8 < 2 ^ 64) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Frame2.F {base : Addr} {o e n : Nat} {m m' : Mem} (h : Frame2 base o e n m m') {d : Nat}
    (h1 : d + 32 ≤ o ∨ o + n ≤ d) (h2 : d + 32 ≤ e ∨ e + n ≤ d) (hd : d + 32 < 2 ^ 64) :
    F m' base d = F m base d := by
  change toFe (AArch64.fe m' base d) = toFe (AArch64.fe m base d)
  unfold AArch64.fe
  rw [h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega),
    h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega)]

/-- What a selection leaves of the registers. -/
def RegsKept (s t : State) : Prop :=
  (∀ r, r ∉ [Reg.x9, .x2, .x4, .x5] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem RegsKept.trans {s t u : State} (h : RegsKept s t) (k : RegsKept t u) : RegsKept s u :=
  ⟨fun r hr => (k.1 r hr).trans (h.1 r hr), k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.trans h.2.2.2⟩

theorem RegsKept.of_keeps {s t : State} (k : Keeps [.x9, .x2, .x4, .x5] s t) : RegsKept s t :=
  ⟨k.gpr, k.rd, k.wr, k.sp⟩

theorem Masks.of_kept {ao ae : Nat} {s t : State} (h : Masks ao ae s) (k : RegsKept s t) :
    Masks ao ae t := by
  refine ⟨fun j h1 h8 => ?_, fun j h1 h8 => ?_, by rw [k.1 _ (by decide)]; exact h.2.2.1,
    by rw [k.1 _ (by decide)]; exact h.2.2.2⟩
  · rw [k.1 _ (odd_regs j (by omega))]; exact h.1 j h1 h8
  · rw [k.1 _ (even_regs j (by omega))]; exact h.2.1 j h1 h8

theorem selectWord_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hm : Masks ao ae s)
    (one : Bool) (vs : List Spec.X25519.Fe) (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) (w : Nat) (hw : w < 4) :
    WP isa (.block (selectWord one vs o e w)) s fun t =>
      t.mem = (s.mem.writeW (off base (o + 8 * w)) (selWord vs ao 8 w)).writeW (off base (e + 8 * w))
        (selWord vs ae 8 w) ∧ RegsKept s t := by
  have _hcap : workSize true = 8192 := rfl
  rw [selectWord, List.append_assoc, WP.block_append_iff]
  refine WP.mono (selectStart_ok s hm one vs h0 w hw) fun a ⟨a4, a5, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectCands_ok a (hm.of_keeps ka) vs w 8 (le_refl _) ⟨a4, a5⟩)
    fun b ⟨b4, b5, kb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    store_sc hsb (show (o + 8 * w) % 8 = 0 by omega) (by omega),
    store_sc (hsb.setMem _) (show (e + 8 * w) % 8 = 0 by omega) (by omega),
    Option.some.injEq, exists_eq_left', b4, b5]
  exact ⟨by rw [kb.mem, ka.mem], (RegsKept.of_keeps ka).trans ⟨kb.gpr, kb.rd, kb.wr, kb.sp⟩⟩

theorem selectFieldPrefix_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat}
    (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun w => selectWord one vs o e w)) s fun t =>
      (∀ w < n, word t.mem base (o + 8 * w) = selWord vs ao 8 w ∧
        word t.mem base (e + 8 * w) = selWord vs ae 8 w) ∧
      Frame2 base o e 32 s.mem t.mem ∧ RegsKept s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tv, tf, kt⟩ => ?_
    have ht : Scr t base := ⟨(kt.1 _ (by decide)).trans hs.x0, kt.2.2.1 ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (selectWord_ok ht (hm.of_kept kt) one vs h0 ho he hb hbe n (by omega))
      fun u ⟨um, ku⟩ => ⟨fun w hw => ?_, ?_, kt.trans ku⟩
    · rw [um]
      by_cases hwn : w = n
      · subst hwn
        refine ⟨?_, word_writeW_self _ _ _ _⟩
        rw [word_writeW_sep _ _ _ (by omega) (by omega) (by omega), word_writeW_self]
      · have hwl : w < n := by omega
        rw [word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
          word_writeW_sep _ _ _ (by omega) (by omega) (by omega)]
        exact tv w hwl
    · rw [um]
      refine tf.trans fun x h1 h2 => ?_
      rw [write_outside _ _ _ (by omega) (by omega) (by omega) h2,
        write_outside _ _ _ (by omega) (by omega) (by omega) h1]

theorem feWord_val (v : Spec.X25519.Fe) :
    val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem selectField_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks ao ae s) (one : Bool) (vs : List Spec.X25519.Fe)
    (h0 : vs.getD 0 0 = if one then 1 else 0)
    {o e : Nat} (ho : o % 8 = 0) (he : e % 8 = 0) (hoe : o + 32 ≤ e ∨ e + 32 ≤ o)
    (hb : o + 32 ≤ 8192) (hbe : e + 32 ≤ 8192) :
    WP isa (.block (selectField one vs o e)) s fun t =>
      F t.mem base o = vs.getD ao 0 ∧ F t.mem base e = vs.getD ae 0 ∧
      Frame2 base o e 32 s.mem t.mem ∧ RegsKept s t := by
  refine WP.mono (selectFieldPrefix_ok hs hm one vs h0 ho he hoe hb hbe 4 (le_refl _))
    fun t ⟨tv, tf, kt⟩ => ⟨?_, ?_, tf, kt⟩
  · simp only [F, fe]
    have w0 := (tv 0 (by decide)).1
    have w1 := (tv 1 (by decide)).1
    have w2 := (tv 2 (by decide)).1
    have w3 := (tv 3 (by decide)).1
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at w0 w1 w2 w3
    rw [w0, w1, w2, w3]
    simp only [selWord, show ao ≤ 8 by omega, ↓reduceIte]
    rw [feWord_val, toFe_self]
  · simp only [F, fe]
    have w0 := (tv 0 (by decide)).2
    have w1 := (tv 1 (by decide)).2
    have w2 := (tv 2 (by decide)).2
    have w3 := (tv 3 (by decide)).2
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at w0 w1 w2 w3
    rw [w0, w1, w2, w3]
    simp only [selWord, show ae ≤ 8 by omega, ↓reduceIte]
    rw [feWord_val, toFe_self]

/-- The cached point in slots `a`, `b`, `c`, with `2Z = 2`. -/
def cachedAt (e : Env) (a b c : Slot) : Spec.Ed25519.Point := ⟨e a, e b, e c, 2⟩

private theorem entries_getD (j a : Nat) (ha : a < 9) (f : Spec.Ed25519.Point → Spec.X25519.Fe) :
    (((List.range 9).map (combCached j)).map f).getD a 0 = f (combCached j a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ha, Option.map_some,
    Option.getD_some]

theorem combCached_T (j a : Nat) : (combCached j a).T = 2 := by
  unfold combCached
  split
  · rfl
  · split; rfl

theorem cachedAt_eq {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point} (hq : q.T = 2)
    (ha : e a = q.X) (hb : e b = q.Y) (hc : e c = q.Z) : cachedAt e a b c = q := by
  cases q
  simp only [cachedAt, ha, hb, hc] at hq ⊢
  rw [hq]

theorem combSelect_ok {s : State} {base : Addr} (hs : Scr s base) {ao ae : Nat} (hao : ao < 9)
    (hae : ae < 9) (hm : Masks ao ae s) (j : Nat) :
    WP isa (.block (combSelect j)) s fun t =>
      cachedAt (env t.mem base) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem base) 13 14 15 = combCached j ae ∧
      Frame2 base (offset 4) (offset 13) 96 s.mem t.mem ∧ RegsKept s t := by
  rw [combSelect]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hs hao hae hm true _ (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := offset 4) (e := offset 13) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun b ⟨b4, b13, bf, kb⟩ => ?_
  have hsb : Scr b base := ⟨(kb.1 _ (by decide)).trans hs.x0, kb.2.2.1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (selectField_ok hsb hao hae (hm.of_kept kb) true _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := offset 5) (e := offset 14) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun c ⟨c5, c14, cf, kc⟩ => ?_
  have hsc : Scr c base := ⟨(kc.1 _ (by decide)).trans hsb.x0, kc.2.2.1 ▸ hsb.wr, hs.nowrap⟩
  refine WP.mono (selectField_ok hsc hao hae ((hm.of_kept kb).of_kept kc) false _
    (by rw [entries_getD j 0 (by decide)]; rfl)
    (o := offset 6) (e := offset 15) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨t6, t15, tf, kt⟩ => ⟨?_, ?_, ?_, (kb.trans kc).trans kt⟩
  · rw [entries_getD j ao hao] at b4 c5 t6
    refine cachedAt_eq (combCached_T j ao) ?_ ?_ t6
    · change F t.mem base (offset 4) = _
      rw [tf.F (by decide) (by decide) (by decide), cf.F (by decide) (by decide) (by decide), b4]
    · change F t.mem base (offset 5) = _
      rw [tf.F (by decide) (by decide) (by decide), c5]
  · rw [entries_getD j ae hae] at b13 c14 t15
    refine cachedAt_eq (combCached_T j ae) ?_ ?_ t15
    · change F t.mem base (offset 13) = _
      rw [tf.F (by decide) (by decide) (by decide), cf.F (by decide) (by decide) (by decide), b13]
    · change F t.mem base (offset 14) = _
      rw [tf.F (by decide) (by decide) (by decide), c14]
  · exact ((bf.mono (by decide) (by decide) (by decide) (by decide)).trans
      (cf.mono (by decide) (by decide) (by decide) (by decide))).trans
      (tf.mono (by decide) (by decide) (by decide) (by decide))

theorem combSelectFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 32) {s : State} {base : Addr}
    (hs : Scr s base) {ao ae : Nat} (hao : ao < 9) (hae : ae < 9) (hm : Masks ao ae s)
    {j : Nat} (hj : j ∈ ks) (hj32 : j < 32) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (combSelectFrom ks) s fun t =>
      cachedAt (env t.mem base) 4 5 6 = combCached j ao ∧
      cachedAt (env t.mem base) 13 14 15 = combCached j ae ∧
      Frame2 base (offset 4) (offset 13) 96 s.mem t.mem ∧ RegsKept s t := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    have hk : k < 32 := hks k (by simp)
    have hz' : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      bv_omega_using [hj32, hk]
    rw [combSelectFrom]
    refine WP.seq (WP.mono (show WP isa (.block [.subImm .x .x9 .x19 k]) s fun t =>
        (t.gpr .x9 == 0) = decide (j = k) ∧ Keeps [.x9] s t by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x (show k < 4096 by omega),
        read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, hz', Option.some.injEq,
        exists_eq_left']
      exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl,
        rfl⟩⟩) fun t ⟨tz, kt⟩ => ?_)
    have ht : Scr t base := hs.of_keeps kt (by decide)
    have kst : RegsKept s t := RegsKept.of_keeps (kt.mono (by decide))
    have tm : Masks ao ae t := hm.of_kept kst
    refine WP.ite (decide (j = k)) (by simp only [eval, read_x, tz]) (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      refine WP.mono (combSelect_ok ht hao hae tm j) fun u ⟨u1, u2, uf, ku⟩ =>
        ⟨u1, u2, by rw [← kt.mem]; exact uf, kst.trans ku⟩
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      refine WP.mono (ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) ht tm hj'
        (by rw [kt.gpr _ (by decide)]; exact hc)) fun u ⟨u1, u2, uf, ku⟩ =>
        ⟨u1, u2, by rw [← kt.mem]; exact uf, kst.trans ku⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.CombLoop`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.CombStep`. -/
section
/-!
# The comb's additions, negation and doublings

`pointAddMixed` adds an affine cached point (`Z = 1`, so its `2Z` is `2` and
the product `Z₁ · 2Z₂` is `Z₁ + Z₁`) exactly as the specification's
`pointAdd`; `combNeg` negates the selected cached point under the sign's mask;
`double4` doubles four times, exactly.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64 Fin.CommRing

/-! ## Frames -/

/-- Only the registers the comb uses (`x1`, `x19` and the field operations') and the field
slots change. -/
structure CombKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x19 → r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem CombKeep.refl (base : Addr) (s : State) : CombKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem CombKeep.trans {base : Addr} {s t u : State} (h : CombKeep base s t)
    (k : CombKeep base t u) : CombKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem CombKeep.scr {base : Addr} {s t : State} (h : CombKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem CombKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : CombKeep base s t :=
  ⟨fun r _ _ hc => h.gpr r hc, h.rd, h.wr, h.sp, h.mem⟩

theorem CombKeep.of_double {base : Addr} {s t : State} (h : DoubleKeep base s t) : CombKeep base s t :=
  ⟨fun r _ h1 hc => h.gpr r h1 hc, h.rd, h.wr, h.sp, h.mem⟩

theorem CombKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : CombKeep base s t := by
  refine ⟨fun r h19 h1 hc => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, by rw [h.mem]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact h19 h
  · exact h1 h
  · exact hc h

theorem CombKeep.bit {base : Addr} {s t : State} (h : CombKeep base s t) {q : Nat} (hq : q < 256) :
    t.mem (off base (768 + q)) = s.mem (off base (768 + q)) :=
  h.mem _ (by rw [ofs_off' base (by omega)]; omega)

theorem CombKeep.powers {base : Addr} {s t : State} (h : CombKeep base s t) :
    PowersKeep base 56 7368 s t :=
  ⟨fun r a b c => h.gpr r a b c, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

/-! ## The mixed additions -/

/-- What `addOddOps` and `addEvenOps` compute, from the accumulator's coordinates and the cached
entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> ring

theorem addOdd_formula (e : Env) :
    point (evalOps addOddOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) := rfl

theorem addEven_formula (e : Env) :
    point (evalOps addEvenOps e) 17 18 19 20 =
      mixedResult (e 17) (e 18) (e 19) (e 20) (e 13) (e 14) (e 15) := rfl

theorem mixed_eval {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point}
    (hq : cachedAt e a b c = cache q) (p : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (e a) (e b) (e c) = Spec.Ed25519.pointAdd p q := by
  have h4 : e a = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e b = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e c = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  rw [h4, h5, h6, mixedResult_eq p q hz]

theorem addOdd_ok {s : State} {base : Addr} (hs : Scr s base)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem base) 4 5 6 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addOddOps)) s fun t =>
      Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, (4 ≤ i.val ∧ i.val < 8 ∨ 13 ≤ i.val) → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok addOddOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addOdd_formula _).trans (mixed_eval hq (point (env s.mem base) 0 1 2 3) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addOddOps, (fieldDest op).val < 4 ∨ (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) :=
    by decide
  have := this op hop
  rw [← h] at this
  omega

theorem addEven_ok {s : State} {base : Addr} (hs : Scr s base)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem base) 13 14 15 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addEvenOps)) s fun t =>
      Keep base s t ∧ point (env t.mem base) 17 18 19 20 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 17 18 19 20) q ∧
      ∀ i : Slot, (i.val < 8 ∨ 13 ≤ i.val ∧ i.val < 17 ∨ 21 ≤ i.val) →
        env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok addEvenOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addEven_formula _).trans (mixed_eval hq (point (env s.mem base) 17 18 19 20) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addEvenOps, (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) ∨
      (17 ≤ (fieldDest op).val ∧ (fieldDest op).val < 21) := by decide
  have := this op hop
  rw [← h] at this
  omega

/-! ## The negations -/

private theorem index3_fact : ∀ j < 32, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

private theorem bit_mask : ∀ b < 2,
    ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 - BitVec.ofNat 64 1 = mask (decide (b = 0)) := by
  decide

theorem nib_neg (S i : Nat) : decide (nib S i < 8) = decide ((S / 2 ^ (4 * i + 3)) % 2 = 0) := by
  rw [nib_bits]
  have h0 := Nat.mod_lt (S / 2 ^ (4 * i)) (show 2 > 0 by decide)
  have h1 := Nat.mod_lt (S / 2 ^ (4 * i + 1)) (show 2 > 0 by decide)
  have h2 := Nat.mod_lt (S / 2 ^ (4 * i + 2)) (show 2 > 0 by decide)
  have h3 := Nat.mod_lt (S / 2 ^ (4 * i + 3)) (show 2 > 0 by decide)
  apply decide_eq_decide.mpr
  omega

theorem signLoad_ok {s : State} {base : Addr} (hs : Scr s base) {S j i o : Nat} (hj : j < 32)
    (hi : i < 64) (hoi : 8 * j + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block [.lsl .x .x3 .x19 3, .add .x .x3 .x0 .x3, .ldrb .x3 .x3 (o + 3),
      .subImm .x .x3 .x3 1]) s fun t =>
      t.gpr .x3 = mask (decide (nib S i < 8)) ∧ Keeps [.x3] s t := by
  have _hcap : workSize true = 8192 := rfl
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + 3))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (o + 3) = off base (768 + (4 * i + 3)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hv := bit_mask _ (Nat.mod_lt (S / 2 ^ (4 * i + 3)) (show 2 > 0 by decide))
  rw [← hb _ (by omega), ← nib_neg] at hv
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, State.load, addr, Size.bits,
    show (3 : Nat) < 64 from by decide, show (1 : Nat) < 4096 from by decide,
    show o + 3 < 4096 * 1 by omega, Nat.mod_one, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    hc, index3_fact j hj, hs.x0, he, hr, read_byte, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The negation, on the environment. -/
theorem neg_env (e : Env) (a b c : Slot) (sw : Bool) (hab : a ≠ b) (hc8 : c ≠ 8) (ha : a ≠ 8)
    (hb : b ≠ 8) (hac : a ≠ c) (hbc : b ≠ c) (hz : e 21 = 0) :
    cachedAt (swapEnvs [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e)) a b c =
      if sw then negCached (cachedAt e a b c) else cachedAt e a b c := by
  cases sw <;> simp [cachedAt, negCached, swapEnvs, swapEnv, evalOps, evalOp,
    hab, hc8, ha, hb, ha.symm, hb.symm, hac, hac.symm, hbc, hbc.symm, hz]

theorem neg_other (e : Env) (a b c : Slot) (sw : Bool) (i : Slot) (ha : i ≠ a) (hb : i ≠ b)
    (hc : i ≠ c) (h8 : i ≠ 8) :
    swapEnvs [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e) i = e i := by
  cases sw <;> simp [swapEnvs, swapEnv, evalOps, evalOp, Function.update_apply, ha, hb, hc, h8]

theorem combNeg_ok {s : State} {base : Addr} (hs : Scr s base) {S j i o : Nat} (a b c : Slot)
    (hj : j < 32) (hi : i < 64) (hoi : 8 * j + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hdis : ∀ ab ∈ [(a, b), (c, (8 : Slot))], ab.1 ≠ ab.2) :
    WP isa (.block (combNeg a b c o)) s fun t => Keep base s t ∧
      env t.mem base = swapEnvs [(a, b), (c, 8)] (decide (nib S i < 8))
        (evalOps [.sub 8 21 c] (env s.mem base)) := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 8 21 c] hs) fun u ⟨ku, vu⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (signLoad_ok (S := S) (ku.scr hs) hj hi hoi ho ((ku.gpr _ (by decide)).trans hc)
    (fun q hq => by rw [ku.mem _ (by rw [ofs_off' base (by omega)]; omega)]; exact hb q hq))
    fun v ⟨v3, kv⟩ => ?_
  have kuv : Keep base u v := Keep.of_keeps kv (by decide)
  refine WP.mono (swapFields_ok ((ku.trans kuv).scr hs) [(a, b), (c, 8)] hdis v3)
    fun t ⟨kt, _, vt⟩ => ⟨(ku.trans kuv).trans kt, ?_⟩
  rw [vt, kv.mem, vu]

/-! ## Four doublings -/

structure Double4Inv (s₀ : State) (base : Addr) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 4
  scratch : Scr s base
  counter : s.gpr .x1 = BitVec.ofNat 64 n
  value : point (env s.mem base) 0 1 2 3 = powerPoint (point (env s₀.mem base) 0 1 2 3) (4 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem base i = env s₀.mem base i
  keep : DoubleKeep base s₀ s

theorem double4_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa double4 s fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s.mem base) 0 1 2 3) 4 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [double4]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .w .x1 4 0]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 4 ∧ Keeps [.x1] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [RegUpd.gpr_write_self]; rfl
    · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)) fun a ⟨ac, ka⟩ => ?_)
  have hsa : Scr a base := hs.of_keeps ka (by decide)
  have kda : DoubleKeep base s a := ⟨fun r hr _ => ka.gpr r (by simpa using hr), ka.rd, ka.wr, ka.sp,
    by rw [ka.mem]; exact Outside.refl _ _ _ _⟩
  have hl : WP isa (.loop (.block doubleBody) (.nonzero .x .x1)) a fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env a.mem base) 0 1 2 3) 4 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env a.mem base i) ∧ DoubleKeep base a t := by
    apply WP.loop (Double4Inv a base) (n := 4)
    · intro n u hi
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
      have hk : k < 4 := by have := hi.bound; omega
      refine WP.mono (doubleBody_ok hi.scratch k hi.counter
        ((hi.high 16 (by decide)).trans (by rw [ka.mem]; exact hd))) fun t ⟨htc, htv, hthi, htk⟩ => ?_
      have hv : point (env t.mem base) 0 1 2 3 = powerPoint (point (env a.mem base) 0 1 2 3) (4 - k) := by
        rw [htv, hi.value, show 4 - k = (4 - (k + 1)) + 1 by omega, powerPoint]
      have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env a.mem base i :=
        fun i h => (hthi i h).trans (hi.high i h)
      have hkeep := hi.keep.trans htk
      by_cases hk0 : k = 0
      · subst hk0
        exact Or.inl ⟨by simp only [eval, read_x, htc, point_counter_nonzero 0 (by decide),
          show decide ((0 : Nat) ≠ 0) = false from rfl], hv, hh, hkeep⟩
      · exact Or.inr ⟨by simp only [eval, read_x, htc, point_counter_nonzero k (by omega),
          decide_eq_true hk0], k, by omega, ⟨by omega, by omega, htk.scratch hi.scratch, htc, hv, hh, hkeep⟩⟩
    · exact ⟨by decide, le_refl _, hsa, ac, rfl, fun _ _ => rfl, DoubleKeep.refl _ _⟩
  refine WP.mono hl fun t ⟨tv, th, tk⟩ => ?_
  have ea : env a.mem base = env s.mem base := by rw [ka.mem]
  rw [ea] at tv th
  exact ⟨tv, th, kda.trans tk⟩

end VG.Proof.Ed25519.AArch64
end

/-!
# The comb's loop

After step `j`, the accumulator `A` (slots 0–3) represents `[G + Σ_{i < j}
d_{2i+1} 256^i]B` and `B` (slots 17–20) represents `[G + Σ_{i < j} d_{2i}
256^i]B` (`CombDigits`); at the end, `16 A + B` is the scalar's multiple.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open Word64

/-- The loop's invariant, after `j` steps. -/
structure CombInv (s₀ : State) (base : Addr) (S j : Nat) (s : State) : Prop where
  bound : j ≤ 32
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  zero : env s.mem base 21 = 0
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  odd : Rep (point (env s.mem base) 0 1 2 3) ((combGVal + oddSumZ S j) • baseAff)
  even : Rep (point (env s.mem base) 17 18 19 20) ((combGVal + evenSumZ S j) • baseAff)
  keep : CombKeep base s₀ s

private theorem next_fact : ∀ j < 32,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 32 != 0) = decide (j + 1 ≠ 32) := by decide +kernel

theorem combNext_ok (s : State) {j : Nat} (hj : j < 32) (h : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 32]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ 32) ∧
      Keeps [.x19, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 1 < 4096 by decide),
    exec_subImm_x (show 32 < 4096 by decide), read_x, RegUpd.gpr_write, BitVec.setWidth_eq, h,
    (next_fact j hj).1, (next_fact j hj).2, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem Frame2.slots {base : Addr} {m m' : Mem} (h : Frame2 base (offset 4) (offset 13) 96 m m') :
    Outside base 64 704 m m' := fun x hx => h x (by simp only [offset]; omega) (by simp only [offset]; omega)

theorem Frame2.env {base : Addr} {m m' : Mem} (h : Frame2 base (offset 4) (offset 13) 96 m m')
    (i : Slot) (hi : i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) : env m' base i = env m base i :=
  h.F (by simp only [offset]; omega) (by simp only [offset]; omega) (by simp only [offset]; omega)

private theorem dis_odd : ∀ ab ∈ [((4 : Slot), (5 : Slot)), (6, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

private theorem dis_even : ∀ ab ∈ [((13 : Slot), (14 : Slot)), (15, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

theorem combStep_ok {s₀ s : State} {base : Addr} {S j : Nat} (h : CombInv s₀ base S j s)
    (hj : j < 32) :
    WP isa combStep s fun t => (t.gpr .x8 != 0) = decide (j + 1 ≠ 32) ∧
      CombInv s₀ base S (j + 1) t := by
  rw [combStep]
  have no := nib_lt S (2 * j + 1)
  have ne := nib_lt S (2 * j)
  -- Both digits' masks.
  refine WP.seq (WP.mono (combDigits_ok h.scratch hj h.counter h.bits) fun a ha => ?_)
  have hsa : Scr a base := h.scratch.of_keeps ha.keeps (by decide)
  have a19 : a.gpr .x19 = BitVec.ofNat 64 j := (ha.keeps.gpr _ (by decide)).trans h.counter
  have hm : Masks (mag (nib S (2 * j + 1))) (mag (nib S (2 * j))) a :=
    ⟨ha.oddMask, ha.evenMask, ha.oddZero, ha.evenZero⟩
  have ksa : CombKeep base s a := CombKeep.of_keeps ha.keeps (by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr
    · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl hr))
  -- Both entries.
  refine WP.seq (WP.mono (combSelectFrom_ok (List.range 32) (fun k hk => List.mem_range.mp hk) hsa
    (mag_lt no) (mag_lt ne) hm (List.mem_range.mpr hj) hj a19) fun b ⟨bo, be, bf, kb⟩ => ?_)
  have hsb : Scr b base := ⟨(kb.1 _ (by decide)).trans hsa.x0, kb.2.2.1 ▸ hsa.wr, hsa.nowrap⟩
  have b19 : b.gpr .x19 = BitVec.ofNat 64 j := (kb.1 _ (by decide)).trans a19
  have kab : CombKeep base a b := ⟨fun r _ _ hc => kb.1 r (fun hm => hc (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide)), kb.2.1, kb.2.2.1, kb.2.2.2, bf.slots⟩
  have ksb := ksa.trans kab
  have bbits : ∀ q < 256, b.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => by rw [ksb.bit hq]; exact h.bits q hq
  have eb : ∀ i : Slot, (i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) →
      env b.mem base i = env s.mem base i := fun i hi => by
    rw [bf.env i hi, ha.keeps.mem]
  -- The odd entry, negated for a negative digit, and added.
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combNeg_ok hsb (S := S) (i := 2 * j + 1) 4 5 6 hj (by omega) (by omega) (by decide)
    b19 bbits dis_odd) fun c ⟨kc, vc⟩ => ?_
  obtain ⟨qo, hqo, hqoz, hrqo⟩ := combEntry_ok j (nib S (2 * j + 1)) hj no
  have b21 : env b.mem base 21 = 0 := (eb 21 (by decide)).trans h.zero
  have co : cachedAt (env c.mem base) 4 5 6 = cache qo := by
    rw [vc, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      b21, bo, ← hqo]
    by_cases hlt : nib S (2 * j + 1) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ec : ∀ i : Slot, (i.val < 4 ∨ 9 ≤ i.val) → env c.mem base i = env b.mem base i := fun i hi => by
    rw [vc, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  rw [WP.block_append_iff]
  refine WP.mono (addOdd_ok (kc.scr hsb) qo co hqoz) fun d ⟨kd, dp, dh⟩ => ?_
  -- The even entry, negated for a negative digit, and added.
  rw [WP.block_append_iff]
  have hsd : Scr d base := kd.scr (kc.scr hsb)
  have d19 : d.gpr .x19 = BitVec.ofNat 64 j := by
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide)]; exact b19
  have dbits : ∀ q < 256, d.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => by rw [(CombKeep.of_keep (kc.trans kd)).bit hq]; exact bbits q hq
  refine WP.mono (combNeg_ok hsd (S := S) (i := 2 * j) 13 14 15 hj (by omega) (by omega) (by decide)
    d19 dbits dis_even) fun f ⟨kf, vf⟩ => ?_
  obtain ⟨qe, hqe, hqez, hrqe⟩ := combEntry_ok j (nib S (2 * j)) hj ne
  have ed : ∀ i : Slot, 13 ≤ i.val → env d.mem base i = env b.mem base i := fun i hi => by
    rw [dh i (Or.inr hi), ec i (Or.inr (by omega))]
  have fe : cachedAt (env f.mem base) 13 14 15 = cache qe := by
    rw [vf, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((ed 21 (by decide)).trans b21)]
    have : cachedAt (env d.mem base) 13 14 15 = cachedAt (env b.mem base) 13 14 15 := by
      simp only [cachedAt, ed 13 (by decide), ed 14 (by decide), ed 15 (by decide)]
    rw [this, be, ← hqe]
    by_cases hlt : nib S (2 * j) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ef : ∀ i : Slot, (i.val < 8 ∨ 16 ≤ i.val) → env f.mem base i = env d.mem base i := fun i hi => by
    rw [vf, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  rw [WP.block_append_iff]
  refine WP.mono (addEven_ok (kf.scr hsd) qe fe hqez) fun g ⟨kg, gp, gh⟩ => ?_
  have g19 : g.gpr .x19 = BitVec.ofNat 64 j := by
    rw [kg.gpr _ (by decide), kf.gpr _ (by decide)]; exact d19
  refine WP.mono (combNext_ok g hj g19) fun t ⟨t19, t8, kt⟩ => ⟨t8, ?_⟩
  have kbt : CombKeep base b t :=
    ((((CombKeep.of_keep kc).trans (CombKeep.of_keep kd)).trans (CombKeep.of_keep kf)).trans
      (CombKeep.of_keep kg)).trans (CombKeep.of_keeps kt (by decide))
  have kst := ksb.trans kbt
  -- Slots 0–3 after the odd addition; 17–20 after the even one.
  have eg : ∀ i : Slot, i.val < 4 → env g.mem base i = env d.mem base i := fun i hi => by
    rw [gh i (Or.inl (by omega)), ef i (Or.inl (by omega))]
  have pc : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide),
      eb 0 (by decide), eb 1 (by decide), eb 2 (by decide), eb 3 (by decide)]
  have pf : point (env f.mem base) 17 18 19 20 = point (env s.mem base) 17 18 19 20 := by
    simp only [point, ef 17 (by decide), ef 18 (by decide), ef 19 (by decide), ef 20 (by decide),
      ed 17 (by decide), ed 18 (by decide), ed 19 (by decide), ed 20 (by decide),
      eb 17 (by decide), eb 18 (by decide), eb 19 (by decide), eb 20 (by decide)]
  refine ⟨by omega, kbt.scr hsb, t19, ?_, fun q hq => ?_, ?_, ?_, h.keep.trans kst⟩
  · rw [kt.mem, gh 21 (Or.inr (Or.inr (by decide))), ef 21 (by decide), ed 21 (by decide)]
    exact b21
  · rw [kst.bit hq]; exact h.bits q hq
  · have pg : point (env g.mem base) 0 1 2 3 = point (env d.mem base) 0 1 2 3 := by
      simp only [point, eg 0 (by decide), eg 1 (by decide), eg 2 (by decide), eg 3 (by decide)]
    rw [kt.mem, pg, dp, pc, oddSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.odd hrqo
  · rw [kt.mem, gp, pf, evenSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.even hrqe

/-! ## The loop and the end -/

theorem combInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block combInit) s fun t => CombKeep base s t ∧ env t.mem base 21 = 0 ∧
      point (env t.mem base) 0 1 2 3 = combG ∧ point (env t.mem base) 17 18 19 20 = combG ∧
      t.gpr .x19 = BitVec.ofNat 64 0 := by
  rw [combInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka, va⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨(CombKeep.of_keep ka).trans ⟨fun r hr _ _ => RegUpd.gpr_write_of_ne _ _ _ hr,
    rfl, rfl, rfl, Outside.refl _ _ _ _⟩, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.mem_write, va]; rfl
  · simp only [RegUpd.mem_write, va]; rfl
  · simp only [RegUpd.mem_write, va]; rfl
  · rw [RegUpd.gpr_write_self]; rfl

theorem combFinish_ok {s : State} {base : Addr} (hs : Scr s base) {v w : ℤ}
    (ha : Rep (point (env s.mem base) 0 1 2 3) (v • baseAff))
    (hb : Rep (point (env s.mem base) 17 18 19 20) (w • baseAff)) :
    WP isa combFinish s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) ((16 * v + w) • baseAff) ∧ CombKeep base s t := by
  rw [combFinish]
  refine WP.seq (WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] hs) fun a ⟨ka, va⟩ => ?_)
  have hsa := ka.scr hs
  have ea : ∀ i : Slot, i ≠ 16 → env a.mem base i = env s.mem base i := fun i hi => by
    rw [va]; exact evalOps_unchanged _ _ i (by simpa [fieldDest] using hi)
  have ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; rfl
  refine WP.seq (WP.mono (double4_ok hsa ad) fun b ⟨bp, bh, kb⟩ => ?_)
  have hsb := kb.scratch hsa
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] hsb)
    fun c ⟨kc, vc⟩ => ?_
  have hsc := kc.scr hsb
  have cd : env c.mem base 16 = Spec.Ed25519.d := by
    rw [vc, show evalOps [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] (env b.mem base) 16 =
      env b.mem base 16 from rfl, bh 16 (by decide), ad]
  refine WP.mono (pointAdd_ok hsc cd) fun t ⟨kt, tp, _⟩ => ?_
  refine ⟨?_, (((CombKeep.of_keep ka).trans (CombKeep.of_double kb)).trans (CombKeep.of_keep kc)).trans
    (CombKeep.of_keep kt)⟩
  have p0 : point (env c.mem base) 0 1 2 3 = point (env b.mem base) 0 1 2 3 := by rw [vc]; rfl
  have p4 : point (env c.mem base) 4 5 6 7 = point (env s.mem base) 17 18 19 20 := by
    rw [vc]
    show point (env b.mem base) 17 18 19 20 = _
    simp only [point, bh 17 (by decide), bh 18 (by decide), bh 19 (by decide), bh 20 (by decide),
      ea 17 (by decide), ea 18 (by decide), ea 19 (by decide), ea 20 (by decide)]
  have pa : point (env a.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, ea 0 (by decide), ea 1 (by decide), ea 2 (by decide), ea 3 (by decide)]
  rw [tp, p0, p4, bp, pa, ← zsmul_16]
  have h4 := powerPoint_rep ha 4
  rw [show (2 ^ 4 : Nat) = 16 from rfl] at h4
  exact pointAdd_rep h4 hb

theorem combMultiply_ok {s : State} {base : Addr} (hs : Scr s base) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ CombKeep base s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono (combInit_ok hs) fun b ⟨kb, bz, bp, bq, b19⟩ => ?_)
  have hg : Rep combG (((combGVal : ℤ) + 0) • baseAff) := by
    rw [add_zero, natCast_zsmul]; exact combG_ok
  have init : CombInv s base S 0 b :=
    ⟨by decide, kb.scr hs, b19, bz, fun q hq => by rw [kb.bit hq]; exact hb q hq,
      by rw [bp]; exact hg, by rw [bq]; exact hg, kb⟩
  have hl : WP isa (.loop combStep (.nonzero .x .x8)) b fun t => CombInv s base S 32 t := by
    apply WP.loop (fun n t => CombInv s base S (32 - n) t ∧ 0 < n ∧ n ≤ 32) (n := 32)
    · intro n t ⟨ht, hn0, hn⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      refine WP.mono (combStep_ok ht (by omega)) fun u ⟨u8, hu⟩ => ?_
      by_cases hk : k = 0
      · subst hk
        exact Or.inl ⟨by simp only [eval, read_x, u8, show 32 - (0 + 1) + 1 = 32 from rfl, ne_eq,
          not_true_eq_false, decide_false], hu⟩
      · refine Or.inr ⟨by simp only [eval, read_x, u8, show 32 - (k + 1) + 1 ≠ 32 by omega, ne_eq,
          not_false_eq_true, decide_true], k, by omega, ?_, by omega, by omega⟩
        rw [show 32 - k = 32 - (k + 1) + 1 by omega]; exact hu
    · exact ⟨init, by decide, by decide⟩
  refine WP.seq (WP.mono hl fun t ht => ?_)
  refine WP.mono (combFinish_ok ht.scratch ht.odd ht.even) fun u ⟨hu, ku⟩ => ⟨?_, ht.keep.trans ku⟩
  rw [comb_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.RecoverSign`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.RecoverAdjust`. -/
section
/-! Sign selection and the extended coordinates of a decoded point. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩

def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem recoverSuccess_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block recoverSuccess) s fun t => Keep base s t ∧ t.gpr .x8 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (env s.mem base 0) (env s.mem base 1) := by
  rw [recoverSuccess, WP.block_append_iff]
  refine WP.mono (fieldCode_ok recoverSuccessOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (returnFlag_ok a true) fun t ⟨tr, kt⟩ => ?_
  refine ⟨ka.trans (Keep.of_keeps kt (by decide)), tr, ?_⟩
  rw [kt.mem, va]
  rfl

private theorem adjustBranch_ok {s : State} {base : Addr} (hs : Scr s base) (b : Bool)
    (hz : (s.gpr .x8 == 0) = (((env s.mem base 0).val % 2 == 1) == b)) :
    WP isa (.ite (.zero .x .x8) (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0]))) s fun t =>
      Keep base s t ∧ env t.mem base 0 = signedX (env s.mem base 0) b ∧ env t.mem base 1 = env s.mem base 1 := by
  apply WP.ite (((env s.mem base 0).val % 2 == 1) == b) (by simp only [eval, read_x, hz])
  · intro h
    exact WP.block_nil ⟨Keep.refl _ _, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hs) fun t ⟨kt, vt⟩ => ?_
    refine ⟨kt, ?_, ?_⟩
    · rw [vt]
      change 0 - env s.mem base 0 = signedX (env s.mem base 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [vt]; rfl

theorem recoverAdjustSign_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa recoverAdjustSign s fun t => Keep base s t ∧ t.gpr .x8 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (signedX (env s.mem base 0) b) (env s.mem base 1) := by
  rw [recoverAdjustSign]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.gpr _ (by decide)).trans hb)) fun c ⟨cz, kc⟩ => ?_
  have kac : Keep base s c := (Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kc (by decide))
  have cm : c.mem = s.mem := kc.mem.trans ka.mem
  have ch : (c.gpr .x8 == 0) = (((env c.mem base 0).val % 2 == 1) == b) := by rw [cz, ax, cm]
  refine WP.seq (WP.mono (adjustBranch_ok (kac.scr hs) b ch) fun d ⟨kd, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok ((kac.trans kd).scr hs)) fun t ⟨kt, tr, tv⟩ => ?_
  exact ⟨(kac.trans kd).trans kt, tr, by rw [tv, dx, dy, cm]⟩

end VG.Proof.Ed25519.AArch64
end

/-! Reject the negative encoding of zero and otherwise return the selected sign. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def DecodeResult (base : Addr) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .x8 = 0
  | some p => s.gpr .x8 = 1 ∧ point (env s.mem base) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (base : Addr) :
    WP isa recoverInvalid s fun t => Keep base s t ∧ DecodeResult base none t :=
  WP.mono (returnFlag_ok s false) fun _ ⟨tr, kt⟩ => ⟨Keep.of_keeps kt (by decide), tr⟩

theorem recoverSign_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa recoverSign s fun t => Keep base s t ∧
      DecodeResult base (signResult (env s.mem base 0) (env s.mem base 1) b) t := by
  rw [recoverSign]
  refine WP.seq (WP.mono (fieldZero_ok hs 0) fun a ⟨az, ka, am⟩ => ?_)
  apply WP.ite (decide (env s.mem base 0 = 0)) (by simp only [eval, read_x, az])
  · intro hzero
    have hz : env s.mem base 0 = 0 := of_decide_eq_true hzero
    have ab : a.gpr .x1 = signWord b := (ka.gpr _ (by decide)).trans hb
    apply WP.ite b (by simp only [eval, read_x, ab]; cases b <;> rfl)
    · intro ht
      refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tr⟩ => ?_
      refine ⟨ka.trans kt, ?_⟩
      simpa only [signResult, hz, ht, decide_true, Bool.and_self, ite_true] using tr
    · intro hf
      refine WP.mono (recoverAdjustSign_ok (ka.scr hs) b ((ka.gpr _ (by decide)).trans hb))
        fun t ⟨kt, tr, tv⟩ => ?_
      refine ⟨ka.trans kt, ?_⟩
      simp only [signResult, hf, Bool.and_false, Bool.false_eq_true, ite_false, DecodeResult]
      exact ⟨tr, by rw [tv, am, hf]⟩
  · intro hnonzero
    have hn : env s.mem base 0 ≠ 0 := of_decide_eq_false hnonzero
    refine WP.mono (recoverAdjustSign_ok (ka.scr hs) b ((ka.gpr _ (by decide)).trans hb))
      fun t ⟨kt, tr, tv⟩ => ?_
    refine ⟨ka.trans kt, ?_⟩
    simp only [signResult, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨tr, by rw [tv, am]⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual`. -/
section

/-! Projective comparison implements the specification's pointEqual. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem equalOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem pointEqual_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa Impl.Ed25519.AArch64.pointEqual s fun t => Keep base s t ∧
      t.gpr .x8 = signWord (Spec.Ed25519.pointEqual (point (env s.mem base) 0 1 2 3)
        (point (env s.mem base) 4 5 6 7)) := by
  rw [Impl.Ed25519.AArch64.pointEqual]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.scr hs) 8 9) fun b ⟨bz, kb, be⟩ => ?_
  have kab := ka.trans kb
  have bx : (b.gpr .x8 == 0) = decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2) := by
    rw [bz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  apply WP.ite _ (congrArg some bx)
  · intro htx
    have hx := of_decide_eq_true htx
    refine WP.seq (WP.mono (fieldEqual_ok (kab.scr hs) 10 11) fun c ⟨cz, kc, _⟩ => ?_)
    have cy : (c.gpr .x8 == 0) = decide (env s.mem base 1 * env s.mem base 6 = env s.mem base 5 * env s.mem base 2) := by
      rw [cz, be 10 (by decide), be 11 (by decide), va, (equalOps_eval _).2.2.1, (equalOps_eval _).2.2.2]
    apply WP.ite _ (congrArg some cy)
    · intro hty
      have hy := of_decide_eq_true hty
      refine WP.mono (returnFlag_ok c true) fun t ⟨tr, kt⟩ => ?_
      refine ⟨(kab.trans kc).trans (Keep.of_keeps kt (by decide)), ?_⟩
      simpa only [Spec.Ed25519.pointEqual, point, hx, hy, beq_self_eq_true, Bool.and_self] using tr
    · intro hfy
      have hy := of_decide_eq_false hfy
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
      refine ⟨(kab.trans kc).trans kt, ?_⟩
      simpa only [Spec.Ed25519.pointEqual, point, hx, beq_self_eq_true, beq_eq_false_iff_ne.mpr hy,
        Bool.and_false, DecodeResult, signWord, Bool.false_eq_true, ite_false] using tr
  · intro hfx
    have hx := of_decide_eq_false hfx
    refine WP.mono (recoverInvalid_ok b base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨kab.trans kt, ?_⟩
    simpa only [Spec.Ed25519.pointEqual, point, beq_eq_false_iff_ne.mpr hx, Bool.false_and, DecodeResult, signWord, Bool.false_eq_true, ite_false] using tr

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.RecoverCandidate`. -/
section
/-! Candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

private theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧
    evalOps recoverInitOps e 6 = rootU (e 1) ∧
    evalOps recoverInitOps e 7 = rootV (e 1) ∧
    evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact pow_three _
  · exact congrArg (rootU (e 1) * ·) (pow_seven _)

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem recoverCandidate_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa recoverCandidate s fun t => CounterKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hs) fun a ⟨ka, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_ok (ka.scr hs)) fun b ⟨kb, vb⟩ => ?_)
  have kbr : CounterKeep base a b := ⟨kb.gpr, kb.rd, kb.wr, kb.sp, kb.mem.mono (by decide) (by decide)⟩
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    exact Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
  refine WP.mono (fieldCode_ok recoverFinishOps (kbr.scr (ka.scr hs))) fun t ⟨kt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootPower_eq, va, au, av3, az]
    rfl
  have kar : CounterKeep base s a := CounterKeep.of_keep ka
  have ktr : CounterKeep base b t := CounterKeep.of_keep kt
  refine ⟨kar.trans (kbr.trans ktr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.AArch64
end

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa recoverSign s fun t => CounterKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨CounterKeep.of_keep kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa recoverPoint s fun t => CounterKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hs) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.scr hs) 11 6) fun c ⟨cz, kc, ce⟩ => ?_)
  have kac := ka.trans (CounterKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by simp only [eval, read_x, cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.scr hs) b ((kac.gpr _ (by decide) (by decide)).trans hb)
      _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kac.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.scr hs) 11 12) fun d ⟨dz, kd, de⟩ => ?_)
    have kacd := kac.trans (CounterKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by simp only [eval, read_x, dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] (kacd.scr hs))
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (CounterKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.scr hs) b ((kacde.gpr _ (by decide) (by decide)).trans hb)
        _ _ ex ey) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacd.trans (CounterKeep.of_keep kt), by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport`. -/
section

/-! Relational constant-time composition with a public stack pointer.
The AArch64 taint domain always includes sp; this wrapper carries its agreement
through every composition, while individual relations describe the other data. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64

def CT (P : State → State → Prop) (c : Prog isa) (Q : State → State → Prop) : Prop :=
  RelCT isa (fun x y => x.sp = y.sp ∧ P x y) c (fun x y => x.sp = y.sp ∧ Q x y)

namespace CT

theorem mono {P P' Q Q' : State → State → Prop} {c : Prog isa} (h : VG.Proof.Ed25519.AArch64.CT P c Q)
    (hp : ∀ x y, P' x y → P x y) (hq : ∀ x y, Q x y → Q' x y) : VG.Proof.Ed25519.AArch64.CT P' c Q' :=
  VG.RelCT.mono h (fun x y h => ⟨h.1, hp x y h.2⟩) (fun x y h => ⟨h.1, hq x y h.2⟩)

theorem seq {P R Q : State → State → Prop} {c d : Prog isa} (h : VG.Proof.Ed25519.AArch64.CT P c R) (k : VG.Proof.Ed25519.AArch64.CT R d Q) :
    VG.Proof.Ed25519.AArch64.CT P (.seq c d) Q := VG.RelCT.seq h k

theorem ite {P Q : State → State → Prop} {c : Cond} {yes no : Prog isa}
    (hc : ∀ x y, P x y → eval c x = eval c y)
    (hy : VG.Proof.Ed25519.AArch64.CT (fun x y => P x y ∧ eval c x = some true) yes Q)
    (hn : VG.Proof.Ed25519.AArch64.CT (fun x y => P x y ∧ eval c x = some false) no Q) :
    VG.Proof.Ed25519.AArch64.CT P (.ite c yes no) Q :=
  VG.RelCT.ite (fun x y h => hc x y h.2)
    (VG.RelCT.mono hy (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h => h))
    (VG.RelCT.mono hn (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h => h))

theorem of_false {P Q : State → State → Prop} {c : Prog isa} (h : ∀ x y, ¬ P x y) : VG.Proof.Ed25519.AArch64.CT P c Q :=
  VG.RelCT.of_false (fun x y hp => h x y hp.2)

theorem wp {P Q : State → State → Prop} {F G : State → Prop} {c : Prog isa}
    (h : VG.Proof.Ed25519.AArch64.CT P c Q) (hw : ∀ x y, P x y → WP isa c x F ∧ WP isa c y G) :
    VG.Proof.Ed25519.AArch64.CT P c (fun x y => Q x y ∧ F x ∧ G y) :=
  VG.RelCT.mono (VG.RelCT.wp h (fun x y hp => hw x y hp.2)) (fun _ _ h => h)
    (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩)

theorem loop {body : Prog isa} {c : Cond} {Q : State → State → Prop}
    (I : Nat → State → State → Prop)
    (hstep : ∀ n, VG.Proof.Ed25519.AArch64.CT (I n) body fun x y => eval c x = eval c y ∧
      (eval c x = some false → Q x y) ∧ (eval c x = some true → ∃ m < n, I m x y))
    (n : Nat) : VG.Proof.Ed25519.AArch64.CT (I n) (.loop body c) Q := by
  apply VG.RelCT.loop (M := isa) (fun n x y => x.sp = y.sp ∧ I n x y) ?_ n
  intro n
  exact VG.RelCT.mono (hstep n) (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1, fun hf => ⟨h.1, h.2.2.1 hf⟩, fun ht =>
      let ⟨m, hm, hi⟩ := h.2.2.2 ht
      ⟨m, hm, h.1, hi⟩⟩)

theorem taint {P : State → State → Prop} {c : Prog isa} (τ : VG.AArch64.Taint.T)
    (hp : ∀ x y, P x y → ∀ r ∈ τ, x.gpr r = y.gpr r) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (VG.AArch64.taint.check τ c hc).isSome = true) : VG.Proof.Ed25519.AArch64.CT P c (fun _ _ => True) := by
  intro x y tx ty u v ⟨hsp, hp'⟩ ex ey
  obtain ⟨τ', hh⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hh (show VG.AArch64.Taint.Agree τ x y from ⟨hsp, hp x y hp'⟩) ex ey
  exact ⟨ht, ha.1, True.intro⟩

theorem taintRegs {τ : VG.AArch64.Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ x y, P x y → ∀ r ∈ τ, x.gpr r = y.gpr r) (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : ((VG.AArch64.taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ') = some true) :
    VG.Proof.Ed25519.AArch64.CT P c (fun x y => ∀ r ∈ rs, x.gpr r = y.gpr r) := by
  intro x y tx ty u v ⟨hsp, hp'⟩ ex ey
  obtain ⟨τ', hh, hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hh (show VG.AArch64.Taint.Agree τ x y from ⟨hsp, hp x y hp'⟩) ex ey
  exact ⟨ht, ha.1, fun r hr => ha.2 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

end CT

theorem agree_ofRegs {rs : List Reg} {x y : State} (h : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs rs, x.gpr r = y.gpr r := fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)

theorem execBlock_append_seq {xs ys : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (xs ++ ys)) s tr t) :
    Exec isa (.seq (.block xs) (.block ys)) s tr t := by
  rw [Exec.block_iff, execBlock_append] at h
  obtain ⟨⟨u, tx⟩, hu, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v, ty⟩, hv, he⟩ := Option.map_eq_some_iff.mp ht
  cases he
  exact .seq (.block hu) (.block hv)

theorem blockAppend_ct {P R Q : State → State → Prop} {xs ys : List Instr}
    (hx : VG.Proof.Ed25519.AArch64.CT P (.block xs) R) (hy : VG.Proof.Ed25519.AArch64.CT R (.block ys) Q) : VG.Proof.Ed25519.AArch64.CT P (.block (xs ++ ys)) Q :=
  fun _ _ _ _ _ _ hp ex ey => CT.seq hx hy _ _ _ _ _ _ hp
    (VG.Proof.Ed25519.AArch64.execBlock_append_seq ex) (VG.Proof.Ed25519.AArch64.execBlock_append_seq ey)

theorem withRuns {P Q F G : State → State → Prop} {c : Prog isa}
    (h : VG.Proof.Ed25519.AArch64.CT P c Q) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (G y)) :
    VG.Proof.Ed25519.AArch64.CT P c (fun u v => Q u v ∧ ∃ x y, P x y ∧ F x u ∧ G y v) := by
  intro x y tx ty u v ⟨hsp, hp⟩ ex ey
  obtain ⟨ht, hs, hq⟩ := h _ _ _ _ _ _ ⟨hsp, hp⟩ ex ey
  obtain ⟨⟨_, u', eu, hu⟩, ⟨_, v', ev, hv⟩⟩ := hw x y hp
  obtain ⟨-, rfl⟩ := Exec.det ex eu
  obtain ⟨-, rfl⟩ := Exec.det ey ev
  exact ⟨ht, hs, hq, x, y, hp, hu, hv⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit`. -/
section

/-! Checked literals for the verifier's fixed control-flow pieces. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

materialize_code recoverCandidate
materialize_code decodeLoadBlock := (.block pointDecodeLoad : Prog isa)
materialize_code parityBlock :=
  (.block (freeze (offset 0) ++ recoverParity) : Prog isa)
materialize_code zeroBlock := (.block (fieldZero 0) : Prog isa)
materialize_code rootCheckBlock := (.block (fieldEqual 11 6) : Prog isa)
materialize_code rootCheckMinusBlock := (.block (fieldEqual 11 12) : Prog isa)
materialize_code negateBlock := (.block (fieldCode [.const 5 0, .sub 0 5 0]) : Prog isa)
materialize_code rootAdjustBlock :=
  (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]) : Prog isa)
materialize_code successBlock := (.block recoverSuccess : Prog isa)
materialize_code pointEqualFirst := (.block (fieldCode pointEqualOps ++ fieldEqual 8 9) : Prog isa)
materialize_code pointEqualSecond := (.block (fieldEqual 10 11) : Prog isa)
materialize_code verifyWriteA := (.block (pointTableWrite 7424) : Prog isa)
materialize_code verifyWriteR := (.block (pointTableWrite 7552) : Prog isa)
materialize_code verifySetupBlock := (.block verifySetup : Prog isa)
materialize_code verifyScalarTail := (.block (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr)) : Prog isa)
materialize_code verifyFinishBlock :=
  (.block (([mov .x2 .x0, mov .x0 .x8] : List Instr) ++ scalarRestore) : Prog isa)
materialize_code windowPrepLit :=
  (.seq (.seq (.seq (.block windowSetup) aTable) (.block bTable)) (.block windowInit) : Prog isa)
materialize_code doubleWindow
materialize_code addDigitA :=
  (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++
    pointAddCachedP) : Prog isa)
materialize_code addDigitAT :=
  (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++
    pointAddCached) : Prog isa)
materialize_code addDigitB :=
  (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr 2048 ++ pointFromTableQ ++
    pointAddCachedP) : Prog isa)
materialize_code negRBlock := (.block negR : Prog isa)

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.CombErase`. -/
section

/-!
# Ed25519's base-point multiplication on AArch64: the code without its immediates

Untrusted: everything here is checked by Lean. The constant-time analysis and
`keepsV` do not read the immediates of `movz` and `movk` (`Code.eraseImm`), and
without them the comb's selections from the 32 tables are the same code, table
0's (`combMultiply_eraseImm`, proven without evaluating them). The kernel,
evaluating the analysis of `scalarBaseEngine0` or the `keepsV` check of
`scalarBase0`, then builds no table's immediates, and builds and checks one
selection rather than 32: it caches the check of the same code from the same
state. These checks are the code's only evaluations (one each), so the code
has no literal (`materialize_code`), which would cost more to check than it
saves.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- `combSelectFrom`, with every table's selection table 0's. -/
def combSelectFrom0 : List Nat → Prog isa
  | [] => .block []
  | j :: js => .seq (.block [.subImm .x .x9 .x19 j])
      (.ite (.zero .x .x9) (.block (combSelect 0)) (VG.Proof.Ed25519.AArch64.combSelectFrom0 js))

/-- `combStep`, with every table's selection table 0's. -/
def combStep0 : Prog isa :=
  .seq (.block combDigits) <|
  .seq (VG.Proof.Ed25519.AArch64.combSelectFrom0 (List.range 32)) <|
  .block (combNeg 4 5 6 772 ++ fieldCode addOddOps ++
    combNeg 13 14 15 768 ++ fieldCode addEvenOps ++
    [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 32])

/-- `combMultiply`, with every table's selection table 0's. -/
def combMultiply0 : Prog isa :=
  .seq (.block combInit) (.seq (.loop VG.Proof.Ed25519.AArch64.combStep0 (.nonzero .x .x8)) combFinish)

/-- `scalarBaseEngine`, with every table's selection table 0's. -/
def scalarBaseEngine0 : Prog isa := .seq scalarBasePrepare (.seq VG.Proof.Ed25519.AArch64.combMultiply0 pointEncode)

/-- `scalarBase`, with every table's selection table 0's. -/
def scalarBase0 : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq VG.Proof.Ed25519.AArch64.scalarBaseEngine0 scalarBaseFinish)

/-- `selectCand` without its immediates. -/
def selectCandE (k w : Nat) : List Instr := (selectCand 0 k w).map Instr.eraseImm

theorem selectCand_eraseImm (v : Spec.X25519.Fe) (k w : Nat) :
    (selectCand v k w).map Instr.eraseImm = VG.Proof.Ed25519.AArch64.selectCandE k w := rfl

/-- `selectWord` without its immediates. -/
def selectWordE (one : Bool) (o e w : Nat) : List Instr :=
  (selectWord one [] o e w).map Instr.eraseImm

theorem selectWord_eraseImm (one : Bool) (vs : List Spec.X25519.Fe) (o e w : Nat) :
    (selectWord one vs o e w).map Instr.eraseImm = VG.Proof.Ed25519.AArch64.selectWordE one o e w := by
  simp only [VG.Proof.Ed25519.AArch64.selectWordE, selectWord, List.map_append, List.map_flatMap, VG.Proof.Ed25519.AArch64.selectCand_eraseImm]

theorem combSelect_eraseImm (j : Nat) :
    (combSelect j).map Instr.eraseImm = (combSelect 0).map Instr.eraseImm := by
  simp only [combSelect, selectField, List.map_append, List.map_flatMap, VG.Proof.Ed25519.AArch64.selectWord_eraseImm]

theorem combSelectFrom_eraseImm (js : List Nat) :
    Code.eraseImm (combSelectFrom js) = Code.eraseImm (VG.Proof.Ed25519.AArch64.combSelectFrom0 js) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [combSelectFrom, VG.Proof.Ed25519.AArch64.combSelectFrom0, Code.eraseImm, VG.Proof.Ed25519.AArch64.combSelect_eraseImm, ih]

theorem combMultiply_eraseImm : Code.eraseImm combMultiply = Code.eraseImm VG.Proof.Ed25519.AArch64.combMultiply0 := by
  simp only [combMultiply, VG.Proof.Ed25519.AArch64.combMultiply0, combStep, VG.Proof.Ed25519.AArch64.combStep0, Code.eraseImm,
    VG.Proof.Ed25519.AArch64.combSelectFrom_eraseImm]

theorem scalarBaseEngine_eraseImm :
    Code.eraseImm scalarBaseEngine = Code.eraseImm VG.Proof.Ed25519.AArch64.scalarBaseEngine0 := by
  simp only [scalarBaseEngine, VG.Proof.Ed25519.AArch64.scalarBaseEngine0, Code.eraseImm, VG.Proof.Ed25519.AArch64.combMultiply_eraseImm]

theorem scalarBase_eraseImm : Code.eraseImm scalarBase = Code.eraseImm VG.Proof.Ed25519.AArch64.scalarBase0 := by
  simp only [scalarBase, VG.Proof.Ed25519.AArch64.scalarBase0, Code.eraseImm, VG.Proof.Ed25519.AArch64.scalarBaseEngine_eraseImm]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks`. -/
section

/-! Fixed-trace arithmetic blocks used in point recovery. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem x0_agree {base : Addr} {s t : State} (hs : s.gpr .x0 = base) (ht : t.gpr .x0 = base) :
    ∀ r ∈ Taint.ofRegs [.x0], s.gpr r = t.gpr r := VG.Proof.Ed25519.AArch64.agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : Addr) :
    VG.Proof.Ed25519.AArch64.CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) recoverCandidate (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.AArch64.x0_agree h.1 h.2

theorem parityBlock_ct (base : Addr) :
    VG.Proof.Ed25519.AArch64.CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (freeze (offset 0) ++ recoverParity)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.AArch64.x0_agree h.1 h.2

theorem zeroBlock_ct (base : Addr) :
    VG.Proof.Ed25519.AArch64.CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.AArch64.x0_agree h.1 h.2

theorem negateBlock_ct (base : Addr) :
    VG.Proof.Ed25519.AArch64.CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (fieldCode [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.AArch64.x0_agree h.1 h.2

theorem successBlock_ct (base : Addr) :
    VG.Proof.Ed25519.AArch64.CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block recoverSuccess) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => VG.Proof.Ed25519.AArch64.x0_agree h.1 h.2

theorem recoverInvalid_ct : VG.Proof.Ed25519.AArch64.CT (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
  exact fun _ _ _ => VG.Proof.Ed25519.AArch64.agree_ofRegs (by simp)

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine`. -/
section

/-! The scalar bits, base-point multiplication, and canonical encoding compose. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (VG.Proof.Ed25519.AArch64.encodedValue p) := rfl

theorem encodedValue_rep {p q : Spec.Ed25519.Point} {a : Edwards.EPoint dZ} (hp : Rep p a)
    (hq : Rep q a) : VG.Proof.Ed25519.AArch64.encodedValue p = VG.Proof.Ed25519.AArch64.encodedValue q := by
  rw [VG.Proof.Ed25519.AArch64.encodedValue, VG.Proof.Ed25519.AArch64.encodedValue, hp.affine_x, hp.affine_y, hq.affine_x, hq.affine_y]

theorem powersKeep_outside {base : Addr} {s t : State} (h : PowersKeep base 56 7368 s t) :
    Outside base 56 7368 s.mem t.mem := fun p hp => h.mem p (by omega) hp

theorem scalarBasePrepare_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa scalarBasePrepare s fun t => PowersKeep base 56 7368 s t ∧
      (∀ i < 16 * 16, t.mem (off base (768 + i)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) / 2 ^ i) % 2)) ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
  rw [scalarBasePrepare]
  refine WP.mono (expandScalarBits_ok hs hp 32 (by decide) (by decide) hr hd) fun a ⟨ka, abits⟩ => ?_
  have kap : PowersKeep base 56 7368 s a := by
    refine ⟨fun r hb _ hr => ka.gpr r (fun hm => ?_), ka.rd, ka.wr, ka.sp,
      (TableFrame.table ka.mem).mono (by decide) (by decide)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hr (by decide)
    · exact hb rfl
    · exact hr (by decide)
  have hscalar : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32) < 2 ^ (16 * 16) := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt s.mem k 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at h
    rw [show 256 ^ 32 = 2 ^ (16 * 16) by decide] at h
    exact h
  exact ⟨kap, abits, hscalar⟩

theorem scalarBaseEngine_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa scalarBaseEngine s fun t => PowersKeep base 56 7368 s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        VG.Proof.Ed25519.AArch64.encodedValue (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint) := by
  rw [scalarBaseEngine]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, bbits, hscalar⟩ => ?_)
  refine WP.seq (WP.mono (combMultiply_ok (kab.scratch hs) (by simpa using hscalar) bbits)
    fun c ⟨cp, kc⟩ => ?_)
  refine WP.mono (pointEncode_ok (kc.scr (kab.scratch hs))) fun t ⟨kt, tv⟩ => ?_
  refine ⟨(kab.trans kc.powers).trans
    ⟨fun r hb _ hr => kt.gpr r hr hb, kt.rd, kt.wr, kt.sp, TableFrame.workspace kt.mem⟩, ?_⟩
  change val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = VG.Proof.Ed25519.AArch64.encodedValue (point (env c.mem base) 0 1 2 3) at tv
  rw [tv]
  exact VG.Proof.Ed25519.AArch64.encodedValue_rep cp (pointMul_rep _ basePoint_rep)

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseCTEngine`. -/
section

/-! Expanding the secret scalar's bits, the comb and the encoding have a public
trace. The loops' counters (`x19`, and `x1` for the doublings) and the table index are
public, every address is the workspace pointer `x0` plus a constant or a counter, and the
digits only reach masks: one taint check covers the whole engine. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def BaseEnginePre (base k : Addr) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    ∀ q < 32, 8192 ≤ ofs base (off k q)

theorem scalarBaseEngine_ct (base k : Addr) :
    VG.Proof.Ed25519.AArch64.CT (fun x y => VG.Proof.Ed25519.AArch64.BaseEnginePre base k x ∧ VG.Proof.Ed25519.AArch64.BaseEnginePre base k y)
      scalarBaseEngine (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0, .x1]) _
    (Taint.isSome_check_of_eraseImm VG.Proof.Ed25519.AArch64.scalarBaseEngine_eraseImm (by taint_decide))
  intro x y h
  apply VG.Proof.Ed25519.AArch64.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.x0.trans h.2.1.x0.symm
  · exact h.1.2.1.trans h.2.2.1.symm

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.ScalarBaseMemory`. -/
section
/-! Output pointer and saved registers remain outside the point workspace. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem scalarBaseSetup_ok (s : State) (hw : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarBaseSetup) s fun t => t.gpr .x0 = s.gpr .x2 ∧
      (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 ∧ Outside (s.gpr .x2) 48 8 s.mem t.mem := by
  have hw' : InRegions s.wr (off (s.gpr .x2) 48) 8 :=
    ⟨_, hw, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseSetup, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.store, addr, Size.bytes, mov, hw', Nat.reduceMod, Nat.reduceLT, Nat.reduceMul,
    and_self, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, ?_, ?_⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.mem_write, BitVec.setWidth_eq, write64_eq_writeW, Mem.readW_writeW_self64]
  · rw [RegUpd.mem_write, BitVec.setWidth_eq, write64_eq_writeW]
    exact writeW_outside _ _ _ (by decide)

theorem scalarBaseFinishArgs_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block scalarBaseFinishArgs) s fun t =>
      t.gpr .x2 = base ∧ t.gpr .x0 = s.mem.readW (off base 48) 64 ∧ Keeps [.x2, .x0] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 48) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  apply WP.of_runBlock
  simp only [scalarBaseFinishArgs, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    mov, ld, addr, Size.bytes, State.load,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs.x0, hr, BitVec.setWidth_eq, BitVec.add_zero, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bytesAt32_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) :
    Spec.Ed25519.bytesAt m' p 32 = Spec.Ed25519.bytesAt m p 32 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 32⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

end VG.Proof.Ed25519.AArch64
end

/-! Base-point multiplication satisfies its memory and ABI obligations. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64
open VG.Spec.Ed25519 (bytesAt)

def scalarBaseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x1, 32⟩] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .x0) 32 = Spec.Ed25519.scalarBase (bytesAt s.mem (s.gpr .x1) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

theorem farScr {base p : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    8192 ≤ ofs base (off p i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  change (off p i - base).toNat + 1 ≤ 8192
  change (off p i - base).toNat < 8192 at h
  omega

theorem scalarBase_correct {s : State} (hs : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  apply WP.withPreservedV
    (hc := Code.allInstrs_keepsV_of_eraseImm VG.Proof.Ed25519.AArch64.scalarBase_eraseImm (by lit_decide))
  obtain ⟨hr, hw, hd, hn⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBase]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, spa, ma, sva⟩ => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, spb, ob, mb⟩ => ?_
  rw [ga] at pb ob mb
  have hb : Scr b (s.gpr .x2) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .x2, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .x2) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .x1) 32 = bytesAt s.mem (s.gpr .x1) 32 := VG.Proof.Ed25519.AArch64.bytesAt32_frame fm hd
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarBaseEngine_ok hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .x1, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun q hq => VG.Proof.Ed25519.AArch64.farScr hd hq (by decide))) fun c ⟨kc, vc⟩ => ?_
  have mc := VG.Proof.Ed25519.AArch64.powersKeep_outside kc
  have svc : Saved (s.gpr .x2) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have x2d : d.gpr .x2 = s.gpr .x2 := pd
  have x0d : d.gpr .x0 = s.gpr .x0 := od.trans oc
  have wd : d.wr = s.wr := kd.wr.trans wc
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) x2d (wd ▸ hws) (by rw [kd.mem]; exact svc))
    fun e ⟨re, ke⟩ => ?_
  have x0e : e.gpr .x0 = s.gpr .x0 := (ke.gpr _ (by decide)).trans x0d
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ e.wr := by rw [ke.wr, wd, hw]; simp
  refine WP.mono (scalarOut_ok x0e hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.x19, 0) (by decide)
    · exact re (.x20, 8) (by decide)
    · exact re (.x21, 16) (by decide)
    · exact re (.x22, 24) (by decide)
    · exact re (.x23, 32) (by decide)
    · exact re (.x24, 40) (by decide)
    all_goals
      rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
  · exact ke.sp.trans (kd.sp.trans (kc.sp.trans (spb.trans spa)))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarBase, VG.Proof.Ed25519.AArch64.encodedValue_spec, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [val4, ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide), ke.gpr .x7 (by decide),
      kd.gpr .x4 (by decide), kd.gpr .x5 (by decide), kd.gpr .x6 (by decide), kd.gpr .x7 (by decide)]
    change val4 (c.gpr .x4) (c.gpr .x5) (c.gpr .x6) (c.gpr .x7) = _
    rw [vc, input]

end VG.Proof.Ed25519.AArch64

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.ScalarBaseCT`. -/
section
/-! Public argument pointers survive the secret point arithmetic. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

private def BaseStart (base k out : Addr) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .x0 = out ∧ s.gpr .x1 = k ∧ s.gpr .x2 = base

private def BasePrepared (base k out : Addr) (s : State) : Prop :=
  BaseEnginePre base k s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out : Addr} {s : State} (hs : BaseStart base k out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out) := by
  obtain ⟨⟨hr, hw, hd, hn⟩, ho, hk, hb⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, _, _⟩ => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, _, ob, _⟩ => ?_
  rw [ga, hb] at pb ob
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_⟩, ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScr hd hq (by decide)

private theorem start_ct (base k out : Addr) :
    CT (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y) := by
  have hc : CT (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1, .x2]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {base k out : Addr} {s : State} (hs : BasePrepared base k out s) :
    WP isa scalarBaseEngine s (BaseReady base out) := by
  refine WP.mono (scalarBaseEngine_ok hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct (base k out : Addr) :
    CT (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y)
      scalarBaseEngine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (scalarBaseEngine_ct base k).mono
    (fun _ _ (h : BasePrepared base k out _ ∧ BasePrepared base k out _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready h.1, engine_ready h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .x2 = base ∧ t.gpr .x0 = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine CT.seq hc' ?_
  apply CT.taint (Taint.ofRegs [.x2, .x0]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  intro x y tx ty x' y' hx hy ⟨hsp, ho, hk, hb⟩ ex ey
  have hc := CT.seq (start_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0))
    (CT.seq (engine_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0))
      (finish_ct (x.gpr .x2) (x.gpr .x0)))
  exact (hc _ _ _ _ _ _ ⟨hsp, ⟨hx, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm⟩⟩ ex ey).1

end VG.Proof.Ed25519.AArch64
end

/-! Base-point multiplication satisfies the merged specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def baseSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := scalarBase_correct hs

theorem scalarBase_verified : Verified AArch64.target scalarBase (Spec.Ed25519.scalarBaseContract AArch64.abi) :=
  Verified.of_correct scalarBase_ok scalarBase_ct (by
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, scalarBaseLocal]
      [baseSatState] using baseSatState)

end VG.Proof.Ed25519.AArch64

end
