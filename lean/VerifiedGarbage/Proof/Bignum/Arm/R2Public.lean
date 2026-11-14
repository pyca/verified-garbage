module

public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.R2

import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # `R² mod n` for a public modulus, from its top bit

The doublings start at `2^(64 (w - 1) + j)` for the top bit `j` of `n`'s top
word `T` (`r2PublicStart`), below the odd `n`, and are `w + 1 + (63 - j)`
(`r2PublicCount`), which reach `2^(64 w + w)` (`r2PublicStart_mul`); for
`T = 0`, `r2`'s `65 w` from 1. `bitFind` finds `j` within a half of `T`.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_dp wp_mov wp_str wp_cmp op2_imm op2_reg op2_lsl op2_lsr dpVal)

/-! ## The counts -/

/-- `n`'s top word. -/
def topWordOf (w M : Nat) : Nat := M / 2 ^ (64 * (w - 1))

/-- The doublings: `w + 1 + (63 - j)` from the top bit `j` of the top word,
or `65 w` from 1 if it is zero. -/
def r2PublicCount (w M : Nat) : Nat :=
  if topWordOf w M = 0 then 65 * w else w + 1 + (63 - Nat.log2 (topWordOf w M))

/-- Where they start. -/
def r2PublicStart (w M : Nat) : Nat :=
  if topWordOf w M = 0 then 1 else 2 ^ (64 * (w - 1) + Nat.log2 (topWordOf w M))

theorem topWordOf_lt {w M : Nat} (hw : 1 ≤ w) (hM : M < 2 ^ (64 * w)) : topWordOf w M < 2 ^ 64 := by
  unfold topWordOf
  refine Nat.div_lt_of_lt_mul ?_
  rw [← Nat.pow_add]
  exact Nat.lt_of_lt_of_le hM (Nat.pow_le_pow_right (by decide) (by omega))

theorem r2PublicStart_mul {w M : Nat} (hw : 1 ≤ w) (hM : M < 2 ^ (64 * w)) :
    2 ^ r2PublicCount w M * r2PublicStart w M = 2 ^ (64 * w + w) := by
  unfold r2PublicCount r2PublicStart
  split
  · rw [Nat.mul_one]; congr 1; omega_using []
  · rename_i h
    have := (Nat.log2_lt h).mpr (topWordOf_lt hw hM)
    rw [← Nat.pow_add]; congr 1; omega_using [hw, this]

theorem r2PublicStart_lt {w M : Nat} (hw : 2 ≤ w) (large : 1 < M) (odd : M % 2 = 1) :
    r2PublicStart w M < M := by
  unfold r2PublicStart
  split
  · exact large
  · rename_i h
    have le : 2 ^ (64 * (w - 1) + Nat.log2 (topWordOf w M)) ≤ M := by
      rw [Nat.pow_add, Nat.mul_comm]
      exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.log2_self_le h)) (Nat.div_mul_le_self M _)
    refine Nat.lt_of_le_of_ne le fun e => ?_
    have even : 2 ^ (64 * (w - 1) + Nat.log2 (topWordOf w M)) % 2 = 0 := by
      rw [show 64 * (w - 1) + Nat.log2 (topWordOf w M) = (64 * (w - 1) + Nat.log2 (topWordOf w M) - 1) + 1 by
        omega_using [hw], Nat.pow_succ, Nat.mul_mod_left]
    omega_using [odd, e, even]

theorem r2PublicCount_le {w M : Nat} (hw : 1 ≤ w) : 0 < r2PublicCount w M ∧ r2PublicCount w M ≤ 65 * w := by
  unfold r2PublicCount
  split <;> omega_using [hw]

/-! ## A half's top bit -/

/-- Below `2^(k+1)`, bit `k` is clear iff the number is below `2^k`. -/
theorem and_two_pow_eq_zero {v k : Nat} (hv : v < 2 ^ (k + 1)) : v &&& 2 ^ k = 0 ↔ v < 2 ^ k := by
  constructor
  · intro h
    refine Nat.lt_of_not_le fun hk => ?_
    have bit : v.testBit k = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
      have one : v / 2 ^ k = 1 := by
        refine Nat.le_antisymm ?_ ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega_using [hk]))
        exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by rw [Nat.pow_succ] at hv; omega_using [hv]))
      rw [one]
    have := Nat.testBit_and v (2 ^ k) k
    rw [h, Nat.zero_testBit, bit, Nat.testBit_two_pow_self] at this
    exact absurd this (by decide)
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
    by_cases e : k = i
    · subst e; rw [Nat.testBit_lt_two_pow h]; rfl
    · simp [e]

theorem and_cmp_zero (x y : BitVec 32) :
    ((x &&& y) - 0 == 0) = decide (x.toNat &&& y.toNat = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show ∀ z : BitVec 32, z - 0 = z from fun z => BitVec.sub_zero z,
    ← BitVec.toNat_inj, BitVec.toNat_and]
  rfl

/-- The search's state at bit `k`, with `v` below `2^k`. -/
structure BitAt (s0 : State) (v c k : Nat) (t : State) : Prop where
  bit : (t.gpr .r2).toNat = 2 ^ k
  below : v < 2 ^ k
  le : k ≤ 31
  count : t.gpr .r1 = BitVec.ofNat 32 (c + (31 - k))
  half : t.gpr .r5 = s0.gpr .r5
  mem : t.mem = s0.mem
  rest : Rest [.r1, .r2, .r3] s0 t

theorem log2_of_bounds {v j : Nat} (lo : 2 ^ j ≤ v) (hi : v < 2 ^ (j + 1)) : Nat.log2 v = j :=
  (Nat.log2_eq_iff (by have := Nat.one_le_two_pow (n := j); omega_using [lo, hi])).mpr ⟨lo, hi⟩

theorem bitFind_ok (s : State) {v c : Nat} (hv : (s.gpr .r5).toNat = v) (pos : 0 < v)
    (count : s.gpr .r1 = BitVec.ofNat 32 c) :
    WP isa bitFind s fun t => (t.gpr .r2).toNat = 2 ^ Nat.log2 v ∧
      t.gpr .r1 = BitVec.ofNat 32 (c + (31 - Nat.log2 v)) ∧ t.gpr .r5 = s.gpr .r5 ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3] s t := by
  have hlt : v < 2 ^ 32 := hv ▸ (s.gpr .r5).isLt
  rw [bitFind, WP.seq_iff]
  unfold bitTest
  refine wp_mov (op2_imm (by decide)) fun a ha => ?_
  refine wp_dp (op2_reg _ _) fun b hb => ?_
  refine wp_cmp (op2_imm (by decide)) fun t0 ht z => WP.block_nil ?_
  have r2t : (t0.gpr .r2).toNat = 2 ^ 31 := by rw [ht.gpr, hb.other .r2 (by decide), ha.gpr]; rfl
  have r5t : t0.gpr .r5 = s.gpr .r5 := by rw [ht.gpr, hb.other .r5 (by decide), ha.other .r5 (by decide)]
  have r1t : t0.gpr .r1 = s.gpr .r1 := by rw [ht.gpr, hb.other .r1 (by decide), ha.other .r1 (by decide)]
  have z' : t0.z = decide (v < 2 ^ 31) := by
    rw [z, hb.gpr, dpVal, ha.other .r5 (by decide), ha.gpr, and_cmp_zero, hv]
    exact decide_eq_decide.mpr (and_two_pow_eq_zero (k := 31) hlt)
  have mem0 : t0.mem = s.mem := ht.mem.trans (hb.mem.trans ha.mem)
  have rest0 : Rest [.r1, .r2, .r3] s t0 :=
    (ha.rest (by decide)).trans ((hb.rest (by decide)).trans (ht.rest _))
  by_cases top : v < 2 ^ 31
  · refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, z', decide_eq_true top]) (fun _ => ?_) (by simp)
    refine WP.loop (M := isa) (fun k t => BitAt s v c k t) (fun k t h => ?_) 31 t0
      ⟨r2t, top, Nat.le_refl _, by rw [r1t, count, Nat.sub_self, Nat.add_zero], r5t, mem0, rest0⟩
    have k1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with e | e
      · have := h.below; rw [e] at this; omega
      · exact e
    unfold bitStep
    refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun a1 h1 => ?_
    refine wp_dp (op2_imm (by decide)) fun a2 h2 => ?_
    refine wp_dp (op2_reg _ _) fun a3 h3 => ?_
    refine wp_cmp (op2_imm (by decide)) fun u hu zu => WP.block_nil ?_
    have r2u : (u.gpr .r2).toNat = 2 ^ (k - 1) := by
      rw [hu.gpr, h3.other .r2 (by decide), h2.other .r2 (by decide), h1.gpr, BitVec.toNat_ushiftRight,
        h.bit, Nat.shiftRight_eq_div_pow, show k = (k - 1) + 1 by omega_using [k1], Nat.pow_succ, Nat.pow_one,
        Nat.mul_div_cancel _ (by decide)]
      congr 1
    have r5u : u.gpr .r5 = s.gpr .r5 := by
      rw [hu.gpr, h3.other .r5 (by decide), h2.other .r5 (by decide), h1.other .r5 (by decide), h.half]
    have r1u : u.gpr .r1 = BitVec.ofNat 32 (c + (31 - (k - 1))) := by
      rw [hu.gpr, h3.other .r1 (by decide), h2.gpr, dpVal, h1.other .r1 (by decide), h.count]
      change BitVec.ofNat 32 _ + BitVec.ofNat 32 1 = _
      rw [← BitVec.ofNat_add]
      congr 1; have := h.le; omega_using [k1, this]
    have below : v < 2 ^ (k - 1 + 1) := by rw [show k - 1 + 1 = k by omega_using [k1]]; exact h.below
    have zk : u.z = decide (v < 2 ^ (k - 1)) := by
      rw [zu, h3.gpr, dpVal, h2.other .r5 (by decide), h1.other .r5 (by decide), h2.other .r2 (by decide),
        and_cmp_zero, h.half, hv, show (a1.gpr .r2).toNat = 2 ^ (k - 1) by
          rw [← r2u, hu.gpr, h3.other .r2 (by decide), h2.other .r2 (by decide)]]
      exact decide_eq_decide.mpr (and_two_pow_eq_zero below)
    have memu : u.mem = s.mem := hu.mem.trans (h3.mem.trans (h2.mem.trans (h1.mem.trans h.mem)))
    have restu : Rest [.r1, .r2, .r3] s u :=
      h.rest.trans ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans ((h3.rest (by decide)).trans
        (hu.rest _))))
    by_cases more : v < 2 ^ (k - 1)
    · right
      exact ⟨by rw [VG.Proof.X25519.Arm.eval_eq, zk, decide_eq_true more], k - 1, by omega_using [k1],
        ⟨r2u, more, by have := h.le; omega_using [this], r1u, r5u, memu, restu⟩⟩
    · left
      have log : Nat.log2 v = k - 1 := log2_of_bounds (Nat.le_of_not_lt more) below
      refine ⟨by rw [VG.Proof.X25519.Arm.eval_eq, zk, decide_eq_false more], ?_, ?_, r5u, memu, restu⟩
      · rw [r2u, log]
      · rw [r1u, log]
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, z', decide_eq_false top]) (by simp)
      (fun _ => WP.block_nil ?_)
    have log : Nat.log2 v = 31 := log2_of_bounds (Nat.le_of_not_lt top) hlt
    exact ⟨by rw [r2t, log], by rw [r1t, count, log, Nat.sub_self, Nat.add_zero], r5t, mem0, rest0⟩

/-! ## The top word in memory -/

/-- One 32-bit word written into a zero number. -/
theorem val32_write_of_zero (m : Mem) (base : Addr) {d n i : Nat} (hi : i < n) (fit : d + 4 * n < 2 ^ 64)
    (zero : val32 m base d n = 0) (v : BitVec 32) :
    val32 (m.writeW (off base (d + 4 * i)) v) base d n = 2 ^ (32 * i) * v.toNat := by
  have split : n = i + ((n - i - 1) + 1) := by omega_using [hi]
  have outside := writeW32_outside m base (d := d + 4 * i) v (by omega_using [hi, fit])
  rw [split, val32_append, val32] at zero ⊢
  have low : val32 m base d i = 0 := by omega_using [zero]
  have pos := Nat.two_pow_pos (32 * i)
  have high : val32 m base (d + 4 * i + 4) (n - i - 1) = 0 := by
    rcases Nat.mul_eq_zero.mp (show 2 ^ (32 * i) * (w32 m base (d + 4 * i) +
      2 ^ 32 * val32 m base (d + 4 * i + 4) (n - i - 1)) = 0 by omega_using [zero]) with h | h
    · omega_using [pos, h]
    · omega_using [h]
  rw [outside.val32 (d := d) (k := i) (by omega_using []) (by omega_using [hi, fit]), low, w32_write_self,
    outside.val32 (d := d + 4 * i + 4) (k := n - i - 1) (by omega_using []) (by omega_using [hi, fit]), high, Nat.mul_zero, Nat.add_zero,
    Nat.zero_add]

/-- `n`'s top word is its array 0's last two 32-bit words. -/
theorem topWord_halves (m : Mem) (base : Addr) {w M : Nat} (hw : 1 ≤ w) (h : numAt m base w 0 = M) :
    w32 m base (arrAt w 0 + 8 * w - 8) + 2 ^ 32 * w32 m base (arrAt w 0 + 8 * w - 4) = topWordOf w M := by
  rw [numAt_native, show 2 * w = (2 * w - 2) + 1 + 1 by omega_using [hw], val32_succ, val32_succ] at h
  have lo := val32_lt m base (arrAt w 0) (2 * w - 2)
  unfold topWordOf
  rw [← h, show 64 * (w - 1) = 32 * (2 * w - 2) by omega_using [],
    show arrAt w 0 + 4 * (2 * w - 2) = arrAt w 0 + 8 * w - 8 by omega_using [hw],
    show arrAt w 0 + 4 * (2 * w - 2 + 1) = arrAt w 0 + 8 * w - 4 by omega_using [hw],
    show 2 ^ (32 * (2 * w - 2 + 1)) = 2 ^ (32 * (2 * w - 2)) * 2 ^ 32 by rw [← Nat.pow_add]; congr 1,
    Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt lo, Nat.zero_add]

/-- The top word's top bit, in its high half. -/
theorem log2_high {l h : Nat} (hh : h ≠ 0) (hl : l < 2 ^ 32) :
    Nat.log2 (l + 2 ^ 32 * h) = 32 + Nat.log2 h := by
  have lo := Nat.log2_self_le hh
  have hi : h < 2 ^ (Nat.log2 h + 1) := Nat.lt_log2_self
  refine log2_of_bounds ?_ ?_
  · rw [Nat.pow_add]; exact Nat.le_add_left_of_le (Nat.mul_le_mul_left _ lo)
  · rw [show 32 + Nat.log2 h + 1 = 32 + (Nat.log2 h + 1) by omega_using [], Nat.pow_add]
    have := Nat.mul_le_mul_left (2 ^ 32) (show h + 1 ≤ 2 ^ (Nat.log2 h + 1) by omega_using [hi])
    rw [Nat.mul_add] at this
    omega_using [hl, hi]

/-! ## The blocks -/

theorem or_cmp_zero (x y : BitVec 32) :
    ((x ||| y) - 0 == 0) = decide (x.toNat = 0 ∧ y.toNat = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show ∀ z : BitVec 32, z - 0 = z from fun z => BitVec.sub_zero z,
    ← BitVec.toNat_inj, BitVec.toNat_or]
  exact Nat.or_eq_zero_iff

theorem cmp_zero (x : BitVec 32) : (x - 0 == 0) = decide (x.toNat = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, show ∀ z : BitVec 32, z - 0 = z from fun z => BitVec.sub_zero z,
    ← BitVec.toNat_inj]
  rfl

theorem shl3_ofNat (x : Nat) : BitVec.ofNat 32 x <<< 3 = BitVec.ofNat 32 (8 * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod,
    Nat.mul_comm]

theorem topPointers_ok (s : State) {base : BitVec 32} {len w : Nat} (h : ArithmeticReady base len w s) :
    WP isa (.block topPointers) s fun t => t.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 0) ∧
      t.gpr .r1 = BitVec.ofNat 32 w ∧ t.mem = s.mem ∧ Rest [.r1, .r6] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have nowrap := h.workspace.nowrap
  unfold topPointers
  refine wp_ldr (a := off (State.addr base) 64) (by decide) (by rw [h.ptr]; exact addr_add (by omega_using [size, nowrap]))
    (h.workspace.read (by omega_using [size])) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [a.other .r0 (by decide), h.ptr]; exact addr_add (by omega_using [size, nowrap]))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega_using [size])) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.other .r6 (by decide), a.gpr]; exact header.array 0 (by decide),
    by rw [b.gpr, a.mem]; exact header.count, b.mem.trans a.mem, (a.rest (by decide)).trans (b.rest (by decide))⟩

theorem topWord_ok (s : State) {base : BitVec 32} {len w : Nat} (h : ArithmeticReady base len w s)
    (r6 : s.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 0)) (r1 : s.gpr .r1 = BitVec.ofNat 32 w) :
    WP isa (.block topWord) s fun t =>
      t.gpr .r4 = BitVec.ofNat 32 (8 * w - 8) ∧
      t.gpr .r3 = s.mem.readW (off (State.addr base) (arrAt w 0 + 8 * w - 8)) 32 ∧
      t.gpr .r5 = s.mem.readW (off (State.addr base) (arrAt w 0 + 8 * w - 4)) 32 ∧
      t.z = decide (w32 s.mem (State.addr base) (arrAt w 0 + 8 * w - 8) = 0 ∧
        w32 s.mem (State.addr base) (arrAt w 0 + 8 * w - 4) = 0) ∧
      t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r5, .r6] s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have end0 := Nat.le_trans (array_end_le (w := w) (by decide : 0 < 8)) fits
  have nowrap := h.workspace.nowrap
  unfold topWord
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun a ha => ?_
  refine wp_dp (op2_imm (by decide)) fun b hb => ?_
  refine wp_dp (op2_reg _ _) fun c hc => ?_
  have r4b : b.gpr .r4 = BitVec.ofNat 32 (8 * w - 8) := by
    rw [hb.gpr, dpVal, ha.gpr, r1, shl3_ofNat]
    exact VG.Offset.ofNat_sub_ofNat (show 8 ≤ 8 * w by omega_using [hw])
  have r4c : c.gpr .r4 = BitVec.ofNat 32 (8 * w - 8) := by rw [hc.other .r4 (by decide), r4b]
  have r6c : c.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 0 + 8 * w - 8) := by
    rw [hc.gpr, dpVal, hb.other .r6 (by decide), ha.other .r6 (by decide), r6, r4b, BitVec.add_assoc,
      ← BitVec.ofNat_add, show arrAt w 0 + 8 * w - 8 = arrAt w 0 + (8 * w - 8) by omega_using [hw]]
  have memc : c.mem = s.mem := hc.mem.trans (hb.mem.trans ha.mem)
  refine wp_ldr (a := off (State.addr base) (arrAt w 0 + 8 * w - 8)) (by decide)
    (by rw [r6c, BitVec.add_zero]; exact addr_add (by omega_using [end0, nowrap]))
    (by rw [hc.rd, hc.wr, hb.rd, hb.wr, ha.rd, ha.wr]; exact h.workspace.read (by omega_using [end0])) fun d hd => ?_
  refine wp_ldr (a := off (State.addr base) (arrAt w 0 + 8 * w - 4)) (by decide)
    (by rw [hd.other .r6 (by decide), r6c, BitVec.add_assoc, ← BitVec.ofNat_add,
      show arrAt w 0 + 8 * w - 8 + 4 = arrAt w 0 + 8 * w - 4 by omega_using [hw]]; exact addr_add (by omega_using [end0, nowrap]))
    (by rw [hd.rd, hd.wr, hc.rd, hc.wr, hb.rd, hb.wr, ha.rd, ha.wr]; exact h.workspace.read (by omega_using [end0]))
    fun e he => ?_
  refine wp_dp (op2_reg _ _) fun f hf => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht z => WP.block_nil ?_
  have r3e : e.gpr .r3 = s.mem.readW (off (State.addr base) (arrAt w 0 + 8 * w - 8)) 32 := by
    rw [he.other .r3 (by decide), hd.gpr, memc]
  have r5e : e.gpr .r5 = s.mem.readW (off (State.addr base) (arrAt w 0 + 8 * w - 4)) 32 := by
    rw [he.gpr, hd.mem, memc]
  refine ⟨by rw [ht.gpr, hf.other .r4 (by decide), he.other .r4 (by decide), hd.other .r4 (by decide)]; exact r4c,
    by rw [ht.gpr, hf.other .r3 (by decide)]; exact r3e, by rw [ht.gpr, hf.other .r5 (by decide)]; exact r5e,
    by rw [z, hf.gpr, dpVal, r3e, r5e, or_cmp_zero],
    ht.mem.trans (hf.mem.trans (he.mem.trans (hd.mem.trans memc))),
    (ha.rest (by decide)).trans ((hb.rest (by decide)).trans ((hc.rest (by decide)).trans ((hd.rest (by decide)).trans
      ((he.rest (by decide)).trans ((hf.rest (by decide)).trans (ht.rest _))))))⟩

/-- `b` stored at 32-bit word `i` of the zeroed array 4, and the count
`c + 1`: the doublings' state. -/
theorem topStore_ready (s : State) {base : BitVec 32} {len w i c : Nat} {b : BitVec 32}
    (h : ArithmeticReady base len w s) (zero : numAt s.mem (State.addr base) w 4 = 0)
    (two : w32 s.mem (State.addr base) (arrAt w 7) = 2) (hi : i < 2 * w)
    (r4 : s.gpr .r4 = BitVec.ofNat 32 (4 * i)) (r2 : s.gpr .r2 = b) (r1 : s.gpr .r1 = BitVec.ofNat 32 c)
    (bound : 2 ^ (32 * i) * b.toNat < numAt s.mem (State.addr base) w 0) :
    WP isa (.block topStore) s fun t => DoubleLoopReady base len w (c + 1) t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (32 * i) * b.toNat ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have end4 := Nat.le_trans (array_end_le (w := w) (by decide : 4 < 8)) fits
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have nowrap := h.workspace.nowrap
  have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  unfold topStore
  refine wp_ldr (a := off (State.addr base) 96) (by decide) (by rw [h.ptr]; exact addr_add (by omega_using [size, nowrap]))
    (h.workspace.read (by omega_using [size])) fun a ha => ?_
  refine wp_dp (op2_reg _ _) fun b' hb => ?_
  have r6b : b'.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 4 + 4 * i) := by
    rw [hb.gpr, dpVal, ha.gpr, header.array 4 (by decide), ha.other .r4 (by decide), r4, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  refine wp_str (a := off (State.addr base) (arrAt w 4 + 4 * i)) (by decide)
    (by rw [r6b, BitVec.add_zero]; exact addr_add (by omega_using [hi, end4, nowrap]))
    (by rw [hb.wr, ha.wr]; exact h.workspace.write (by omega_using [hi, end4])) fun c' hc => ?_
  refine wp_dp (op2_imm (by decide)) fun d hd => ?_
  have r0d : d.gpr .r0 = base := by
    rw [hd.other .r0 (by decide), hc.gpr, hb.other .r0 (by decide), ha.other .r0 (by decide), h.ptr]
  refine wp_str (a := off (State.addr base) 208) (by decide) (by rw [r0d]; exact addr_add (by omega_using [size, nowrap]))
    (by rw [hd.wr, hc.wr, hb.wr, ha.wr]; exact h.workspace.write (by omega_using [size])) fun t ht => WP.block_nil ?_
  have memc : c'.mem = s.mem.writeW (off (State.addr base) (arrAt w 4 + 4 * i)) b := by
    rw [hc.mem, hb.mem, ha.mem, hb.other .r2 (by decide), ha.other .r2 (by decide), r2]
  have outside := writeW32_outside s.mem (State.addr base) (d := arrAt w 4 + 4 * i) b (by omega_using [hi, end4, nowrap])
  rw [← memc] at outside
  have arrayOutside := outside.mono (o' := arrAt w 4) (n' := 8 * w) (by omega_using []) (by omega_using [hi])
  have keeps := outside_array_keeps arrayOutside (len := len) (by omega_using [nowrap])
  have frame := outside_workspace arrayOutside (size := 8 * len) (by omega_using [end4])
  have restc : Rest roundClobbers s c' :=
    ((ha.rest (ws := [.r6]) (by decide)).trans ((hb.rest (ws := [.r6]) (by decide)).trans (hc.rest _))).mono
      (by decide)
  have ready := h.after_array (by decide : 4 ≠ 0) keeps frame restc
    (by rw [hc.gpr, hb.other .r0 (by decide), ha.other .r0 (by decide), h.ptr])
  have value : numAt c'.mem (State.addr base) w 4 = 2 ^ (32 * i) * b.toNat := by
    rw [numAt_native, memc]
    exact val32_write_of_zero s.mem _ hi (by omega_using [end4, nowrap]) (by rw [← numAt_native]; exact zero) b
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have twoC : w32 c'.mem (State.addr base) (arrAt w 7) = 2 := by
    have := keeps_array_word (d := 0) (bits := 32) keeps fits op7 (by decide) (by omega_using [])
    simp only [Nat.add_zero] at this
    change (c'.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [this]; exact two
  have dc : DoubleLoopReady base len w (c'.mem.readW (off (State.addr base) 208) 32).toNat c' :=
    ⟨ready.1.workspace, ready.1.layout, ready.1.width, ready.1.ptr, ready.1.inverse,
      by rw [value, ready.2]; exact bound, twoC, by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      ready.1.stackRead, ready.1.stackSep, ready.1.saved⟩
  have r1d : d.gpr .r1 = BitVec.ofNat 32 (c + 1) := by
    rw [hd.gpr, dpVal, hc.gpr, hb.other .r1 (by decide), ha.other .r1 (by decide), r1]
    change BitVec.ofNat 32 c + BitVec.ofNat 32 1 = _
    rw [← BitVec.ofNat_add]
  obtain ⟨dt, ft, n4, n0⟩ := dc.after_count (t := t) (c' := c + 1) (by rw [ht.mem, hd.mem, r1d])
    ((hd.rest (by decide)).trans (ht.rest _))
  exact ⟨dt, n4.trans value, n0.trans ready.2, frame.trans ft,
    restc.trans (((hd.rest (ws := [.r1]) (by decide)).trans (ht.rest _)).mono (by decide))⟩

/-! ## The initialization -/

structure R2PublicInitialized (base : BitVec 32) (len w M : Nat) (s : State) : Prop where
  ready : DoubleLoopReady base len w (r2PublicCount w M) s
  value : numAt s.mem (State.addr base) w 4 = r2PublicStart w M
  modulus : numAt s.mem (State.addr base) w 0 = M
  large : 1 < M

/-- The search and the store, for a half `v` at 32-bit word `i` of the top word. -/
theorem topFinish_ok (s : State) {base : BitVec 32} {len w M i c v : Nat}
    (h : ArithmeticReady base len w s) (zero : numAt s.mem (State.addr base) w 4 = 0)
    (two : w32 s.mem (State.addr base) (arrAt w 7) = 2) (modulus : numAt s.mem (State.addr base) w 0 = M)
    (hi : i < 2 * w) (r4 : s.gpr .r4 = BitVec.ofNat 32 (4 * i)) (r1 : s.gpr .r1 = BitVec.ofNat 32 c)
    (r5 : (s.gpr .r5).toNat = v) (pos : 0 < v)
    (count : c + (31 - Nat.log2 v) + 1 = r2PublicCount w M)
    (start : 2 ^ (32 * i) * 2 ^ Nat.log2 v = r2PublicStart w M) :
    WP isa (.seq bitFind (.block topStore)) s fun t => R2PublicInitialized base len w M t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have large : 1 < M := modulus ▸ h.modulus
  have odd : M % 2 = 1 := modulus ▸ numAt_odd_of_inverse s.mem _ (by omega_using [hi]) h.inverse
  rw [WP.seq_iff]
  refine WP.mono (bitFind_ok s r5 pos r1) ?_
  rintro u ⟨r2u, r1u, _, mem, rest⟩
  have ready := h.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ptr)
  have bound : 2 ^ (32 * i) * (u.gpr .r2).toNat < numAt u.mem (State.addr base) w 0 := by
    rw [r2u, start, mem, modulus]; exact r2PublicStart_lt hw large odd
  refine WP.mono (topStore_ready u ready (by rw [mem]; exact zero) (by rw [mem]; exact two) hi
    (by rw [rest.gpr .r4 (by decide)]; exact r4) rfl r1u bound) ?_
  rintro t ⟨d, value, mod, frame, restT⟩
  rw [r2u, start] at value
  rw [count] at d
  exact ⟨⟨d, value, by rw [mod, mem, modulus], large⟩, by rw [← mem]; exact frame,
    (rest.mono (by decide)).trans restT⟩

theorem r2PublicInit_ok (s : State) {base : BitVec 32} {len w M : Nat}
    (h : ArithmeticReady base len w s) (initialM : numAt s.mem (State.addr base) w 0 = M) :
    WP isa r2PublicInit s fun t => R2PublicInitialized base len w M t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have large : 1 < M := initialM ▸ h.modulus
  have op (i : Nat) (hi : i = 0 ∨ i = 4) : Operand i := by
    rcases hi with rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [r2PublicInit, WP.seq_iff]
  refine WP.mono (smallConst_ok s (o := 4) 0 h (by decide) (by decide) (by decide) (by decide)) ?_
  rintro s1 ⟨ready1, zero1, _, keeps1, frame1, rest1⟩
  have mod1 := (keeps_array_num keeps1 fits (op 0 (by decide)) (by decide)).trans initialM
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok s1 (o := 7) 2 ready1 (by decide) (by decide) (by decide) (by decide)) ?_
  rintro s2 ⟨ready2, _, two2, keeps2, frame2, rest2⟩
  have mod2 := (keeps_array_num keeps2 fits (op 0 (by decide)) (by decide)).trans mod1
  have zero2 := (keeps_array_num keeps2 fits (op 4 (by decide)) (by decide)).trans zero1
  rw [WP.seq_iff]
  refine WP.mono (topPointers_ok s2 ready2) ?_
  rintro s3 ⟨r6, r1, mem3, rest3⟩
  have ready3 := ready2.of_mem mem3 rest3 ((rest3.gpr .r0 (by decide)).trans ready2.ptr)
  rw [WP.seq_iff]
  refine WP.mono (topWord_ok s3 ready3 r6 r1) ?_
  rintro s4 ⟨r4, r3, r5, z4, mem4, rest4⟩
  have ready4 := ready3.of_mem mem4 rest4 ((rest4.gpr .r0 (by decide)).trans ready3.ptr)
  have halves := topWord_halves s3.mem (State.addr base) (by omega_using [hw]) (show numAt s3.mem _ w 0 = M by
    rw [mem3]; exact mod2)
  have frame4 : Frame [⟨State.addr base, 8 * len⟩] s.mem s4.mem := by
    rw [mem4, mem3]; exact frame1.trans frame2
  have rest14 : Rest roundClobbers s s4 :=
    rest1.trans (rest2.trans ((rest3.mono (by decide)).trans (rest4.mono (by decide))))
  have mod4 : numAt s4.mem (State.addr base) w 0 = M := by rw [mem4, mem3]; exact mod2
  have zero4 : numAt s4.mem (State.addr base) w 4 = 0 := by rw [mem4, mem3]; exact zero2
  have two4 : w32 s4.mem (State.addr base) (arrAt w 7) = 2 := by rw [mem4, mem3]; exact two2.trans rfl
  generalize hL : w32 s3.mem (State.addr base) (arrAt w 0 + 8 * w - 8) = L at halves z4
  generalize hH : w32 s3.mem (State.addr base) (arrAt w 0 + 8 * w - 4) = H at halves z4
  have hL32 : L < 2 ^ 32 := hL ▸ BitVec.isLt _
  by_cases T0 : topWordOf w M = 0
  · have both : L = 0 ∧ H = 0 := by omega_using [halves, T0]
    refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, z4, decide_eq_true both]) (fun _ => ?_) (by simp)
    refine WP.mono (r2Init_ok s4 ready4) ?_
    rintro t ⟨ready, one, mod, frame, rest⟩
    refine ⟨⟨by simpa only [r2PublicCount, T0, ite_true] using ready,
      by simpa only [r2PublicStart, T0, ite_true] using one, mod.trans mod4, large⟩,
      frame4.trans frame, rest14.trans rest⟩
  · have notBoth : ¬ (L = 0 ∧ H = 0) := fun e => T0 (by omega_using [halves, e])
    refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, z4, decide_eq_false notBoth]) (by simp)
      (fun _ => ?_)
    rw [topInit, WP.seq_iff]
    unfold topHalf
    refine wp_dp (op2_imm (by decide)) fun a ha => ?_
    refine wp_cmp (op2_imm (by decide)) fun u hu zu => WP.block_nil ?_
    have restU : Rest [.r4] s4 u := (ha.rest (by decide)).trans (hu.rest _)
    have memU : u.mem = s4.mem := hu.mem.trans ha.mem
    have readyU := ready4.of_mem memU restU ((restU.gpr .r0 (by decide)).trans ready4.ptr)
    have r4u : u.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) := by
      rw [hu.gpr, ha.gpr, dpVal, r4]
      change BitVec.ofNat 32 _ + BitVec.ofNat 32 4 = _
      rw [← BitVec.ofNat_add, show 8 * w - 8 + 4 = 8 * w - 4 by omega_using [hw]]
    have r5u : u.gpr .r5 = s4.gpr .r5 := by rw [hu.gpr, ha.other .r5 (by decide)]
    have zH : u.z = decide (H = 0) := by
      rw [zu, ha.other .r5 (by decide), cmp_zero, r5, ← hH]
    have post (t : State) (ht : R2PublicInitialized base len w M t ∧
        Frame [⟨State.addr base, 8 * len⟩] u.mem t.mem ∧ Rest roundClobbers u t) :
        R2PublicInitialized base len w M t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
          Rest roundClobbers s t :=
      ⟨ht.1, frame4.trans (by rw [← memU]; exact ht.2.1), rest14.trans ((restU.mono (by decide)).trans ht.2.2)⟩
    rw [WP.seq_iff]
    by_cases H0 : H = 0
    · rw [H0, Nat.mul_zero, Nat.add_zero] at halves
      refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, zH, decide_eq_true H0]) (fun _ => ?_) (by simp)
      unfold lowHalf
      refine wp_dp (op2_imm (by decide)) fun b hb => ?_
      refine wp_mov (op2_reg _ _) fun c hc => ?_
      refine wp_dp (op2_imm (by decide)) fun d hd => WP.block_nil ?_
      have restD : Rest [.r1, .r4, .r5] u d :=
        (hb.rest (by decide)).trans ((hc.rest (by decide)).trans (hd.rest (by decide)))
      have memD : d.mem = u.mem := hd.mem.trans (hc.mem.trans hb.mem)
      have readyD := readyU.of_mem memD restD ((restD.gpr .r0 (by decide)).trans readyU.ptr)
      have Lpos : 0 < L := by have := Nat.pos_of_ne_zero T0; omega_using [halves, T0]
      have r4d : d.gpr .r4 = BitVec.ofNat 32 (4 * (2 * w - 2)) := by
        rw [hd.other .r4 (by decide), hc.other .r4 (by decide), hb.gpr, dpVal, r4u]
        change BitVec.ofNat 32 _ - BitVec.ofNat 32 4 = _
        rw [VG.Offset.ofNat_sub_ofNat (by omega_using [hw])]; congr 1; omega_using []
      have r1d : d.gpr .r1 = BitVec.ofNat 32 (w + 32) := by
        rw [hd.gpr, dpVal, hc.other .r1 (by decide), hb.other .r1 (by decide), restU.gpr .r1 (by decide),
          rest4.gpr .r1 (by decide), r1]
        change BitVec.ofNat 32 _ + BitVec.ofNat 32 32 = _
        rw [← BitVec.ofNat_add]
      have r5d : (d.gpr .r5).toNat = L := by
        rw [hd.other .r5 (by decide), hc.gpr, hb.other .r3 (by decide), restU.gpr .r3 (by decide), r3, ← hL]
      have logL : Nat.log2 L ≤ 31 := Nat.le_of_lt_succ ((Nat.log2_lt (by omega_using [Lpos])).mpr hL32)
      refine WP.mono (topFinish_ok d readyD (M := M) (i := 2 * w - 2) (c := w + 32) (v := L)
        (by rw [memD, memU]; exact zero4) (by rw [memD, memU]; exact two4) (by rw [memD, memU]; exact mod4)
        (by omega_using [hw])
        r4d r1d r5d Lpos
        (by simp only [r2PublicCount, T0, ite_false]; rw [← halves]; omega_using [logL])
        (by simp only [r2PublicStart, T0, ite_false]; rw [← halves, ← Nat.pow_add]; congr 1; omega_using [])) ?_
      intro t ht
      exact post t ⟨ht.1, by rw [← memD]; exact ht.2.1, (restD.mono (by decide)).trans ht.2.2⟩
    · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, zH, decide_eq_false H0]) (by simp)
        (fun _ => WP.block_nil ?_)
      have hH32 : H < 2 ^ 32 := hH ▸ BitVec.isLt _
      have logH : Nat.log2 H ≤ 31 := Nat.le_of_lt_succ ((Nat.log2_lt H0).mpr hH32)
      have logT : Nat.log2 (topWordOf w M) = 32 + Nat.log2 H := by rw [← halves]; exact log2_high H0 hL32
      refine WP.mono (topFinish_ok u readyU (M := M) (i := 2 * w - 1) (c := w) (v := H)
        (by rw [memU]; exact zero4) (by rw [memU]; exact two4) (by rw [memU]; exact mod4) (by omega_using [hw])
        (by rw [r4u]; congr 1; omega_using [])
        (by rw [restU.gpr .r1 (by decide), rest4.gpr .r1 (by decide)]; exact r1)
        (by rw [r5u, r5, ← hH]) (Nat.pos_of_ne_zero H0)
        (by simp only [r2PublicCount, T0, ite_false]; rw [logT]; omega_using [])
        (by simp only [r2PublicStart, T0, ite_false]; rw [logT, ← Nat.pow_add]; congr 1; omega_using [hw])) ?_
      exact fun t ht => post t ht

theorem r2PublicLoop_ok (s : State) {base : BitVec 32} {len w M : Nat}
    (h : R2PublicInitialized base len w M s) (countFits : 128 * w < 2 ^ 32) :
    WP isa doubleLoop s fun t => R2Sq base len w M w t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  obtain ⟨cpos, cle⟩ := r2PublicCount_le (w := w) (M := M) (by omega_using [hw])
  have hM : M < 2 ^ (64 * w) := by
    rw [← h.modulus, numAt_native, show 64 * w = 32 * (2 * w) by omega_using []]
    exact val32_lt _ _ _ _
  refine WP.mono (doubleLoop_ok s h.ready cpos (by omega_using [countFits, cle])) ?_
  rintro v ⟨done, value, modV, frameV, restV⟩
  rw [h.value, h.modulus, r2PublicStart_mul (by omega_using [hw]) hM] at value
  rw [h.modulus] at modV
  exact ⟨⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modV]; exact h.large, done.stackRead, done.stackSep, done.saved⟩,
    modV, modV ▸ done.operand, by rw [value, Nat.mod_mod], done.two, done.counter⟩,
    frameV, restV⟩

theorem r2Public_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) (countFits : 128 * w < 2 ^ 32) :
    WP isa r2Public s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2Public, WP.seq_iff]
  refine WP.mono (r2PublicInit_ok s h rfl) ?_
  rintro u ⟨ready, frame, rest⟩
  rw [WP.seq_iff]
  refine WP.mono (r2PublicLoop_ok u ready countFits) ?_
  rintro v ⟨sq, frameV, restV⟩
  refine WP.mono (r2Squares_ok v sq) ?_
  rintro t ⟨fin, frameT, restT⟩
  have value : numAt t.mem (State.addr base) w 4 =
      2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 := by
    rw [← Nat.mod_eq_of_lt fin.operand, fin.value, show 64 * w + 64 * w = 128 * w by omega_using []]
  exact ⟨⟨fin.ready.workspace, fin.ready.layout, fin.ready.width, fin.ready.ptr, fin.ready.inverse,
    by rw [fin.modulus]; exact fin.operand, fin.two, fin.counter,
    fin.ready.stackRead, fin.ready.stackSep, fin.ready.saved⟩,
    value, fin.modulus, frame.trans (frameV.trans frameT), rest.trans (restV.trans restT)⟩

/-! ## For the constant-time proof -/

/-- One step of the search, at bit `n`. -/
theorem bitStep_ok (s : State) {v n : Nat} (bit : (s.gpr .r2).toNat = 2 ^ n) (below : v < 2 ^ n)
    (r5 : (s.gpr .r5).toNat = v) (n1 : 1 ≤ n) :
    WP isa (.block bitStep) s fun u => (u.gpr .r2).toNat = 2 ^ (n - 1) ∧ u.z = decide (v < 2 ^ (n - 1)) ∧
      (u.gpr .r5).toNat = v := by
  unfold bitStep
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun a1 h1 => ?_
  refine wp_dp (op2_imm (by decide)) fun a2 h2 => ?_
  refine wp_dp (op2_reg _ _) fun a3 h3 => ?_
  refine wp_cmp (op2_imm (by decide)) fun u hu zu => WP.block_nil ?_
  have r2a : (a1.gpr .r2).toNat = 2 ^ (n - 1) := by
    rw [h1.gpr, BitVec.toNat_ushiftRight, bit, Nat.shiftRight_eq_div_pow, show n = (n - 1) + 1 by omega_using [n1],
      Nat.pow_succ, Nat.pow_one, Nat.mul_div_cancel _ (by decide)]
    congr 1
  refine ⟨by rw [hu.gpr, h3.other .r2 (by decide), h2.other .r2 (by decide)]; exact r2a, ?_,
    by rw [hu.gpr, h3.other .r5 (by decide), h2.other .r5 (by decide), h1.other .r5 (by decide)]; exact r5⟩
  rw [zu, h3.gpr, dpVal, h2.other .r5 (by decide), h1.other .r5 (by decide), h2.other .r2 (by decide),
    and_cmp_zero, r5, r2a]
  exact decide_eq_decide.mpr (and_two_pow_eq_zero (by rw [show n - 1 + 1 = n by omega_using [n1]]; exact below))

/-- `n`'s top word's low and high halves. -/
def topLow (w M : Nat) : Nat := topWordOf w M % 2 ^ 32
def topHigh (w M : Nat) : Nat := topWordOf w M / 2 ^ 32

theorem topWord_split {w M L H : Nat} (hL : L < 2 ^ 32) (h : L + 2 ^ 32 * H = topWordOf w M) :
    L = topLow w M ∧ H = topHigh w M := by
  unfold topLow topHigh
  rw [← h]
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL]
  · rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hL, Nat.zero_add]

/-- `topWord`, in terms of `M`. -/
theorem topWord_state (s : State) {base : BitVec 32} {len w M : Nat} (h : ArithmeticReady base len w s)
    (r6 : s.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 0)) (r1 : s.gpr .r1 = BitVec.ofNat 32 w)
    (modulus : numAt s.mem (State.addr base) w 0 = M) :
    WP isa (.block topWord) s fun t => t.gpr .r4 = BitVec.ofNat 32 (8 * w - 8) ∧
      (t.gpr .r3).toNat = topLow w M ∧ (t.gpr .r5).toNat = topHigh w M ∧ t.z = decide (topWordOf w M = 0) ∧
      t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r5, .r6] s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have halves := topWord_halves s.mem (State.addr base) (by omega_using [hw]) modulus
  obtain ⟨eL, eH⟩ := topWord_split (BitVec.isLt _) halves
  refine (topWord_ok s h r6 r1).mono ?_
  rintro t ⟨r4, r3, r5, z, mem, rest⟩
  refine ⟨r4, by rw [r3]; exact eL, by rw [r5]; exact eH, ?_, mem, rest⟩
  rw [z, ← halves]
  exact decide_eq_decide.mpr ⟨fun e => by rw [e.1, e.2], fun e => by omega_using [e]⟩

end VG.Proof.Bignum.Arm
