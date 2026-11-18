module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Mont.Words
meta import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
meta import VerifiedGarbage.Proof.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Init
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
meta import VerifiedGarbage.Proof.Mont.Words

/-! ### `Bignum.Arm.R2Public`, which this module and modules that import it used -/

section

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
    obtain le : 2 ^ (64 * (w - 1) + Nat.log2 (topWordOf w M)) ≤ M := by
      rw [Nat.pow_add, Nat.mul_comm]
      exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.log2_self_le h)) (Nat.div_mul_le_self M _)
    refine Nat.lt_of_le_of_ne le fun e => ?_
    obtain even : 2 ^ (64 * (w - 1) + Nat.log2 (topWordOf w M)) % 2 = 0 := by
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
    obtain bit : v.testBit k = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
      obtain one : v / 2 ^ k = 1 := by
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
  obtain hlt : v < 2 ^ 32 := hv ▸ (s.gpr .r5).isLt
  rw [bitFind, WP.seq_iff]
  unfold bitTest
  refine wp_mov (op2_imm (by decide)) fun a ha => ?_
  refine wp_dp (op2_reg _ _) fun b hb => ?_
  refine wp_cmp (op2_imm (by decide)) fun t0 ht z => WP.block_nil ?_
  obtain r2t : (t0.gpr .r2).toNat = 2 ^ 31 := by rw [ht.gpr, hb.other .r2 (by decide), ha.gpr]; rfl
  obtain r5t : t0.gpr .r5 = s.gpr .r5 := by rw [ht.gpr, hb.other .r5 (by decide), ha.other .r5 (by decide)]
  obtain r1t : t0.gpr .r1 = s.gpr .r1 := by rw [ht.gpr, hb.other .r1 (by decide), ha.other .r1 (by decide)]
  obtain z' : t0.z = decide (v < 2 ^ 31) := by
    rw [z, hb.gpr, dpVal, ha.other .r5 (by decide), ha.gpr, and_cmp_zero, hv]
    exact decide_eq_decide.mpr (and_two_pow_eq_zero (k := 31) hlt)
  obtain mem0 : t0.mem = s.mem := ht.mem.trans (hb.mem.trans ha.mem)
  obtain rest0 : Rest [.r1, .r2, .r3] s t0 :=
    (ha.rest (by decide)).trans ((hb.rest (by decide)).trans (ht.rest _))
  by_cases top : v < 2 ^ 31
  · refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, z', decide_eq_true top]) (fun _ => ?_) (by simp)
    refine WP.loop (M := isa) (fun k t => BitAt s v c k t) (fun k t h => ?_) 31 t0
      ⟨r2t, top, Nat.le_refl _, by rw [r1t, count, Nat.sub_self, Nat.add_zero], r5t, mem0, rest0⟩
    obtain k1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with e | e
      · have := h.below; rw [e] at this; omega
      · exact e
    unfold bitStep
    refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun a1 h1 => ?_
    refine wp_dp (op2_imm (by decide)) fun a2 h2 => ?_
    refine wp_dp (op2_reg _ _) fun a3 h3 => ?_
    refine wp_cmp (op2_imm (by decide)) fun u hu zu => WP.block_nil ?_
    obtain r2u : (u.gpr .r2).toNat = 2 ^ (k - 1) := by
      rw [hu.gpr, h3.other .r2 (by decide), h2.other .r2 (by decide), h1.gpr, BitVec.toNat_ushiftRight,
        h.bit, Nat.shiftRight_eq_div_pow, show k = (k - 1) + 1 by omega_using [k1], Nat.pow_succ, Nat.pow_one,
        Nat.mul_div_cancel _ (by decide)]
      congr 1
    obtain r5u : u.gpr .r5 = s.gpr .r5 := by
      rw [hu.gpr, h3.other .r5 (by decide), h2.other .r5 (by decide), h1.other .r5 (by decide), h.half]
    obtain r1u : u.gpr .r1 = BitVec.ofNat 32 (c + (31 - (k - 1))) := by
      rw [hu.gpr, h3.other .r1 (by decide), h2.gpr, dpVal, h1.other .r1 (by decide), h.count]
      change BitVec.ofNat 32 _ + BitVec.ofNat 32 1 = _
      rw [← BitVec.ofNat_add]
      congr 1; have := h.le; omega_using [k1, this]
    obtain below : v < 2 ^ (k - 1 + 1) := by rw [show k - 1 + 1 = k by omega_using [k1]]; exact h.below
    obtain zk : u.z = decide (v < 2 ^ (k - 1)) := by
      rw [zu, h3.gpr, dpVal, h2.other .r5 (by decide), h1.other .r5 (by decide), h2.other .r2 (by decide),
        and_cmp_zero, h.half, hv, show (a1.gpr .r2).toNat = 2 ^ (k - 1) by
          rw [← r2u, hu.gpr, h3.other .r2 (by decide), h2.other .r2 (by decide)]]
      exact decide_eq_decide.mpr (and_two_pow_eq_zero below)
    obtain memu : u.mem = s.mem := hu.mem.trans (h3.mem.trans (h2.mem.trans (h1.mem.trans h.mem)))
    obtain restu : Rest [.r1, .r2, .r3] s u :=
      h.rest.trans ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans ((h3.rest (by decide)).trans
        (hu.rest _))))
    by_cases more : v < 2 ^ (k - 1)
    · right
      exact ⟨by rw [VG.Proof.X25519.Arm.eval_eq, zk, decide_eq_true more], k - 1, by omega_using [k1],
        ⟨r2u, more, by have := h.le; omega_using [this], r1u, r5u, memu, restu⟩⟩
    · left
      obtain log : Nat.log2 v = k - 1 := log2_of_bounds (Nat.le_of_not_lt more) below
      refine ⟨by rw [VG.Proof.X25519.Arm.eval_eq, zk, decide_eq_false more], ?_, ?_, r5u, memu, restu⟩
      · rw [r2u, log]
      · rw [r1u, log]
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, z', decide_eq_false top]) (by simp)
      (fun _ => WP.block_nil ?_)
    obtain log : Nat.log2 v = 31 := log2_of_bounds (Nat.le_of_not_lt top) hlt
    exact ⟨by rw [r2t, log], by rw [r1t, count, log, Nat.sub_self, Nat.add_zero], r5t, mem0, rest0⟩

/-! ## The top word in memory -/

/-- One 32-bit word written into a zero number. -/
theorem val32_write_of_zero (m : Mem) (base : Addr) {d n i : Nat} (hi : i < n) (fit : d + 4 * n < 2 ^ 64)
    (zero : val32 m base d n = 0) (v : BitVec 32) :
    val32 (m.writeW (off base (d + 4 * i)) v) base d n = 2 ^ (32 * i) * v.toNat := by
  obtain split : n = i + ((n - i - 1) + 1) := by omega_using [hi]
  obtain outside := writeW32_outside m base (d := d + 4 * i) v (by omega_using [hi, fit])
  rw [split, val32_append, val32] at zero ⊢
  obtain low : val32 m base d i = 0 := by omega_using [zero]
  obtain pos := Nat.two_pow_pos (32 * i)
  obtain high : val32 m base (d + 4 * i + 4) (n - i - 1) = 0 := by
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
  obtain lo := val32_lt m base (arrAt w 0) (2 * w - 2)
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
  obtain lo := Nat.log2_self_le hh
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
  obtain fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  obtain size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  obtain header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
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
  obtain hw : 2 ≤ w := h.width ▸ h.layout.1
  obtain fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  obtain end0 := Nat.le_trans (array_end_le (w := w) (by decide : 0 < 8)) fits
  have nowrap := h.workspace.nowrap
  unfold topWord
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun a ha => ?_
  refine wp_dp (op2_imm (by decide)) fun b hb => ?_
  refine wp_dp (op2_reg _ _) fun c hc => ?_
  obtain r4b : b.gpr .r4 = BitVec.ofNat 32 (8 * w - 8) := by
    rw [hb.gpr, dpVal, ha.gpr, r1, shl3_ofNat]
    exact VG.Offset.ofNat_sub_ofNat (show 8 ≤ 8 * w by omega_using [hw])
  obtain r4c : c.gpr .r4 = BitVec.ofNat 32 (8 * w - 8) := by rw [hc.other .r4 (by decide), r4b]
  obtain r6c : c.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 0 + 8 * w - 8) := by
    rw [hc.gpr, dpVal, hb.other .r6 (by decide), ha.other .r6 (by decide), r6, r4b, BitVec.add_assoc,
      ← BitVec.ofNat_add, show arrAt w 0 + 8 * w - 8 = arrAt w 0 + (8 * w - 8) by omega_using [hw]]
  obtain memc : c.mem = s.mem := hc.mem.trans (hb.mem.trans ha.mem)
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
  obtain r3e : e.gpr .r3 = s.mem.readW (off (State.addr base) (arrAt w 0 + 8 * w - 8)) 32 := by
    rw [he.other .r3 (by decide), hd.gpr, memc]
  obtain r5e : e.gpr .r5 = s.mem.readW (off (State.addr base) (arrAt w 0 + 8 * w - 4)) 32 := by
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
  obtain hw : 2 ≤ w := h.width ▸ h.layout.1
  obtain fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  obtain end4 := Nat.le_trans (array_end_le (w := w) (by decide : 4 < 8)) fits
  obtain size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have nowrap := h.workspace.nowrap
  obtain header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  unfold topStore
  refine wp_ldr (a := off (State.addr base) 96) (by decide) (by rw [h.ptr]; exact addr_add (by omega_using [size, nowrap]))
    (h.workspace.read (by omega_using [size])) fun a ha => ?_
  refine wp_dp (op2_reg _ _) fun b' hb => ?_
  obtain r6b : b'.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 4 + 4 * i) := by
    rw [hb.gpr, dpVal, ha.gpr, header.array 4 (by decide), ha.other .r4 (by decide), r4, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  refine wp_str (a := off (State.addr base) (arrAt w 4 + 4 * i)) (by decide)
    (by rw [r6b, BitVec.add_zero]; exact addr_add (by omega_using [hi, end4, nowrap]))
    (by rw [hb.wr, ha.wr]; exact h.workspace.write (by omega_using [hi, end4])) fun c' hc => ?_
  refine wp_dp (op2_imm (by decide)) fun d hd => ?_
  obtain r0d : d.gpr .r0 = base := by
    rw [hd.other .r0 (by decide), hc.gpr, hb.other .r0 (by decide), ha.other .r0 (by decide), h.ptr]
  refine wp_str (a := off (State.addr base) 208) (by decide) (by rw [r0d]; exact addr_add (by omega_using [size, nowrap]))
    (by rw [hd.wr, hc.wr, hb.wr, ha.wr]; exact h.workspace.write (by omega_using [size])) fun t ht => WP.block_nil ?_
  obtain memc : c'.mem = s.mem.writeW (off (State.addr base) (arrAt w 4 + 4 * i)) b := by
    rw [hc.mem, hb.mem, ha.mem, hb.other .r2 (by decide), ha.other .r2 (by decide), r2]
  obtain outside := writeW32_outside s.mem (State.addr base) (d := arrAt w 4 + 4 * i) b (by omega_using [hi, end4, nowrap])
  rw [← memc] at outside
  obtain arrayOutside := outside.mono (o' := arrAt w 4) (n' := 8 * w) (by omega_using []) (by omega_using [hi])
  obtain keeps := outside_array_keeps arrayOutside (len := len) (by omega_using [nowrap])
  obtain frame := outside_workspace arrayOutside (size := 8 * len) (by omega_using [end4])
  obtain restc : Rest roundClobbers s c' :=
    ((ha.rest (ws := [.r6]) (by decide)).trans ((hb.rest (ws := [.r6]) (by decide)).trans (hc.rest _))).mono
      (by decide)
  obtain ready := h.after_array (by decide : 4 ≠ 0) keeps frame restc
    (by rw [hc.gpr, hb.other .r0 (by decide), ha.other .r0 (by decide), h.ptr])
  obtain value : numAt c'.mem (State.addr base) w 4 = 2 ^ (32 * i) * b.toNat := by
    rw [numAt_native, memc]
    exact val32_write_of_zero s.mem _ hi (by omega_using [end4, nowrap]) (by rw [← numAt_native]; exact zero) b
  obtain op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain twoC : w32 c'.mem (State.addr base) (arrAt w 7) = 2 := by
    have := keeps_array_word (d := 0) (bits := 32) keeps fits op7 (by decide) (by omega_using [])
    simp only [Nat.add_zero] at this
    change (c'.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [this]; exact two
  obtain dc : DoubleLoopReady base len w (c'.mem.readW (off (State.addr base) 208) 32).toNat c' :=
    ⟨ready.1.workspace, ready.1.layout, ready.1.width, ready.1.ptr, ready.1.inverse,
      by rw [value, ready.2]; exact bound, twoC, by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      ready.1.stackRead, ready.1.stackSep, ready.1.saved⟩
  obtain r1d : d.gpr .r1 = BitVec.ofNat 32 (c + 1) := by
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
  obtain hw : 2 ≤ w := h.width ▸ h.layout.1
  obtain large : 1 < M := modulus ▸ h.modulus
  obtain odd : M % 2 = 1 := modulus ▸ numAt_odd_of_inverse s.mem _ (by omega_using [hi]) h.inverse
  rw [WP.seq_iff]
  refine WP.mono (bitFind_ok s r5 pos r1) ?_
  rintro u ⟨r2u, r1u, _, mem, rest⟩
  obtain ready := h.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ptr)
  obtain bound : 2 ^ (32 * i) * (u.gpr .r2).toNat < numAt u.mem (State.addr base) w 0 := by
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
  obtain hw : 2 ≤ w := h.width ▸ h.layout.1
  obtain fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  obtain large : 1 < M := initialM ▸ h.modulus
  have op (i : Nat) (hi : i = 0 ∨ i = 4) : Operand i := by
    rcases hi with rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [r2PublicInit, WP.seq_iff]
  refine WP.mono (smallConst_ok s (o := 4) 0 h (by decide) (by decide) (by decide) (by decide)) ?_
  rintro s1 ⟨ready1, zero1, _, keeps1, frame1, rest1⟩
  obtain mod1 := (keeps_array_num keeps1 fits (op 0 (by decide)) (by decide)).trans initialM
  rw [WP.seq_iff]
  refine WP.mono (smallConst_ok s1 (o := 7) 2 ready1 (by decide) (by decide) (by decide) (by decide)) ?_
  rintro s2 ⟨ready2, _, two2, keeps2, frame2, rest2⟩
  obtain mod2 := (keeps_array_num keeps2 fits (op 0 (by decide)) (by decide)).trans mod1
  obtain zero2 := (keeps_array_num keeps2 fits (op 4 (by decide)) (by decide)).trans zero1
  rw [WP.seq_iff]
  refine WP.mono (topPointers_ok s2 ready2) ?_
  rintro s3 ⟨r6, r1, mem3, rest3⟩
  obtain ready3 := ready2.of_mem mem3 rest3 ((rest3.gpr .r0 (by decide)).trans ready2.ptr)
  rw [WP.seq_iff]
  refine WP.mono (topWord_ok s3 ready3 r6 r1) ?_
  rintro s4 ⟨r4, r3, r5, z4, mem4, rest4⟩
  obtain ready4 := ready3.of_mem mem4 rest4 ((rest4.gpr .r0 (by decide)).trans ready3.ptr)
  obtain halves := topWord_halves s3.mem (State.addr base) (by omega_using [hw]) (show numAt s3.mem _ w 0 = M by
    rw [mem3]; exact mod2)
  obtain frame4 : Frame [⟨State.addr base, 8 * len⟩] s.mem s4.mem := by
    rw [mem4, mem3]; exact frame1.trans frame2
  obtain rest14 : Rest roundClobbers s s4 :=
    rest1.trans (rest2.trans ((rest3.mono (by decide)).trans (rest4.mono (by decide))))
  obtain mod4 : numAt s4.mem (State.addr base) w 0 = M := by rw [mem4, mem3]; exact mod2
  obtain zero4 : numAt s4.mem (State.addr base) w 4 = 0 := by rw [mem4, mem3]; exact zero2
  obtain two4 : w32 s4.mem (State.addr base) (arrAt w 7) = 2 := by rw [mem4, mem3]; exact two2.trans rfl
  generalize hL : w32 s3.mem (State.addr base) (arrAt w 0 + 8 * w - 8) = L at halves z4
  generalize hH : w32 s3.mem (State.addr base) (arrAt w 0 + 8 * w - 4) = H at halves z4
  obtain hL32 : L < 2 ^ 32 := hL ▸ BitVec.isLt _
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
    obtain restU : Rest [.r4] s4 u := (ha.rest (by decide)).trans (hu.rest _)
    obtain memU : u.mem = s4.mem := hu.mem.trans ha.mem
    obtain readyU := ready4.of_mem memU restU ((restU.gpr .r0 (by decide)).trans ready4.ptr)
    obtain r4u : u.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) := by
      rw [hu.gpr, ha.gpr, dpVal, r4]
      change BitVec.ofNat 32 _ + BitVec.ofNat 32 4 = _
      rw [← BitVec.ofNat_add, show 8 * w - 8 + 4 = 8 * w - 4 by omega_using [hw]]
    obtain r5u : u.gpr .r5 = s4.gpr .r5 := by rw [hu.gpr, ha.other .r5 (by decide)]
    obtain zH : u.z = decide (H = 0) := by
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
      obtain restD : Rest [.r1, .r4, .r5] u d :=
        (hb.rest (by decide)).trans ((hc.rest (by decide)).trans (hd.rest (by decide)))
      obtain memD : d.mem = u.mem := hd.mem.trans (hc.mem.trans hb.mem)
      obtain readyD := readyU.of_mem memD restD ((restD.gpr .r0 (by decide)).trans readyU.ptr)
      obtain Lpos : 0 < L := by have := Nat.pos_of_ne_zero T0; omega_using [halves, T0]
      obtain r4d : d.gpr .r4 = BitVec.ofNat 32 (4 * (2 * w - 2)) := by
        rw [hd.other .r4 (by decide), hc.other .r4 (by decide), hb.gpr, dpVal, r4u]
        change BitVec.ofNat 32 _ - BitVec.ofNat 32 4 = _
        rw [VG.Offset.ofNat_sub_ofNat (by omega_using [hw])]; congr 1; omega_using []
      obtain r1d : d.gpr .r1 = BitVec.ofNat 32 (w + 32) := by
        rw [hd.gpr, dpVal, hc.other .r1 (by decide), hb.other .r1 (by decide), restU.gpr .r1 (by decide),
          rest4.gpr .r1 (by decide), r1]
        change BitVec.ofNat 32 _ + BitVec.ofNat 32 32 = _
        rw [← BitVec.ofNat_add]
      obtain r5d : (d.gpr .r5).toNat = L := by
        rw [hd.other .r5 (by decide), hc.gpr, hb.other .r3 (by decide), restU.gpr .r3 (by decide), r3, ← hL]
      obtain logL : Nat.log2 L ≤ 31 := Nat.le_of_lt_succ ((Nat.log2_lt (by omega_using [Lpos])).mpr hL32)
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
      obtain hH32 : H < 2 ^ 32 := hH ▸ BitVec.isLt _
      obtain logH : Nat.log2 H ≤ 31 := Nat.le_of_lt_succ ((Nat.log2_lt H0).mpr hH32)
      obtain logT : Nat.log2 (topWordOf w M) = 32 + Nat.log2 H := by rw [← halves]; exact log2_high H0 hL32
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
  obtain hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  obtain ⟨cpos, cle⟩ := r2PublicCount_le (w := w) (M := M) (by omega_using [hw])
  obtain hM : M < 2 ^ (64 * w) := by
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
  obtain value : numAt t.mem (State.addr base) w 4 =
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
  obtain r2a : (a1.gpr .r2).toNat = 2 ^ (n - 1) := by
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
  obtain hw : 2 ≤ w := h.width ▸ h.layout.1
  obtain halves := topWord_halves s.mem (State.addr base) (by omega_using [hw]) modulus
  obtain ⟨eL, eH⟩ := topWord_split (BitVec.isLt _) halves
  refine (topWord_ok s h r6 r1).mono ?_
  rintro t ⟨r4, r3, r5, z, mem, rest⟩
  refine ⟨r4, by rw [r3]; exact eL, by rw [r5]; exact eH, ?_, mem, rest⟩
  rw [z, ← halves]
  exact decide_eq_decide.mpr ⟨fun e => by rw [e.1, e.2], fun e => by omega_using [e]⟩

end VG.Proof.Bignum.Arm

end

end

/-! # `R² mod n` for a public modulus is constant-time

Its branches, its search's trip count and its doublings depend only on the
public modulus `M`, through its top word; every address is the workspace's
or one its header holds.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov wp_cmp op2_imm op2_reg dpVal)

/-! ## Composing stages -/

/-- A relational fact proven from the related states. -/
theorem relCT_of_pre {P Q : State → State → Prop} {c : Prog isa} (h : ∀ s t, P s t → RelCT isa P c Q) :
    RelCT isa P c Q :=
  fun s t tr1 tr2 u w hp e1 e2 => h s t hp s t tr1 tr2 u w hp e1 e2

/-- Two stages, each run's state carried by its own predicate. -/
theorem stage_seq_ct {P1 P2 Q1 Q2 : State → Prop} {a b : Prog isa}
    (first : RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) a (fun _ _ => True))
    (wp1 : ∀ s, P1 s → WP isa a s Q1) (wp2 : ∀ s, P2 s → WP isa a s Q2)
    (second : RelCT isa (fun s t => Q1 s ∧ Q2 t ∧ s.sp = t.sp) b (fun _ _ => True)) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.seq a b) (fun _ _ => True) := by
  have start := (relCT_keep_sp first (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wp1 s h.1, wp2 t h.2.1⟩)
  exact start.seq (second.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

/-- A branch both runs take the same way. -/
theorem stage_ite_ct {P1 P2 : State → Prop} {c : Cond} {a b : Prog isa} {cond : Bool}
    (h1 : ∀ s, P1 s → isa.eval c s = some cond) (h2 : ∀ s, P2 s → isa.eval c s = some cond)
    (ha : cond = true → RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) a (fun _ _ => True))
    (hb : cond = false → RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) b (fun _ _ => True)) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.ite c a b) (fun _ _ => True) := by
  refine RelCT.ite (fun s t h => (h1 s h.1).trans (h2 t h.2.1).symm) ?_ ?_
  · cases cond
    · exact RelCT.of_false fun s t h => by rw [h1 s h.1.1] at h; cases h.2
    · exact (ha rfl).mono (fun _ _ h => h.1) (fun _ _ _ => trivial)
  · cases cond
    · exact (hb rfl).mono (fun _ _ h => h.1) (fun _ _ _ => trivial)
    · exact RelCT.of_false fun s t h => by rw [h1 s h.1.1] at h; cases h.2

/-- A block that touches no memory. -/
theorem regBlock_ct {P : State → State → Prop} {l : List Instr} {hc : Taint.Hint _}
    (h : (taint.check (Taint.ofRegs []) (.block l) hc).isSome = true) :
    RelCT isa P (.block l) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) h

/-! ## The search -/

theorem bitTest_ok (s : State) {v : Nat} (r5 : (s.gpr .r5).toNat = v) :
    WP isa (.block bitTest) s fun t => (t.gpr .r2).toNat = 2 ^ 31 ∧ (t.gpr .r5).toNat = v ∧
      t.z = decide (v < 2 ^ 31) := by
  have hlt : v < 2 ^ 32 := r5 ▸ (s.gpr .r5).isLt
  unfold bitTest
  refine wp_mov (op2_imm (by decide)) fun a ha => ?_
  refine wp_dp (op2_reg _ _) fun b hb => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht z => WP.block_nil ?_
  refine ⟨by rw [ht.gpr, hb.other .r2 (by decide), ha.gpr]; rfl,
    by rw [ht.gpr, hb.other .r5 (by decide), ha.other .r5 (by decide)]; exact r5, ?_⟩
  rw [z, hb.gpr, dpVal, ha.other .r5 (by decide), ha.gpr, and_cmp_zero, r5]
  exact decide_eq_decide.mpr (and_two_pow_eq_zero (k := 31) hlt)

/-- The search's trip count is `v`'s, which both runs share. -/
theorem bitFind_ct {v : Nat} (pos : 0 < v) :
    RelCT isa (fun s t => (s.gpr .r5).toNat = v ∧ (t.gpr .r5).toNat = v ∧ s.sp = t.sp) bitFind
      (fun _ _ => True) := by
  let B := fun (s : State) => (s.gpr .r2).toNat = 2 ^ 31 ∧ (s.gpr .r5).toNat = v ∧ s.z = decide (v < 2 ^ 31)
  have test : RelCT isa (fun s t => (s.gpr .r5).toNat = v ∧ (t.gpr .r5).toNat = v ∧ s.sp = t.sp)
      (.block bitTest) (fun _ _ => True) := regBlock_ct (by taint_decide)
  let I := fun (n : Nat) (s t : State) =>
    ((s.gpr .r2).toNat = 2 ^ n ∧ (s.gpr .r5).toNat = v ∧ v < 2 ^ n) ∧
      ((t.gpr .r2).toNat = 2 ^ n ∧ (t.gpr .r5).toNat = v ∧ v < 2 ^ n) ∧ s.sp = t.sp
  have step (n : Nat) : RelCT isa (I n) (.block bitStep) fun s t => isa.eval .eq s = isa.eval .eq t ∧
      (isa.eval .eq s = some false → True) ∧ (isa.eval .eq s = some true → ∃ m < n, I m s t) := by
    refine relCT_of_pre fun s0 _ h0 => ?_
    have n1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with e | e
      · have := h0.1.2.2; rw [e] at this; omega
      · exact e
    let F := fun (u : State) => (u.gpr .r2).toNat = 2 ^ (n - 1) ∧ u.z = decide (v < 2 ^ (n - 1)) ∧
      (u.gpr .r5).toNat = v
    have ct := (relCT_keep_sp (regBlock_ct (P := I n) (l := bitStep) (by taint_decide))
      (fun _ _ h => h.2.2)).wp (F₁ := F) (F₂ := F)
      (fun s t h => ⟨bitStep_ok s h.1.1 h.1.2.2 h.1.2.1 n1, bitStep_ok t h.2.1.1 h.2.1.2.2 h.2.1.2.1 n1⟩)
    refine ct.mono (fun _ _ h => h) ?_
    rintro s t ⟨sp, fs, ft⟩
    refine ⟨by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, fs.2.1, ft.2.1], fun _ => trivial,
      fun e => ⟨n - 1, by omega_using [n1], ⟨fs.1, fs.2.2, ?_⟩, ⟨ft.1, ft.2.2, ?_⟩, sp⟩⟩
    · rw [VG.Proof.X25519.Arm.eval_eq, fs.2.1] at e; simpa using e
    · rw [VG.Proof.X25519.Arm.eval_eq, fs.2.1] at e; simpa using e
  have loop : RelCT isa (fun s t => B s ∧ B t ∧ s.sp = t.sp) (.ite .eq (.loop (.block bitStep) .eq) (.block []))
      (fun _ _ => True) :=
    stage_ite_ct (cond := decide (v < 2 ^ 31)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2.2])
      (fun hc => (RelCT.loop I step 31).mono (fun _ _ h => by
          have : v < 2 ^ 31 := of_decide_eq_true hc
          exact ⟨⟨h.1.1, h.1.2.1, this⟩, ⟨h.2.1.1, h.2.1.2.1, this⟩, h.2.2⟩) (fun _ _ _ => trivial))
      (fun _ => RelCT.block_nil (fun _ _ _ => trivial))
  rw [bitFind]
  exact stage_seq_ct test (fun s h => bitTest_ok s h) (fun s h => bitTest_ok s h) loop

/-! ## The store and the half's choice -/

theorem topStore_ct {base : BitVec 32} {len w o : Nat} :
    RelCT isa (fun s t => (ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 o) ∧
      (ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 o) ∧ s.sp = t.sp) (.block topStore)
      (fun _ _ => True) := by
  let P := fun (s : State) => s.gpr .r0 = base ∧ s.gpr .r4 = BitVec.ofNat 32 o ∧
    s.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 4)
  have one (s : State) (h : ArithmeticReady base len w s) (r4 : s.gpr .r4 = BitVec.ofNat 32 o) :
      WP isa (.block [.ldr .r6 .r0 96]) s P := by
    have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
    have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
    have nowrap := h.workspace.nowrap
    have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    refine wp_ldr (a := off (State.addr base) 96) (by decide) (by rw [h.ptr]; exact addr_add (by omega_using [size, nowrap]))
      (h.workspace.read (by omega_using [size])) fun t a => WP.block_nil ?_
    exact ⟨(a.other .r0 (by decide)).trans h.ptr, (a.other .r4 (by decide)).trans r4,
      a.gpr.trans (header.array 4 (by decide))⟩
  have first := RelCT.wp (RelCT.taint (A := taint) (c := .block [.ldr .r6 .r0 96]) (Taint.ofRegs [.r0])
    (P := fun s t => (ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 o) ∧
      (ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 o) ∧ s.sp = t.sp)
    (fun s t h => Taint.agree_ofRegs (by simpa using h.1.1.ptr.trans h.2.1.1.ptr.symm)) (by taint_decide))
    (fun s t h => ⟨one s h.1.1 h.1.2, one t h.2.1.1 h.2.1.2⟩)
  show RelCT isa _ (.block ([Instr.ldr .r6 .r0 96] ++ [.dp .add .r6 .r6 (.reg .r4), .str .r2 .r6 0,
    .dp .add .r1 .r1 (.imm 1), .str .r1 .r0 208])) _
  apply RelCT.block_append
  refine first.seq (RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r4, .r6]) ?_ (by taint_decide))
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.2.1.1.trans h.2.2.1.symm
  · exact h.2.1.2.1.trans h.2.2.2.1.symm
  · exact h.2.1.2.2.trans h.2.2.2.2.symm

/-- The half the search runs on, and its 32-bit word in the top word. -/
def topV (w M : Nat) : Nat := if topHigh w M = 0 then topLow w M else topHigh w M
def topIdx (w M : Nat) : Nat := if topHigh w M = 0 then 2 * w - 2 else 2 * w - 1

theorem topV_pos {w M : Nat} (hT : topWordOf w M ≠ 0) : 0 < topV w M := by
  unfold topV topLow topHigh at *
  split
  · rename_i h
    have := Nat.div_add_mod (topWordOf w M) (2 ^ 32)
    rw [h, Nat.mul_zero, Nat.zero_add] at this
    omega_using [hT, h]
  · omega_arith

/-- The top word's halves read: the state the choice starts from. -/
def TopRead (base : BitVec 32) (len w M : Nat) (s : State) : Prop :=
  ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (8 * w - 8) ∧
    (s.gpr .r3).toNat = topLow w M ∧ (s.gpr .r5).toNat = topHigh w M

/-- The half chosen. -/
def TopChosen (base : BitVec 32) (len w M : Nat) (s : State) : Prop :=
  ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (4 * topIdx w M) ∧ (s.gpr .r5).toNat = topV w M

theorem topHalf_wp (s : State) {base : BitVec 32} {len w M : Nat} (h : TopRead base len w M s) :
    WP isa (.block topHalf) s fun t => (ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
      (t.gpr .r3).toNat = topLow w M ∧ (t.gpr .r5).toNat = topHigh w M) ∧ t.z = decide (topHigh w M = 0) := by
  have hw : 2 ≤ w := h.1.width ▸ h.1.layout.1
  unfold topHalf
  refine wp_dp (op2_imm (by decide)) fun a ha => ?_
  refine wp_cmp (op2_imm (by decide)) fun u hu zu => WP.block_nil ?_
  have rest : Rest [.r4] s u := (ha.rest (by decide)).trans (hu.rest _)
  refine ⟨⟨h.1.of_mem (hu.mem.trans ha.mem) rest ((rest.gpr .r0 (by decide)).trans h.1.ptr), ?_,
    by rw [rest.gpr .r3 (by decide)]; exact h.2.2.1, by rw [rest.gpr .r5 (by decide)]; exact h.2.2.2⟩, ?_⟩
  · rw [hu.gpr, ha.gpr, dpVal, h.2.1]
    change BitVec.ofNat 32 _ + BitVec.ofNat 32 4 = _
    rw [← BitVec.ofNat_add, show 8 * w - 8 + 4 = 8 * w - 4 by omega_using [hw]]
  · rw [zu, ha.other .r5 (by decide), cmp_zero, h.2.2.2]

theorem topChoose_wp (s : State) {base : BitVec 32} {len w M : Nat}
    (h : (ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
      (s.gpr .r3).toNat = topLow w M ∧ (s.gpr .r5).toNat = topHigh w M) ∧ s.z = decide (topHigh w M = 0)) :
    WP isa (.ite .eq (.block lowHalf) (.block [])) s (TopChosen base len w M) := by
  have hw : 2 ≤ w := h.1.1.width ▸ h.1.1.layout.1
  by_cases H0 : topHigh w M = 0
  · refine WP.ite true (by rw [VG.Proof.X25519.Arm.eval_eq, h.2, decide_eq_true H0]) (fun _ => ?_) (by simp)
    unfold lowHalf
    refine wp_dp (op2_imm (by decide)) fun b hb => ?_
    refine wp_mov (op2_reg _ _) fun c hc => ?_
    refine wp_dp (op2_imm (by decide)) fun d hd => WP.block_nil ?_
    have rest : Rest [.r1, .r4, .r5] s d :=
      (hb.rest (by decide)).trans ((hc.rest (by decide)).trans (hd.rest (by decide)))
    refine ⟨h.1.1.of_mem (hd.mem.trans (hc.mem.trans hb.mem)) rest ((rest.gpr .r0 (by decide)).trans h.1.1.ptr),
      ?_, ?_⟩
    · rw [hd.other .r4 (by decide), hc.other .r4 (by decide), hb.gpr, dpVal, h.1.2.1]
      change BitVec.ofNat 32 _ - BitVec.ofNat 32 4 = _
      simp only [topIdx, H0, ite_true]
      rw [VG.Offset.ofNat_sub_ofNat (by omega_using [hw])]
      congr 1; omega_using []
    · simp only [topV, H0, ite_true]
      rw [hd.other .r5 (by decide), hc.gpr, hb.other .r3 (by decide), h.1.2.2.1]
  · refine WP.ite false (by rw [VG.Proof.X25519.Arm.eval_eq, h.2, decide_eq_false H0]) (by simp)
      (fun _ => WP.block_nil ?_)
    refine ⟨h.1.1, ?_, ?_⟩
    · simp only [topIdx, H0, ite_false]; rw [h.1.2.1]; congr 1; omega_using []
    · simp only [topV, H0, ite_false]; exact h.1.2.2.2

theorem topFind_wp (s : State) {base : BitVec 32} {len w M : Nat} (h : TopChosen base len w M s)
    (pos : 0 < topV w M) :
    WP isa bitFind s fun t => ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 (4 * topIdx w M) := by
  refine (bitFind_ok s (c := (s.gpr .r1).toNat) h.2.2 pos (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])).mono ?_
  rintro t ⟨_, _, _, mem, rest⟩
  exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.1.ptr), by rw [rest.gpr .r4 (by decide)]; exact h.2.1⟩

theorem topInit_ct {base : BitVec 32} {len w M : Nat} (hT : topWordOf w M ≠ 0) :
    RelCT isa (fun s t => TopRead base len w M s ∧ TopRead base len w M t ∧ s.sp = t.sp) topInit
      (fun _ _ => True) := by
  have low : RelCT isa (fun s t =>
      (((ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
        (s.gpr .r3).toNat = topLow w M ∧ (s.gpr .r5).toNat = topHigh w M) ∧ s.z = decide (topHigh w M = 0)) ∧
      ((ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
        (t.gpr .r3).toNat = topLow w M ∧ (t.gpr .r5).toNat = topHigh w M) ∧ t.z = decide (topHigh w M = 0)) ∧
      s.sp = t.sp)) (.block lowHalf) (fun _ _ => True) := regBlock_ct (by taint_decide)
  have choose : RelCT isa (fun s t =>
      ((ArithmeticReady base len w s ∧ s.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
        (s.gpr .r3).toNat = topLow w M ∧ (s.gpr .r5).toNat = topHigh w M) ∧ s.z = decide (topHigh w M = 0)) ∧
      ((ArithmeticReady base len w t ∧ t.gpr .r4 = BitVec.ofNat 32 (8 * w - 4) ∧
        (t.gpr .r3).toNat = topLow w M ∧ (t.gpr .r5).toNat = topHigh w M) ∧ t.z = decide (topHigh w M = 0)) ∧
      s.sp = t.sp) (.ite .eq (.block lowHalf) (.block [])) (fun _ _ => True) :=
    stage_ite_ct (cond := decide (topHigh w M = 0)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2]) (fun _ => low)
      (fun _ => RelCT.block_nil (fun _ _ _ => trivial))
  have find : RelCT isa (fun s t => TopChosen base len w M s ∧ TopChosen base len w M t ∧ s.sp = t.sp) bitFind
      (fun _ _ => True) :=
    (bitFind_ct (topV_pos hT)).mono (fun _ _ h => ⟨h.1.2.2, h.2.1.2.2, h.2.2⟩) (fun _ _ _ => trivial)
  rw [topInit]
  exact stage_seq_ct (regBlock_ct (by taint_decide)) (fun s h => topHalf_wp s h) (fun s h => topHalf_wp s h)
    (stage_seq_ct choose (fun s h => topChoose_wp s h) (fun s h => topChoose_wp s h)
      (stage_seq_ct find (fun s h => topFind_wp s h (topV_pos hT)) (fun s h => topFind_wp s h (topV_pos hT))
        topStore_ct))

/-! ## The initialization and `R² mod n` -/

theorem r2PublicInit_ct {base : BitVec 32} {len w M : Nat} :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
      r2PublicInit (fun _ _ => True) := by
  let A := fun (s : State) => ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have small (o : Nat) (v : BitVec 32) (ho : o < 8) (ho0 : o ≠ 0) (encO : encodable (BitVec.ofNat 32 o) = true)
      (encV : encodable v = true) (s : State) (h : A s) : WP isa (smallConst (BitVec.ofNat 32 o) v) s A := by
    have fits : arrAt w 8 ≤ 8 * len := h.1.width ▸ h.1.layout.2.2.1
    exact (smallConst_ok s v h.1 ho ho0 encO encV).mono fun t k =>
      ⟨k.1, (keeps_array_num k.2.2.2.1 fits op0 (Ne.symm ho0)).trans h.2⟩
  have smallCT (o : Nat) (v : BitVec 32) (ho : o < 8) (encO : encodable (BitVec.ofNat 32 o) = true)
      (encV : encodable v = true) :
      RelCT isa (fun s t => A s ∧ A t ∧ s.sp = t.sp) (smallConst (BitVec.ofNat 32 o) v) (fun _ _ => True) :=
    (smallConst_ct v ho encO encV).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  let A3 := fun (s : State) => A s ∧ s.gpr .r6 = base + BitVec.ofNat 32 (arrAt w 0) ∧
    s.gpr .r1 = BitVec.ofNat 32 w
  have wp3 (s : State) (h : A s) : WP isa (.block topPointers) s A3 :=
    (topPointers_ok s h.1).mono fun t k =>
      ⟨⟨h.1.of_mem k.2.2.1 k.2.2.2 ((k.2.2.2.gpr .r0 (by decide)).trans h.1.ptr), by rw [k.2.2.1]; exact h.2⟩,
        k.1, k.2.1⟩
  have ct3 : RelCT isa (fun s t => A s ∧ A t ∧ s.sp = t.sp) (.block topPointers) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r0])
      (fun s t h => Taint.agree_ofRegs (by simpa using h.1.1.ptr.trans h.2.1.1.ptr.symm)) (by taint_decide)
  let A4 := fun (s : State) => TopRead base len w M s ∧ s.z = decide (topWordOf w M = 0)
  have wp4 (s : State) (h : A3 s) : WP isa (.block topWord) s A4 :=
    (topWord_state s h.1.1 h.2.1 h.2.2 h.1.2).mono fun t k =>
      ⟨⟨h.1.1.of_mem k.2.2.2.2.1 k.2.2.2.2.2 ((k.2.2.2.2.2.gpr .r0 (by decide)).trans h.1.1.ptr), k.1, k.2.1,
        k.2.2.1⟩, k.2.2.2.1⟩
  have ct4 : RelCT isa (fun s t => A3 s ∧ A3 t ∧ s.sp = t.sp) (.block topWord) (fun _ _ => True) := by
    refine RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1, .r6]) ?_ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.1.1.ptr.trans h.2.1.1.1.ptr.symm
    · exact h.1.2.2.trans h.2.1.2.2.symm
    · exact h.1.2.1.trans h.2.1.2.1.symm
  have branch : RelCT isa (fun s t => A4 s ∧ A4 t ∧ s.sp = t.sp) (.ite .eq r2Init topInit) (fun _ _ => True) :=
    stage_ite_ct (cond := decide (topWordOf w M = 0)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun _ => (r2Init_ct (base := base) (len := len) (w := w)).mono
        (fun _ _ h => ⟨h.1.1.1, h.2.1.1.1, h.2.2⟩) (fun _ _ _ => trivial))
      (fun hc => (topInit_ct (of_decide_eq_false hc)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩)
        (fun _ _ _ => trivial))
  rw [r2PublicInit]
  exact stage_seq_ct (smallCT 4 0 (by decide) (by decide) (by decide))
    (fun s h => small 4 0 (by decide) (by decide) (by decide) (by decide) s h)
    (fun s h => small 4 0 (by decide) (by decide) (by decide) (by decide) s h)
    (stage_seq_ct (smallCT 7 2 (by decide) (by decide) (by decide))
      (fun s h => small 7 2 (by decide) (by decide) (by decide) (by decide) s h)
      (fun s h => small 7 2 (by decide) (by decide) (by decide) (by decide) s h)
      (stage_seq_ct ct3 (fun s h => wp3 s h) (fun s h => wp3 s h)
        (stage_seq_ct ct4 (fun s h => wp4 s h) (fun s h => wp4 s h) branch)))

theorem r2Public_ct {base : BitVec 32} {len w M : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧
      (ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ s.sp = t.sp)
      r2Public (fun _ _ => True) := by
  let P := R2PublicInitialized base len w M
  have initialized := (relCT_keep_sp (r2PublicInit_ct (base := base) (len := len) (w := w) (M := M))
    (fun _ _ h => h.2.2)).wp (fun s t h =>
      ⟨WP.mono (r2PublicInit_ok s h.1.1 h.1.2) (fun _ j => j.1),
       WP.mono (r2PublicInit_ok t h.2.1.1 h.2.1.2) (fun _ j => j.1)⟩)
  have loop : RelCT isa (fun s t => s.sp = t.sp ∧ P s ∧ P t) doubleLoop (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have hw : 2 ≤ w := h.2.1.ready.width ▸ h.2.1.ready.layout.1
    obtain ⟨cpos, cle⟩ := r2PublicCount_le (w := w) (M := M) (by omega_using [hw])
    exact doubleLoop_ct cpos (by omega_using [countFits, cle]) s t tr1 tr2 u v ⟨h.2.1.ready, h.2.2.ready, h.1⟩ e1 e2
  have post (s : State) (h : P s) : WP isa doubleLoop s fun t => ∃ m, R2Sq base len w m w t :=
    WP.mono (r2PublicLoop_ok s h countFits) (fun _ j => ⟨M, j.1⟩)
  have powered := ((relCT_keep_sp loop (fun _ _ h => h.1)).wp
    (fun s t h => ⟨post s h.2.1, post t h.2.2⟩)).mono
    (Q' := R2SqRel base len w w) (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)
  exact initialized.seq (powered.seq r2Squares_ct)

end VG.Proof.Bignum.Arm
