module

public import VerifiedGarbage.Proof.Rc2.CbcScratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
public import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Run
meta import VerifiedGarbage.Proof.Rc2.Memory
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rc2.RISCV64.Cbc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Rc2.CbcList
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Rc2.CbcList
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Impl.Rc2.RISCV64.Block
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Impl.Rc2.RISCV64.Lookup
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Impl.Rc2.RISCV64.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Spec.Rc2
meta import VerifiedGarbage.Impl.Rc2.RISCV64.Lookup
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! ### `Rc2.RISCV64.Rounds`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Lookup`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Scan`, which this module and modules that import it used -/

section

/-!
# RC2 on RISC-V: the table scan

`scan_run`: `scan base rows laneBits bits` leaves in `t1` the doubleword
of the table at `base` that holds byte offset `q` (in `t0`), shifted right
by `q`'s byte offset in it and kept to `bits` bits: the entry at `q`. Row
`k`'s mask is bit `k` of `2 ^ (q / 8)` spread over the doubleword
(`row_mask`), so only the index's row survives the rows' OR (`rows_run`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-! ## The rows -/

/-- Bit `c` of `q` shifted to the top and arithmetically back: all ones if
it is set. -/
theorem bit_mask (q : BitVec 64) {c : Nat} (hc : c < 64) :
    (q <<< (63 - c)).sshiftRight 63 = if q.getLsbD c then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have key : (q <<< (63 - c)).getLsbD 63 = q.getLsbD c := by
    rw [BitVec.getLsbD_shiftLeft]
    simp only [show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
      show ¬ (63 < 63 - c) by omega_using [], decide_false, Bool.not_false, show 63 - (63 - c) = c by omega_using [hc]]
  rw [show (if 63 + i < 64 then (q <<< (63 - c)).getLsbD (63 + i) else (q <<< (63 - c)).getLsbD (64 - 1)) =
    (q <<< (63 - c)).getLsbD 63 by split; (congr 1; omega_arith); rfl, key]
  cases q.getLsbD c
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true, show ¬ 64 ≤ i by omega_using [hi], decide_false,
      Bool.not_false, Bool.and_true]

/-- Row `k`'s mask from the row's bit: all ones exactly for the index's row. -/
theorem row_mask (r : Nat) {k : Nat} (hk : k < 64) :
    (BitVec.twoPow 64 r <<< (63 - k)).sshiftRight 63 = if r = k then BitVec.allOnes 64 else 0 := by
  rw [bit_mask _ hk, BitVec.getLsbD_twoPow]
  by_cases h : r = k
  · subst h; simp only [ite_true, decide_eq_true hk, Bool.true_and, decide_true]
  · simp [h]

/-- The scan's base is none of the registers it writes or reads the index from. -/
structure ScanRegs (base : Reg) : Prop where
  b0 : base ≠ .a7
  b10 : base ≠ .t0
  b11 : base ≠ .t1
  b12 : base ≠ .t2
  b13 : base ≠ .t3

theorem rowBit_run (u : State) (hq : (u.gpr .t0).toNat < 256) :
    WP isa (.block rowBit) u fun t =>
      t.gpr .t3 = BitVec.twoPow 64 ((u.gpr .t0).toNat / 8) ∧ t.mem = u.mem := by
  unfold rowBit
  rrun
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [hq])]
  rfl

theorem row0_run {base : Reg} (R : ScanRegs base) (u : State) {T B : BitVec 64} (hT : u.gpr base = T)
    (h3 : u.gpr .t3 = B) (hal : T.toNat % 8 = 0) (hr : InRegions (u.rd ++ u.wr) T 8) :
    WP isa (.block (row0 base)) u fun t =>
      t.gpr .t1 = u.mem.readW T 64 &&& (B <<< (63 - 0)).sshiftRight 63 ∧ t.mem = u.mem := by
  have b12 := R.b12; have b13 := R.b13
  unfold row0 rowMask
  rrun [hT, h3, hr, hal, b12, b13, Ne.symm b12, Ne.symm b13]

theorem row_run {base : Reg} (R : ScanRegs base) (u : State) {T B : BitVec 64} {k : Nat} (hk : k < 32)
    (hT : u.gpr base = T) (h3 : u.gpr .t3 = B)
    (hal : (T + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0)
    (hr : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (row base k)) u fun t =>
      t.gpr .t1 = u.gpr .t1 ||| (u.mem.readW (T + BitVec.ofNat 64 (8 * k)) 64 &&&
        (B <<< (63 - k)).sshiftRight 63) ∧ t.mem = u.mem := by
  have b0 := R.b0; have b12 := R.b12; have b13 := R.b13
  unfold row rowMask
  rrun [hT, h3, hr, hal, b0, b12, b13, Ne.symm b0, Ne.symm b12, Ne.symm b13, show 63 - k < 64 by omega_using [],
    show 8 * k < 2048 by omega_using [hk]]

/-- After rows `0, …, n - 1`, from the scan's start `s₀`. -/
structure RowInv (s₀ : State) (T : Addr) (n : Nat) (u : State) : Prop where
  acc : u.gpr .t1 = if (s₀.gpr .t0).toNat / 8 < n then
    s₀.mem.readW (T + BitVec.ofNat 64 (8 * ((s₀.gpr .t0).toNat / 8))) 64 else 0#64
  bit : u.gpr .t3 = BitVec.twoPow 64 ((s₀.gpr .t0).toNat / 8)
  keep : Keep [.a7, .t1, .t2, .t3] s₀ u
  mem : u.mem = s₀.mem

theorem rowsCode_succ (base : Reg) (n : Nat) : rowsCode base (n + 1) = rowsCode base n ++ row base (n + 1) := by
  simp only [rowsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

theorem keep_or (x : BitVec 64) (c : Prop) [Decidable c] :
    x &&& (if c then BitVec.allOnes 64 else 0) = if c then x else 0#64 := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h, BitVec.and_allOnes]
  · rw [ite_eq_right h, ite_eq_right h]; exact BitVec.and_zero

/-- Rows `0, …, n`, from `u` with the row's bit in `t3`. -/
theorem rows_run {base : Reg} (R : ScanRegs base) {s₀ : State} {T : Addr} (hT : s₀.gpr base = T)
    (hal : T.toNat % 8 = 0) {u : State} (h3 : u.gpr .t3 = BitVec.twoPow 64 ((s₀.gpr .t0).toNat / 8))
    (hk : Keep [.a7, .t1, .t2, .t3] s₀ u) (hm : u.mem = s₀.mem) {rows : Nat} (hrows : rows ≤ 32)
    (hr : ∀ k < rows, InRegions (s₀.rd ++ s₀.wr) (T + BitVec.ofNat 64 (8 * k)) 8) :
    ∀ n, n < rows → WP isa (.block (rowsCode base n)) u (RowInv s₀ T (n + 1)) := by
  have nb : base ∉ [Reg.a7, .t1, .t2, .t3] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨R.b0, R.b11, R.b12, R.b13⟩
  intro n
  induction n with
  | zero =>
    intro _
    unfold rowsCode
    simp only [List.range_zero, List.flatMap_nil, List.append_nil]
    have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [hk.2.1, hk.2.2]
    have r0 := hr 0 (by omega_arith)
    simp only [Nat.mul_zero, BitVec.add_zero] at r0
    refine WP.mono (WP.keep [.a7, .t1, .t2] (row0_run R u ((hk.gpr nb).trans hT) h3 hal
      (by rw [hrd]; exact r0)) (by rfl) rfl) fun t ⟨⟨t1, tm⟩, tk⟩ =>
        ⟨?_, by rw [tk.gpr (by decide), h3], (hk.trans tk).mono (by decide), tm.trans hm⟩
    rw [t1, row_mask _ (by decide), keep_or, hm]
    by_cases h : (s₀.gpr .t0).toNat / 8 = 0
    · rw [ite_eq_left h, ite_eq_left (by omega_using [h]), h, Nat.mul_zero, BitVec.add_zero]
    · rw [ite_eq_right h, ite_eq_right (by omega_using [h])]
  | succ n ih =>
    intro hn
    rw [rowsCode_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun v V => ?_
    have hrd : v.rd ++ v.wr = s₀.rd ++ s₀.wr := by rw [V.keep.2.1, V.keep.2.2]
    refine WP.mono (WP.keep [.a7, .t1, .t2] (row_run R v (k := n + 1) (by omega_using [hrows, hn]) ((V.keep.gpr nb).trans hT)
      V.bit (Spill.al8 hal (by omega_using [])) (by rw [hrd]; exact hr _ hn)) (by rfl) rfl) fun t ⟨⟨t1, tm⟩, tk⟩ =>
        ⟨?_, by rw [tk.gpr (by decide), V.bit], (V.keep.trans tk).mono (by decide), tm.trans V.mem⟩
    rw [t1, V.acc, row_mask _ (by omega_using [hrows, hn]), keep_or, V.mem]
    by_cases h1 : (s₀.gpr .t0).toNat / 8 = n + 1
    · rw [ite_eq_right (by omega_using [h1]), ite_eq_left h1, ite_eq_left (by omega_using [h1]), h1, BitVec.zero_or]
    · by_cases h2 : (s₀.gpr .t0).toNat / 8 < n + 1
      · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left (by omega_using [h2]), BitVec.or_zero]
      · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by omega_using [h1, h2]), BitVec.or_zero]

/-! ## The lane -/

theorem shl_shr (x : BitVec 64) {n : Nat} (hn : n ≤ 64) :
    (x <<< (64 - n)) >>> (64 - n) = (x.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i < n
  · simp [h, hi]; intro _; omega_arith
  · simp [h]; intro _; omega_arith

/-- `andi` of a numeral below 2048. -/
theorem exec_andi_nat {s : State} {d n : Reg} {m : Nat} (h : m < 2048) :
    exec (.logicImm .and d n (m : Int)) s = some (s.write d (s.gpr n &&& BitVec.ofNat 64 m)) := by
  rw [exec_logicImm (by unfold imm12; omega_using [h]), BitVec.ofInt_natCast]

theorem lane_run (u : State) {laneBits : Nat} (hb : laneBits < 2048)
    (hlane : (u.gpr .t0 &&& BitVec.ofNat 64 laneBits).toNat = (u.gpr .t0).toNat % 8) :
    WP isa (.block (laneCode laneBits)) u fun t =>
      t.gpr .t1 = u.gpr .t1 >>> (8 * ((u.gpr .t0).toNat % 8)) ∧ t.mem = u.mem := by
  unfold laneCode
  rrun [↓exec_andi_nat, hb]
  have := Nat.mod_lt (u.gpr .t0).toNat (by decide : 8 > 0)
  rw [BitVec.toNat_shiftLeft, hlane, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using []),
    Nat.mul_comm]

/-- The whole scan. -/
theorem scan_run {base : Reg} (R : ScanRegs base) (s : State) {T : Addr} (hT : s.gpr base = T)
    (hal : T.toNat % 8 = 0)
    {rows : Nat} (hrows : 1 ≤ rows ∧ rows ≤ 32) {laneBits : Nat} (hb : laneBits < 2048)
    {bits : Nat} (hbits : 1 ≤ bits ∧ bits ≤ 64)
    (hq : (s.gpr .t0).toNat < 8 * rows)
    (hlane : (s.gpr .t0 &&& BitVec.ofNat 64 laneBits).toNat = (s.gpr .t0).toNat % 8)
    (hr : ∀ k < rows, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (scan base rows laneBits bits) s fun t =>
      t.gpr .t1 = (((s.mem.readW (T + BitVec.ofNat 64 (8 * ((s.gpr .t0).toNat / 8))) 64) >>>
        (8 * ((s.gpr .t0).toNat % 8))).setWidth bits).setWidth 64 ∧
      Keep [.a7, .t1, .t2, .t3] s t ∧ t.mem = s.mem := by
  unfold scan
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .t3] (rowBit_run s (by omega_using [hrows, hq])) (by rfl) rfl) fun u ⟨⟨u3, um⟩, uk⟩ => ?_
  refine WP.mono (rows_run R hT hal u3 (uk.mono (by decide)) um hrows.2 hr (rows - 1) (by omega_using [hrows])) fun v V => ?_
  have q : v.gpr .t0 = s.gpr .t0 := V.keep.gpr (by decide)
  refine WP.mono (WP.keep [.t1, .t2] (lane_run v hb (by rw [q]; exact hlane)) (by rfl) rfl)
    fun w ⟨⟨w1, wm⟩, wk⟩ => ?_
  refine WP.mono (WP.keep [.t1] (Q := fun t => t.gpr .t1 = ((w.gpr .t1).setWidth bits).setWidth 64 ∧
      t.mem = w.mem) (by unfold mask; rrun [show 64 - bits < 64 by omega_arith]; exact shl_shr _ hbits.2)
    (by rfl) rfl) fun t ⟨⟨t11, tm⟩, tk⟩ =>
      ⟨?_, ((V.keep.trans wk).trans tk).mono (by decide), by rw [tm, wm, V.mem]⟩
  rw [t11, w1, V.acc, q, ite_eq_left (by omega_using [hq])]

end VG.Proof.Rc2.RISCV64

end

end

/-!
# RC2 on RISC-V: the lookups

`keyLookup_run`: the scan of the schedule's copy leaves key word `idx` in
`t1`, for `q = 2 idx` in `t0`. `entry_byte`: a byte table's scan leaves its
byte.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem shr_word16 (x : BitVec 64) (l : Nat) :
    (x >>> (8 * l)).setWidth 16 =
      (x.extractLsb' (8 * l) 8).zeroExtend 16 ||| (x.extractLsb' (8 * (l + 1)) 8).zeroExtend 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.truncate_eq_setWidth, BitVec.getLsbD_extractLsb', hj,
    decide_true, Bool.true_and]
  by_cases h8 : j < 8
  · simp [h8, Nat.add_comm]
  · simp [h8, show j - 8 < 8 by omega_using [hj], show j - 8 < 16 by omega_using [hj]]
    congr 1; omega_using [h8]

theorem shr_byte (x : BitVec 64) (l : Nat) :
    (x >>> (8 * l)).setWidth 8 = x.extractLsb' (8 * l) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hj,
    decide_true, Bool.true_and]

/-- Key word `idx` of the schedule at `T`, from its doubleword. -/
theorem entry_word (m : Mem) (T : Addr) {idx : Nat} (hidx : idx < 64) :
    ((m.readW (T + BitVec.ofNat 64 (8 * ((BitVec.ofNat 64 (2 * idx)).toNat / 8))) 64) >>>
      (8 * ((BitVec.ofNat 64 (2 * idx)).toNat % 8))).setWidth 16 = (Spec.Rc2.scheduleAt m T).getD idx 0 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 * idx < 2 ^ 64 by omega_using [hidx]),
    show 2 * idx % 8 = 2 * (idx % 4) by omega_using [], shr_word16 _ _, Proof.Rc2.read64_byte _ _ _ (by omega_using []),
    Proof.Rc2.read64_byte _ _ _ (by omega_using []), Offset.add_add, Offset.add_add, Spec.Rc2.scheduleAt,
    Proof.Rc2.getD_ofFn _ _ hidx]
  simp only
  rw [show 8 * (2 * idx / 8) + 2 * (idx % 4) = 2 * idx by omega_using [],
    show 8 * (2 * idx / 8) + (2 * (idx % 4) + 1) = 2 * idx + 1 by omega_using []]

/-- The byte at offset `q` of the table at `T`, from its doubleword. -/
theorem entry_byte (m : Mem) (T : Addr) (q : BitVec 64) :
    ((m.readW (T + BitVec.ofNat 64 (8 * (q.toNat / 8))) 64) >>> (8 * (q.toNat % 8))).setWidth 8 =
      m (T + q) := by
  rw [shr_byte _ _, Proof.Rc2.read64_byte _ _ _ (Nat.mod_lt _ (by decide)),
    Offset.add_add, show 8 * (q.toNat / 8) + q.toNat % 8 = q.toNat by omega_using [], BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem keyRegs : ScanRegs .a2 := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- A key word's offset is even, so its lane is its bits 1 and 2. -/
theorem word_lane : ∀ idx < 64,
    (BitVec.ofNat 64 (2 * idx) &&& BitVec.ofNat 64 6).toNat = (BitVec.ofNat 64 (2 * idx)).toNat % 8 := by
  decide

/-- The scan of the schedule's copy at `a2`. -/
theorem keyLookup_run (s : State) {T : Addr} (hT : s.gpr .a2 = T) (hal : T.toNat % 8 = 0) {idx : Nat}
    (hidx : idx < 64) (hq : s.gpr .t0 = BitVec.ofNat 64 (2 * idx))
    (hr : ∀ k < 16, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa keyLookup s fun t =>
      t.gpr .t1 = ((Spec.Rc2.scheduleAt s.mem T).getD idx 0).setWidth 64 ∧
      Keep [.a7, .t1, .t2, .t3] s t ∧ t.mem = s.mem := by
  have h2 : (BitVec.ofNat 64 (2 * idx)).toNat = 2 * idx := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hidx])]
  refine WP.mono (scan_run keyRegs s hT hal (rows := 16) (by decide) (laneBits := 6) (by decide)
    (bits := 16) (by decide) (by rw [hq, h2]; omega_using [hidx]) (by rw [hq]; exact word_lane _ hidx) hr)
    fun t ⟨t11, tk, tm⟩ => ⟨?_, tk, tm⟩
  rw [t11, hq, entry_word _ _ hidx]

end VG.Proof.Rc2.RISCV64

end

end

/-! ### `Rc2.RISCV64.Mix`, which this module and modules that import it used -/

section

/-!
# RC2 on RISC-V: the words and the key words

`Holds`: the four words are in `a3`–`a6`; `KeyEnv`: the schedule's copy is
at `a2`; `loadKey_run`: `lhu` reads a key word from the copy. The lemmas
about 16-bit words of the steps, as on PPC64LE (`Proof/Rc2/PPC64LE/Block.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The four words are in `a3`–`a6`, zero-extended. -/
def Holds (v : Spec.Rc2.State) (s : State) : Prop :=
  ∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 64

/-- What the rounds need: the schedule's copy at `a2`, `T`, aligned to 8
bytes and readable. -/
structure KeyEnv (T : Addr) (s : State) : Prop where
  a2 : s.gpr .a2 = T
  al : T.toNat % 8 = 0
  rd : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 o) n

theorem KeyEnv.keep {T : Addr} {s t : State} (E : KeyEnv T s) {rs : List Reg} (h : Keep rs s t)
    (h2 : Reg.a2 ∉ rs) : KeyEnv T t :=
  ⟨by rw [h.gpr h2]; exact E.a2, E.al, fun o n hn => by rw [h.2.1, h.2.2]; exact E.rd o n hn⟩

/-! ## Words in 64-bit registers -/

theorem bv16_bytes (x : BitVec 16) :
    x = (x.extractLsb' 0 8).zeroExtend 16 ||| (x.extractLsb' 8 8).zeroExtend 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · simp [h8]
  · simp only [h8, decide_false, Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and,
      decide_true, show i - 8 < 8 by omega_using [hi], show i - 8 < 16 by omega_using [hi]]
    rw [show 8 + (i - 8) = i by omega_using [h8]]

theorem readW16_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 2) :
    (m.readW a 16).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m a (n := 2) hi]
  simp only [Mem.readW]
  rfl

theorem key_word (m : Mem) (T : Addr) {j : Nat} (hj : j < 64) :
    m.readW (T + BitVec.ofNat 64 (2 * j)) 16 = (Spec.Rc2.scheduleAt m T).getD j 0 := by
  rw [bv16_bytes (m.readW _ 16), show (0 : Nat) = 8 * 0 from rfl, show (8 : Nat) = 8 * 1 from rfl,
    readW16_byte m _ (by decide), readW16_byte m _ (by decide), Offset.add_add, Offset.add_add,
    Spec.Rc2.scheduleAt, Proof.Rc2.getD_ofFn _ _ hj]
  simp only [Nat.add_zero]

theorem lo16_add (x y : BitVec 64) : (x + y).setWidth 16 = x.setWidth 16 + y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (by decide), Nat.add_mod]

theorem lo16_sub (x y : BitVec 64) : (x - y).setWidth 16 = x.setWidth 16 - y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  omega_using []

theorem lo16_ext (x : BitVec 16) : (x.setWidth 64).setWidth 16 = x :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq x)

theorem lo16_and (x y : BitVec 64) : (x &&& y).setWidth 16 = x.setWidth 16 &&& y.setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo16_xor (x y : BitVec 64) : (x ^^^ y).setWidth 16 = x.setWidth 16 ^^^ y.setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem andNot_xor (a c : BitVec 16) : c ^^^ (a &&& c) = ~~~a &&& c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases c.getLsbD i <;> rfl

theorem mask16 (x : BitVec 64) : (x <<< 48) >>> 48 = (x.setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i < 16
  · simp [h, hi]; intro _; omega_using [h]
  · simp [h]; intro _; omega

/-- `rotateSum`: the low 16 bits of `x` rotated left by `s`, zero-extended. -/
theorem rotSum16 (x : BitVec 64) {s : Nat} (h1 : 1 ≤ s) (h2 : s < 16) :
    (x <<< 48) >>> (64 - s) ||| (x <<< (48 + s)) >>> 48 = ((x.setWidth 16).rotateLeft s).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h16 : i < 16
  · rw [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt h2]
    by_cases h : i < s
    · rw [ite_eq_left h]
      simp [hi, show 64 - s + i < 64 by omega, show ¬ 64 - s + i < 48 by omega_using [h2],
        show 64 - s + i - 48 = 16 - s + i by omega_using [h2], show 16 - s + i < 16 by omega_using [h2, h], show 48 + i < 48 + s by omega_using [h]]
    · rw [ite_eq_right h]
      simp [h16, hi, show ¬ 64 - s + i < 64 by omega_using [h], show 48 + i < 64 by omega_using [h16],
        show ¬ 48 + i < 48 + s by omega_using [h], show 48 + i - (48 + s) = i - s by omega_using [], show i - s < 16 by omega_using [h16]]
  · simp [h16, Nat.mod_eq_of_lt h2, show ¬ i < s by omega_using [h2, h16], show ¬ 64 - s + i < 64 by omega_using [h2, h16],
      show ¬ 48 + i < 64 by omega_using [h16]]

/-- `rotate16`: the zero-extended `y` rotated left by `s`. -/
theorem rot16 (y : BitVec 16) {s : Nat} (h1 : 1 ≤ s) (h2 : s < 16) :
    y.setWidth 64 >>> (16 - s) ||| (y.setWidth 64 <<< (48 + s)) >>> 48 = (y.rotateLeft s).setWidth 64 := by
  have e : y.setWidth 64 >>> (16 - s) = (y.setWidth 64 <<< 48) >>> (64 - s) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h : i < s
    · simp [show 16 - s + i < 64 by omega_using [h2, h], show 64 - s + i < 64 by omega_using [h2, h], show ¬ 64 - s + i < 48 by omega_using [h2],
        show 64 - s + i - 48 = 16 - s + i by omega_using [h2]]
    · simp [show ¬ 64 - s + i < 64 by omega_using [h], BitVec.getLsbD_of_ge y (16 - s + i) (by omega_using [h])]
  rw [e, rotSum16 _ h1 h2, lo16_ext]

theorem al2 {T : Addr} (hT : T.toNat % 8 = 0) (j : Nat) : (T + BitVec.ofNat 64 (2 * j)).toNat % 2 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hT]

theorem loadKey_run (u : State) {T : Addr} (E : KeyEnv T u) {j : Nat} (hj : j < 64) :
    WP isa (.block (loadKey j)) u fun t =>
      (t.gpr .t2).setWidth 16 = (Spec.Rc2.scheduleAt u.mem T).getD j 0 ∧ t.mem = u.mem ∧
        Keep [.t2] u t := by
  refine WP.mono (WP.keep (c := .block (loadKey j)) [.t2] (Q := fun t =>
      (t.gpr .t2).setWidth 16 = (Spec.Rc2.scheduleAt u.mem T).getD j 0 ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold loadKey
  rrun [E.a2, E.rd (2 * j) 2 (by omega_using [hj]), al2 E.al j, show 2 * j < 2048 by omega_using [hj]]
  rw [lo16_ext, key_word _ _ hj]

end VG.Proof.Rc2.RISCV64

end

end

/-!
# RC2 on RISC-V: the steps of the rounds

`mix_run`, `reverseMix_run` and `mash_run`: each step maps the four words
in `a3`–`a6` (`Holds`) to the specification's step of them.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem getD_set (v : Spec.Rc2.State) (x : BitVec 16) {i j : Nat} (hj : j < 4) :
    (v.set! i x).getD j 0 = if i = j then x else v.getD j 0 := by
  rw [Proof.Rc2.getD_eq_getElem _ _ hj, Proof.Rc2.getD_eq_getElem _ _ hj]
  simp [Vector.getElem_set!]

theorem wordReg_0 : wordReg 0 = .a3 := rfl
theorem wordReg_1 : wordReg 1 = .a4 := rfl
theorem wordReg_2 : wordReg 2 = .a5 := rfl
theorem wordReg_3 : wordReg 3 = .a6 := rfl
theorem wordReg_4 : wordReg 4 = .a3 := rfl
theorem wordReg_5 : wordReg 5 = .a4 := rfl
theorem wordReg_6 : wordReg 6 = .a5 := rfl

/-- `Holds` after changing word `i`. -/
theorem Holds.set {v : Spec.Rc2.State} {u t : State} (H : Holds v u) {i : Nat} {x : BitVec 16}
    (hx : t.gpr (wordReg i) = x.setWidth 64) (hk : ∀ i' < 4, i' ≠ i → t.gpr (wordReg i') = u.gpr (wordReg i')) :
    Holds (v.set! i x) t := by
  intro i' hi'
  rw [getD_set _ _ hi']
  by_cases h : i = i'
  · subst h; rw [ite_eq_left rfl]; exact hx
  · rw [ite_eq_right h, hk i' hi' (Ne.symm h)]; exact H i' hi'

/-- The words before `i`: their registers' values. -/
theorem Holds.nb {v : Spec.Rc2.State} {u : State} (H : Holds v u) (i d : Nat) :
    u.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 64 := by
  have := H ((i + d) % 4) (Nat.mod_lt _ (by decide))
  rw [← this]; congr 1; simp [wordReg]

theorem mix_val (X K A B C : BitVec 16) (k : BitVec 64) (hk : k.setWidth 16 = K) :
    ((X.setWidth 64 + k + (A.setWidth 64 &&& B.setWidth 64) +
      (C.setWidth 64 ^^^ (A.setWidth 64 &&& C.setWidth 64))) <<< 48) >>> 48 =
      (X + K + (A &&& B) + (~~~A &&& C)).setWidth 64 := by
  rw [mask16]
  congr 1
  simp only [lo16_add, lo16_and, lo16_xor, lo16_ext, hk, andNot_xor]

theorem rmix_val (X K A B C : BitVec 16) (k : BitVec 64) (hk : k.setWidth 16 = K) :
    ((X.setWidth 64 - k - (A.setWidth 64 &&& B.setWidth 64) -
      (C.setWidth 64 ^^^ (A.setWidth 64 &&& C.setWidth 64))) <<< 48) >>> 48 =
      (X - K - (A &&& B) - (~~~A &&& C)).setWidth 64 := by
  rw [mask16]
  congr 1
  simp only [lo16_sub, lo16_and, lo16_xor, lo16_ext, hk, andNot_xor]

/-- The first three instructions of a mix's inputs. -/
def andInputs (i : Nat) : List Instr :=
  [.logic .and .t0 (wordReg (i + 3)) (wordReg (i + 2)), .logic .and .t1 (wordReg (i + 3)) (wordReg (i + 1)),
   .logic .xor .t1 (wordReg (i + 1)) .t1]

theorem andInputs_run (u : State) {i : Nat} (hi : i < 4) :
    WP isa (.block (andInputs i)) u fun t =>
      t.gpr .t0 = u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 2)) ∧
      t.gpr .t1 = u.gpr (wordReg (i + 1)) ^^^ (u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 1))) ∧
      t.mem = u.mem ∧ Keep [.t0, .t1] u t := by
  refine WP.mono (WP.keep [.t0, .t1] (c := .block (andInputs i)) (Q := fun t =>
      t.gpr .t0 = u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 2)) ∧
      t.gpr .t1 = u.gpr (wordReg (i + 1)) ^^^ (u.gpr (wordReg (i + 3)) &&& u.gpr (wordReg (i + 1))) ∧
      t.mem = u.mem) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    (unfold andInputs; rrun [wordReg_0, wordReg_1, wordReg_2, wordReg_3, wordReg_4, wordReg_5, wordReg_6])

/-- The sum and rotation of a mix, on word `i` of `a3`–`a6`. -/
theorem addRot_run (u : State) {i s : Nat} (hi : i < 4) (hs : 1 ≤ s ∧ s < 16) {y : BitVec 16}
    (hy : ((u.gpr (wordReg i) + u.gpr .t2 + u.gpr .t0 + u.gpr .t1) <<< 48) >>> 48 = y.setWidth 64) :
    WP isa (.block (addInputs (wordReg i) ++ rotateSum (wordReg i) s)) u fun t =>
      t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem ∧ Keep [.a7, wordReg i] u t := by
  refine WP.mono (WP.keep [.a7, wordReg i] (c := .block (addInputs (wordReg i) ++ rotateSum (wordReg i) s))
    (Q := fun t => t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, addInputs, rotateSum, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  have h48 : (48 : Nat) < 64 := by decide
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold addInputs rotateSum
    rrun [show 48 + s < 64 by omega_using [hs], show 64 - s < 64 by omega_using [hs]]
    rw [mask16] at hy
    have h16 := congrArg (BitVec.setWidth 16) hy
    rw [lo16_ext, lo16_ext] at h16
    rw [rotSum16 _ hs.1 hs.2, h16]

theorem wordReg_ne : ∀ i' < 4, ∀ i < 4, i' ≠ i → wordReg i' ≠ wordReg i := by decide
theorem wordReg_other : ∀ i < 4, wordReg i ∉ [Reg.a7, .a2, .a1, .t3, .t0, .t1, .t2] := by decide
theorem rotation_bounds : ∀ i < 4, 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by decide

/-- A step that changes only word `i` and the code's temporaries. -/
theorem keep_others {u t : State} {i : Nat} (hi : i < 4) (k : Keep [.a7, .t0, .t1, .t2, wordReg i] u t) :
    ∀ i' < 4, i' ≠ i → t.gpr (wordReg i') = u.gpr (wordReg i') := fun i' hi' hne => by
  refine k.gpr ?_
  have h1 := wordReg_other i' hi'
  have h2 := wordReg_ne i' hi' i hi hne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨h1.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2⟩

theorem mix_run {T : Addr} (u : State) (E : KeyEnv T u) {v : Spec.Rc2.State} (H : Holds v u) {j i : Nat}
    (hj : j < 64) (hi : i < 4) :
    WP isa (.block (mix j i)) u fun t =>
      Holds (Spec.Rc2.mix (Spec.Rc2.scheduleAt u.mem T) j i v) t ∧ t.mem = u.mem ∧
        Keep [.a7, .t0, .t1, .t2, wordReg i] u t := by
  have e : mix j i = andInputs i ++ (loadKey j ++ (addInputs (wordReg i) ++
      rotateSum (wordReg i) (Spec.Rc2.rotation i))) := by
    simp only [mix, mixInputs, andInputs, List.append_assoc, List.cons_append, List.nil_append]
  have o := wordReg_other i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
  rw [e, WP.block_append_iff]
  refine WP.mono (andInputs_run u hi) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadKey_run t₁ (E.keep k₁ (by decide)) hj) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have x2 : t₂.gpr (wordReg i) = u.gpr (wordReg i) := by
    rw [k₂.gpr (by simp; exact Ne.symm o.2.2.2.2.2.2 |> fun h => by simpa using o.2.2.2.2.2.2),
      k₁.gpr (by simp; exact ⟨o.2.2.2.2.1, o.2.2.2.2.2.1⟩)]
  have r10 : t₂.gpr .t0 = t₁.gpr .t0 := k₂.gpr (by decide)
  have r11 : t₂.gpr .t1 = t₁.gpr .t1 := k₂.gpr (by decide)
  have hs := rotation_bounds i hi
  refine WP.mono (addRot_run t₂ hi hs (y := v.getD i 0 + (Spec.Rc2.scheduleAt u.mem T).getD j 0 +
    (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) + (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0))
    (by rw [x2, r10, r11, a₁, b₁, H i hi, H.nb i 3, H.nb i 2, H.nb i 1]
        exact mix_val _ _ _ _ _ _ (by rw [a₂, m₁])))
    fun t₃ ⟨a₃, m₃, k₃⟩ => ⟨?_, by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  exact H.set (by rw [a₃]) (keep_others hi (((k₁.trans k₂).trans k₃).mono (by simp)))

theorem rot_run (u : State) {i s : Nat} (hi : i < 4) (hs : 1 ≤ s ∧ s < 16) {y : BitVec 16}
    (hy : u.gpr (wordReg i) = y.setWidth 64) :
    WP isa (.block (rotate16 (wordReg i) s)) u fun t =>
      t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem ∧ Keep [.a7, wordReg i] u t := by
  refine WP.mono (WP.keep [.a7, wordReg i] (c := .block (rotate16 (wordReg i) s))
    (Q := fun t => t.gpr (wordReg i) = (y.rotateLeft s).setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, rotate16, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold rotate16
    rrun [hy, show 48 + s < 64 by omega_using [hs], show 16 - s < 64 by omega_using []]
    exact rot16 y hs.1 hs.2

theorem sub_run (u : State) {i : Nat} (hi : i < 4) {y : BitVec 16}
    (hy : ((u.gpr (wordReg i) - u.gpr .t2 - u.gpr .t0 - u.gpr .t1) <<< 48) >>> 48 = y.setWidth 64) :
    WP isa (.block (subInputs (wordReg i))) u fun t =>
      t.gpr (wordReg i) = y.setWidth 64 ∧ t.mem = u.mem ∧ Keep [wordReg i] u t := by
  refine WP.mono (WP.keep [wordReg i] (c := .block (subInputs (wordReg i)))
    (Q := fun t => t.gpr (wordReg i) = y.setWidth 64 ∧ t.mem = u.mem) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, subInputs, mask, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [wordReg_0, wordReg_1, wordReg_2, wordReg_3] at hy ⊢
    unfold subInputs mask
    rrun
    exact hy

theorem reverseMix_run {T : Addr} (u : State) (E : KeyEnv T u) {v : Spec.Rc2.State} (H : Holds v u)
    {j i : Nat} (hj : j < 64) (hi : i < 4) :
    WP isa (.block (reverseMix j i)) u fun t =>
      Holds (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt u.mem T) j i v) t ∧ t.mem = u.mem ∧
        Keep [.a7, .t0, .t1, .t2, wordReg i] u t := by
  have hs := rotation_bounds i hi
  have e : reverseMix j i = rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ (andInputs i ++ (loadKey j ++
      subInputs (wordReg i))) := by
    simp only [reverseMix, mixInputs, andInputs, List.append_assoc, List.cons_append, List.nil_append]
  rw [e, WP.block_append_iff]
  refine WP.mono (rot_run u hi (s := 16 - Spec.Rc2.rotation i) (by omega_using [hs]) (H i hi)) fun t₀ ⟨a₀, m₀, k₀⟩ => ?_
  have H₀ : ∀ d, d = 1 ∨ d = 2 ∨ d = 3 →
      t₀.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 64 := fun d hd => by
    rw [← H.nb i d]
    refine k₀.gpr ?_
    have := wordReg_ne ((i + d) % 4) (Nat.mod_lt _ (by decide)) i hi (by omega_using [hd])
    have h1 := wordReg_other ((i + d) % 4) (Nat.mod_lt _ (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
    rw [show wordReg (i + d) = wordReg ((i + d) % 4) by simp [wordReg]]
    exact ⟨h1.1, this⟩
  rw [WP.block_append_iff]
  refine WP.mono (andInputs_run t₀ hi) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have o := wordReg_other i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
  have n3 : Reg.a2 ∉ [Reg.a7, wordReg i] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, Ne.symm o.2.1⟩
  refine WP.mono (loadKey_run t₁ ((E.keep k₀ n3).keep k₁ (by decide)) hj) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have x2 : t₂.gpr (wordReg i) = t₀.gpr (wordReg i) := by
    rw [k₂.gpr (by simpa using o.2.2.2.2.2.2), k₁.gpr (by simp; exact ⟨o.2.2.2.2.1, o.2.2.2.2.2.1⟩)]
  have r10 : t₂.gpr .t0 = t₁.gpr .t0 := k₂.gpr (by decide)
  have r11 : t₂.gpr .t1 = t₁.gpr .t1 := k₂.gpr (by decide)
  refine WP.mono (sub_run t₂ hi (y := (v.getD i 0).rotateRight (Spec.Rc2.rotation i) -
    (Spec.Rc2.scheduleAt u.mem T).getD j 0 - (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) -
    (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0))
    (by rw [x2, r10, r11, a₁, b₁, a₀, H₀ 3 (by omega_using []), H₀ 2 (by omega_using []),
          H₀ 1 (by omega_using []), rotateLeft_reverse _ _ hs.1 hs.2]
        exact rmix_val _ _ _ _ _ _ (by rw [a₂, m₁, m₀])))
    fun t₃ ⟨a₃, m₃, k₃⟩ => ⟨?_, by rw [m₃, m₂, m₁, m₀],
      (((k₀.trans k₁).trans k₂).trans k₃).mono (by simp)⟩
  exact H.set (by rw [a₃]) (keep_others hi ((((k₀.trans k₁).trans k₂).trans k₃).mono (by simp)))

/-! ## Mashing -/

theorem idx_val (w : BitVec 16) :
    ((w.setWidth 64) <<< 58) >>> 57 = BitVec.ofNat 64 (2 * (w &&& 63#16).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h63 : (w &&& 63#16).toNat = w.toNat % 64 := by
    rw [BitVec.toNat_and, show (63#16).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := w.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h63,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show w.toNat < 2 ^ 64 by omega_using [])]
  omega_using []

/-- A mash of word `i`, in the direction `d`. -/
def mashSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem keep_others' {u t : State} {i : Nat} (hi : i < 4)
    (k : Keep [.a7, .t3, .t0, .t1, .t2, wordReg i] u t) :
    ∀ i' < 4, i' ≠ i → t.gpr (wordReg i') = u.gpr (wordReg i') := fun i' hi' hne => by
  refine k.gpr ?_
  have h1 := wordReg_other i' hi'
  have h2 := wordReg_ne i' hi' i hi hne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨h1.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2⟩

theorem mashIndex_run (u : State) {i : Nat} (hi : i < 4) :
    WP isa (.block (mashIndex i)) u fun t =>
      t.gpr .t0 = (u.gpr (wordReg (i + 3)) <<< 58) >>> 57 ∧ t.mem = u.mem ∧ Keep [.t0] u t := by
  refine WP.mono (WP.keep [.t0] (c := .block (mashIndex i)) (Q := fun t =>
      t.gpr .t0 = (u.gpr (wordReg (i + 3)) <<< 58) >>> 57 ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    (unfold mashIndex; rrun [wordReg_3, wordReg_4, wordReg_5, wordReg_6])

theorem adjust_run (u : State) (sub : Bool) {i : Nat} (hi : i < 4) :
    WP isa (.block (adjust sub (wordReg i))) u fun t =>
      t.gpr (wordReg i) = (((if sub then u.gpr (wordReg i) - u.gpr .t1 else u.gpr (wordReg i) + u.gpr .t1)
        <<< 48) >>> 48) ∧ t.mem = u.mem ∧ Keep [wordReg i] u t := by
  refine WP.mono (WP.keep [wordReg i] (c := .block (adjust sub (wordReg i))) (Q := fun t =>
      t.gpr (wordReg i) = (((if sub then u.gpr (wordReg i) - u.gpr .t1 else u.gpr (wordReg i) + u.gpr .t1)
        <<< 48) >>> 48) ∧ t.mem = u.mem) ?_
    (by cases sub <;> simp [writesOnly, Code.allInstrs_eq, instrs, adjust, mask, dstOf]) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> cases sub <;>
    (unfold adjust mask; rrun [wordReg_0, wordReg_1, wordReg_2, wordReg_3])

theorem mash_run {T : Addr} (u : State) (E : KeyEnv T u) {v : Spec.Rc2.State} (H : Holds v u)
    (d : Spec.Rc2.Direction) {i : Nat} (hi : i < 4) :
    WP isa (mash d i) u fun t =>
      Holds (mashSpec d (Spec.Rc2.scheduleAt u.mem T) i v) t ∧ t.mem = u.mem ∧
        Keep [.a7, .t3, .t0, .t1, .t2, wordReg i] u t := by
  have o := wordReg_other i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at o
  unfold mash
  apply WP.seq
  refine WP.mono (mashIndex_run u hi) fun t₁ ⟨a₁, m₁, k₁⟩ => ?_
  let w := v.getD ((i + 3) % 4) 0
  have hidx : (w &&& 63#16).toNat < 64 := by
    rw [BitVec.toNat_and, show (63#16).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega_using []
  have hr : ∀ k < 16, InRegions (t₁.rd ++ t₁.wr) (T + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => by
    rw [k₁.2.1, k₁.2.2]; exact E.rd (8 * k) 8 (by omega_using [hk])
  have h3 : t₁.gpr .a2 = T := by rw [k₁.gpr (by decide)]; exact E.a2
  have hq : t₁.gpr .t0 = BitVec.ofNat 64 (2 * (w &&& 63#16).toNat) := by rw [a₁, H.nb i 3]; exact idx_val w
  apply WP.seq
  refine WP.mono (keyLookup_run t₁ h3 E.al hidx hq hr) fun t₂ ⟨a₂, k₂, m₂⟩ => ?_
  refine WP.mono (adjust_run t₂ (d == .decrypt) hi) fun t₃ ⟨a₃, m₃, k₃⟩ =>
    ⟨?_, by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  have x2 : t₂.gpr (wordReg i) = (v.getD i 0).setWidth 64 := by
    rw [k₂.gpr (by simp [o]), k₁.gpr (by simp [o])]
    exact H i hi
  have K : (Spec.Rc2.scheduleAt t₁.mem T) = Spec.Rc2.scheduleAt u.mem T := by rw [m₁]
  have hk := keep_others' hi (((k₁.trans k₂).trans k₃).mono (by simp))
  rw [K] at a₂
  cases d
  · show Holds (Spec.Rc2.mash _ i v) t₃
    refine H.set ?_ hk
    rw [a₃, x2, a₂, mask16]
    simp only [show (Spec.Rc2.Direction.encrypt == .decrypt) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine congrArg (BitVec.setWidth 64) ?_
    rw [lo16_add, lo16_ext, lo16_ext]; rfl
  · show Holds (Spec.Rc2.reverseMash _ i v) t₃
    refine H.set ?_ hk
    rw [a₃, x2, a₂, mask16]
    simp only [show (Spec.Rc2.Direction.decrypt == .decrypt) = true from rfl, ↓reduceIte]
    refine congrArg (BitVec.setWidth 64) ?_
    rw [lo16_sub, lo16_ext, lo16_ext]; rfl

end VG.Proof.Rc2.RISCV64

end

end

/-! ### `Rc2.RISCV64.Cbc.Io`, which this module and modules that import it used -/

section

/-!
# RC2-CBC on RISC-V: the blocks' bytes

The CBC code reads and writes the IV and the data a byte at a time, as
little-endian doublewords (`Bytes.loadLE64_ok`, `Bytes.storeLE64_ok`):
`before_run` and `after_run` state each of its blocks as the PPC64LE proofs'
single loads and stores (`Proof/Rc2/PPC64LE/Cbc/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc
open VG.Impl.Words.RISCV64 (loadLE64 storeLE64)

/-- The doubleword's second word, from the region holding the doubleword. -/
theorem in8_hi {rs : List Region} {p : Addr} (h : InRegions rs p 8) : InRegions rs (p + BitVec.ofNat 64 4) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : p + BitVec.ofNat 64 4 - r.base = p - r.base + BitVec.ofNat 64 4 := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 4),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((p - r.base).toNat + 4 % 2 ^ 64) (2 ^ 64)
  omega_using [hc]

theorem in8_lo {rs : List Region} {p : Addr} (h : InRegions rs p 8) : InRegions rs (p + BitVec.ofNat 64 0) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains, BitVec.add_zero] at hc ⊢
  omega_using [hc]

theorem load64_run {d n : Reg} (hdn : d ≠ n) (h7n : Reg.a7 ≠ n) (h1n : Reg.t1 ≠ n) (hd7 : d ≠ .a7)
    (hd1 : d ≠ .t1) (u : State) {p : Addr} (hp : u.gpr n = p) (hr : InRegions (u.rd ++ u.wr) p 8) :
    WP isa (.block (loadLE64 d .a7 .t1 n 0)) u fun t =>
      t.gpr d = u.mem.readW p 64 ∧ t.mem = u.mem ∧ Keep [d, .a7, .t1] u t := by
  rw [← hp] at hr
  refine WP.mono (Bytes.loadLE64_ok hdn h7n h1n hd7 hd1 (by decide) (by decide) (in8_lo hr) (in8_hi hr))
    fun t ⟨a, g, m, rd, wr, _⟩ => ⟨by rw [a, BitVec.add_zero, hp], m, fun r hr => ?_, rd, wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact g r hr.1 hr.2.1 hr.2.2

theorem store64_run {v n : Reg} (hv7 : Reg.a7 ≠ v) (h7n : Reg.a7 ≠ n) (h1n : Reg.t1 ≠ n) (u : State) {p : Addr}
    (hp : u.gpr n = p) (hw : InRegions u.wr p 8) :
    WP isa (.block (storeLE64 v .a7 .t1 n 0)) u fun t =>
      t.mem = u.mem.writeW p (u.gpr v) ∧ Keep [.a7, .t1] u t := by
  rw [← hp] at hw
  refine WP.mono (Bytes.storeLE64_ok hv7 h7n h1n (by decide) (by decide) (in8_lo hw) (in8_hi hw))
    fun t ⟨m, g, rd, wr, _⟩ => ⟨?_, fun r hr => ?_, rd, wr⟩
  · rw [m, BitVec.add_zero, show (0 + 4 : Nat) = 4 from rfl, Words64.writeW64_split, hp]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g r hr.1 hr.2

/-- The block at `s3` XORed with the chaining value at `s2`, in place. -/
theorem xorIv_run (u : State) {p I : Addr} (h3 : u.gpr .s3 = p) (h2 : u.gpr .s2 = I)
    (hpr : InRegions (u.rd ++ u.wr) p 8) (hpw : InRegions u.wr p 8) (hir : InRegions (u.rd ++ u.wr) I 8) :
    WP isa (.block xorIv) u fun t =>
      t.mem = u.mem.writeW p (u.mem.readW p 64 ^^^ u.mem.readW I 64) ∧ Keep [.t0, .a7, .t1, .t2] u t := by
  unfold xorIv
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (load64_run (d := .t0) (n := .s3) (p := p) (by decide) (by decide) (by decide) (by decide) (by decide)
    u h3 hpr) fun t₁ ⟨a₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load64_run (d := .t2) (n := .s2) (p := I) (by decide) (by decide) (by decide) (by decide)
    (by decide) t₁ (by rw [k₁.gpr (by decide), h2]) (by rw [k₁.2.1, k₁.2.2]; exact hir)) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  rw [List.singleton_append, WP.block_cons_iff]
  let t₃ := t₂.write .t0 (t₂.gpr .t0 ^^^ t₂.gpr .t2)
  have k₃ : Keep [.t0] t₂ t₃ := ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (by simpa using hr), rfl, rfl⟩
  refine ⟨t₃, rfl, ?_⟩
  refine WP.mono (store64_run (v := .t0) (n := .s3) (p := p) (by decide) (by decide) (by decide) t₃
    (by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), h3])
    (by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hpw)) fun t ⟨m, k⟩ =>
      ⟨?_, (((k₁.trans k₂).trans k₃).trans k).mono (by simp)⟩
  rw [m, RegUpd.mem_write, RegUpd.gpr_write_self, m₂, m₁, k₂.gpr (by decide), a₁, a₂, m₁]

theorem args_run (u : State) {T p W : Addr} (h1 : u.gpr .s1 = T) (h3 : u.gpr .s3 = p) (h5 : u.gpr .s5 = W) :
    WP isa (.block args) u fun t => t.gpr .a0 = T ∧ t.gpr .a1 = p ∧ t.gpr .a2 = W ∧ t.mem = u.mem ∧
      Keep [.a0, .a1, .a2] u t :=
  WP.mono (WP.keep [.a0, .a1, .a2] (c := .block args) (Q := fun t => t.gpr .a0 = T ∧ t.gpr .a1 = p ∧
      t.gpr .a2 = W ∧ t.mem = u.mem) (by unfold args; rrun [mov, h1, h3, h5]) (by rfl) rfl)
    fun _ ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, d, k⟩

theorem advance_run (u : State) {p : Addr} {X : BitVec 64} (h3 : u.gpr .s3 = p) (h4 : u.gpr .s4 = X) :
    WP isa (.block advance) u fun t => t.gpr .s3 = p + 8#64 ∧ t.gpr .s4 = X - 1#64 ∧ t.mem = u.mem ∧
      Keep [.s3, .s4] u t :=
  WP.mono (WP.keep [.s3, .s4] (c := .block advance) (Q := fun t => t.gpr .s3 = p + 8#64 ∧ t.gpr .s4 = X - 1#64 ∧
      t.mem = u.mem) (by unfold advance; rrun [h3, h4]) (by rfl) rfl)
    fun _ ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩

theorem beforeEnc_run (t : State) {T p I W : Addr} (h1 : t.gpr .s1 = T) (h2 : t.gpr .s2 = I)
    (h3 : t.gpr .s3 = p) (h5 : t.gpr .s5 = W) (hpr : InRegions (t.rd ++ t.wr) p 8) (hpw : InRegions t.wr p 8)
    (hir : InRegions (t.rd ++ t.wr) I 8) :
    WP isa (.block (before .encrypt)) t fun t₁ => t₁.gpr .a0 = T ∧ t₁.gpr .a1 = p ∧ t₁.gpr .a2 = W ∧
      t₁.mem = t.mem.writeW p (t.mem.readW p 64 ^^^ t.mem.readW I 64) ∧
      Keep [.t0, .a7, .t1, .t2, .a0, .a1, .a2] t t₁ := by
  unfold before
  rw [WP.block_append_iff]
  refine WP.mono (xorIv_run t h3 h2 hpr hpw hir) fun u ⟨m, k⟩ => ?_
  refine WP.mono (args_run u (by rw [k.gpr (by decide), h1]) (by rw [k.gpr (by decide), h3])
    (by rw [k.gpr (by decide), h5])) fun t₁ ⟨a, b, c, m₁, k₁⟩ => ⟨a, b, c, by rw [m₁, m], k.trans k₁⟩

theorem beforeDec_run (t : State) {T p W : Addr} (h1 : t.gpr .s1 = T) (h3 : t.gpr .s3 = p) (h5 : t.gpr .s5 = W)
    (hpr : InRegions (t.rd ++ t.wr) p 8) :
    WP isa (.block (before .decrypt)) t fun t₁ => t₁.gpr .a0 = T ∧ t₁.gpr .a1 = p ∧ t₁.gpr .a2 = W ∧
      t₁.gpr .s6 = t.mem.readW p 64 ∧ t₁.mem = t.mem ∧ Keep [.s6, .a7, .t1, .a0, .a1, .a2] t t₁ := by
  unfold before
  rw [WP.block_append_iff]
  refine WP.mono (load64_run (d := .s6) (n := .s3) (p := p) (by decide) (by decide) (by decide) (by decide)
    (by decide) t h3 hpr) fun u ⟨a₀, m, k⟩ => ?_
  refine WP.mono (args_run u (by rw [k.gpr (by decide), h1]) (by rw [k.gpr (by decide), h3])
    (by rw [k.gpr (by decide), h5])) fun t₁ ⟨a, b, c, m₁, k₁⟩ =>
      ⟨a, b, c, by rw [k₁.gpr (by decide), a₀], by rw [m₁, m], k.trans k₁⟩

theorem afterEnc_run (t : State) {p I : Addr} {X : BitVec 64} (h2 : t.gpr .s2 = I) (h3 : t.gpr .s3 = p)
    (h4 : t.gpr .s4 = X) (hpr : InRegions (t.rd ++ t.wr) p 8) (hiw : InRegions t.wr I 8) :
    WP isa (.block (after .encrypt ++ advance)) t fun t₃ => t₃.gpr .s3 = p + 8#64 ∧ t₃.gpr .s4 = X - 1#64 ∧
      t₃.mem = t.mem.writeW I (t.mem.readW p 64) ∧ Keep [.t0, .a7, .t1, .s3, .s4] t t₃ := by
  unfold after
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (load64_run (d := .t0) (n := .s3) (p := p) (by decide) (by decide) (by decide) (by decide)
    (by decide) t h3 hpr) fun u ⟨a₀, m₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (store64_run (v := .t0) (n := .s2) (p := I) (by decide) (by decide) (by decide) u
    (by rw [k₀.gpr (by decide), h2]) (by rw [k₀.2.2]; exact hiw)) fun u₁ ⟨m₁, k₁⟩ => ?_
  refine WP.mono (advance_run u₁ (by rw [k₁.gpr (by decide), k₀.gpr (by decide), h3])
    (by rw [k₁.gpr (by decide), k₀.gpr (by decide), h4])) fun t₃ ⟨a, b, m, k⟩ =>
      ⟨a, b, by rw [m, m₁, a₀, m₀], ((k₀.trans k₁).trans k).mono (by simp)⟩

theorem afterDec_run (t : State) {p I : Addr} {X c : BitVec 64} (h2 : t.gpr .s2 = I) (h3 : t.gpr .s3 = p)
    (h4 : t.gpr .s4 = X) (h6 : t.gpr .s6 = c) (hpr : InRegions (t.rd ++ t.wr) p 8) (hpw : InRegions t.wr p 8)
    (hir : InRegions (t.rd ++ t.wr) I 8) (hiw : InRegions t.wr I 8) :
    WP isa (.block (after .decrypt ++ advance)) t fun t₃ => t₃.gpr .s3 = p + 8#64 ∧ t₃.gpr .s4 = X - 1#64 ∧
      t₃.mem = (t.mem.writeW p (t.mem.readW p 64 ^^^ t.mem.readW I 64)).writeW I c ∧
      Keep [.t0, .a7, .t1, .t2, .s3, .s4] t t₃ := by
  unfold after
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorIv_run t h3 h2 hpr hpw hir) fun u ⟨m₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (store64_run (v := .s6) (n := .s2) (p := I) (by decide) (by decide) (by decide) u
    (by rw [k₀.gpr (by decide), h2]) (by rw [k₀.2.2]; exact hiw)) fun u₁ ⟨m₁, k₁⟩ => ?_
  refine WP.mono (advance_run u₁ (by rw [k₁.gpr (by decide), k₀.gpr (by decide), h3])
    (by rw [k₁.gpr (by decide), k₀.gpr (by decide), h4])) fun t₃ ⟨a, b, m, k⟩ =>
      ⟨a, b, by rw [m, m₁, m₀, k₀.gpr (by decide), h6], ((k₀.trans k₁).trans k).mono (by simp)⟩

end VG.Proof.Rc2.RISCV64.Cbc

end

end

/-! ### `Rc2.RISCV64.Cbc.Verified`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Cbc.Body`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Cbc.Call`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.Block`, which this module and modules that import it used -/

section

/-! ### `Rc2.RISCV64.BlockIO`, which only this module used -/

section

/-! # RC2 on RISC-V: loading and storing the block

The block is read and written a byte at a time, as a little-endian
doubleword (`Bytes.loadLE64_ok`, `Bytes.storeLE64_ok`), and split into the
words, or joined from them, as on PPC64LE (`Proof/Rc2/PPC64LE/Block.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem lane (x : BitVec 64) {i : Nat} (hi : i < 4) :
    (x <<< (48 - 16 * i)) >>> 48 = ((x >>> (16 * i)).setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j < 16
  · simp only [h, hj, decide_true, Bool.true_and, show 48 + j < 64 by omega_using [h], show ¬48 + j < 48 - 16 * i by omega_using [],
      decide_false, Bool.not_false]
    rw [show 48 + j - (48 - 16 * i) = 16 * i + j by omega_using [hi]]
  · simp only [h, show ¬48 + j < 64 by omega_using [h], decide_false, Bool.false_and, Bool.and_false]

theorem lane3 (x : BitVec 64) : x >>> 48 = ((x >>> (16 * 3)).setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  by_cases h : j < 16
  · simp [h, hj]
  · simp only [h, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge x (48 + j) (by omega_using [h])]
    simp

theorem blockLoad_run (u : State) (hr0 : InRegions (u.rd ++ u.wr) (u.gpr .a1) 4)
    (hr4 : InRegions (u.rd ++ u.wr) (u.gpr .a1 + BitVec.ofNat 64 4) 4) :
    WP isa (.block blockLoad) u fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .a1))) t ∧ t.mem = u.mem ∧
        Keep [.a3, .a4, .a5, .a6, .t1, .t2, .a7] u t := by
  refine WP.mono (WP.keep [.a3, .a4, .a5, .a6, .t1, .t2, .a7] (c := .block blockLoad) (Q := fun t =>
      Holds (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt u.mem (u.gpr .a1))) t ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold blockLoad
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (d := .t1) (tmp := .a7) (hi := .t2) (n := .a1) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hr0) hr4) fun s₁ ⟨h1, _, hm, _, _, _⟩ => ?_
  rw [BitVec.add_zero] at h1
  rrun [h1, hm]
  intro i hi
  rw [decode_read64 _ _ _ hi]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact lane _ (i := 0) (by decide)
  · exact lane _ (i := 1) (by decide)
  · exact lane _ (i := 2) (by decide)
  · exact lane3 _

theorem pack_or (v : Spec.Rc2.State) :
    (v.getD 1 0).setWidth 64 <<< 16 ||| (v.getD 0 0).setWidth 64 ||| (v.getD 2 0).setWidth 64 <<< 32 |||
      (v.getD 3 0).setWidth 64 <<< 48 = pack v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pack, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h₁ : j < 16
  · simp (disch := omega_arith) [h₁, hj, show j < 32 by omega_using [h₁], show j < 48 by omega_using [h₁]]
  · by_cases h₂ : j < 32
    · simp (disch := omega) [h₁, h₂, hj, show j < 48 by omega_using [h₂], show j - 16 < 64 by omega_using [hj], show j - 16 < 16 by omega_using [h₂],
        BitVec.getLsbD_of_ge]
    · by_cases h₃ : j < 48
      · simp (disch := omega) [h₁, h₂, h₃, hj, show j - 32 < 64 by omega_using [hj], show ¬j - 16 < 16 by omega_using [h₂],
          show j - 16 - 16 = j - 32 by omega_using [], show j - 32 < 16 by omega_using [h₃], BitVec.getLsbD_of_ge]
      · simp (disch := omega) [h₁, h₂, h₃, hj, show j - 48 < 64 by omega_using [hj], show ¬j - 16 < 16 by omega_using [h₂],
          show j - 16 - 16 = j - 32 by omega_using [], show ¬j - 32 < 16 by omega_using [h₃], show j - 32 - 16 = j - 48 by omega_using [],
          BitVec.getLsbD_of_ge]

theorem blockStore_run (u : State) {v : Spec.Rc2.State} (H : Holds v u)
    (hw0 : InRegions u.wr (u.gpr .a1) 4) (hw4 : InRegions u.wr (u.gpr .a1 + BitVec.ofNat 64 4) 4) :
    WP isa (.block blockStore) u fun t =>
      t.mem = u.mem.writeW (u.gpr .a1) (pack v) ∧ Keep [.t1, .t2, .a7] u t := by
  refine WP.mono (WP.keep [.t1, .t2, .a7] (c := .block blockStore) (Q := fun t =>
      t.mem = u.mem.writeW (u.gpr .a1) (pack v)) ?_
    (by rfl) rfl) fun t ⟨a, c⟩ => ⟨a, c⟩
  have h0 := H 0 (by decide)
  have h1 := H 1 (by decide)
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  rw [wordReg_0] at h0
  rw [wordReg_1] at h1
  rw [wordReg_2] at h2
  rw [wordReg_3] at h3
  unfold blockStore
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s₁ : State) => s₁.gpr .t1 = pack v ∧ s₁.gpr .a1 = u.gpr .a1 ∧ s₁.mem = u.mem ∧
      s₁.wr = u.wr) (by rrun [h0, h1, h2, h3]; exact pack_or v) fun s₁ ⟨e1, e2, e3, e4⟩ => ?_
  refine WP.mono (Bytes.storeLE64_ok (v := .t1) (tmp := .a7) (hi := .t2) (n := .a1) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [e2, e4]; simpa using hw0) (by rw [e2, e4]; exact hw4)) fun s₂ ⟨m₂, _⟩ => ?_
  rw [m₂, e1, e2, e3, BitVec.add_zero, Words64.writeW64_split]

end VG.Proof.Rc2.RISCV64

end

end

/-! ### `Rc2.RISCV64.Cipher`, which this module and modules that import it used -/

section

/-! # RC2 on RISC-V: composition of the sixteen rounds -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The registers the rounds write. -/
abbrev roundRegs : List Reg := [.a7, .t3, .a3, .a4, .a5, .a6, .t0, .t1, .t2]

/-- `c` maps the words to `g` of them, on memory `m` with the schedule at `T`. -/
def RunsTo (T : Addr) (m : Mem) (c : Prog isa) (g : Spec.Rc2.State → Spec.Rc2.State) : Prop :=
  ∀ u, KeyEnv T u → u.mem = m → ∀ v, Holds v u →
    WP isa c u fun t => Holds (g v) t ∧ t.mem = m ∧ Keep roundRegs u t

theorem roundRegs_append : ∀ r ∈ roundRegs ++ roundRegs, r ∈ roundRegs := fun r h => by
  rcases List.mem_append.1 h with h | h <;> exact h

theorem RunsTo.of_eq {T : Addr} {m : Mem} {c : Prog isa} {g g' : Spec.Rc2.State → Spec.Rc2.State}
    (h : RunsTo T m c g) (e : ∀ v, g v = g' v) : RunsTo T m c g' := fun u E hm v H =>
  WP.mono (h u E hm v H) fun _ ⟨a, b, c⟩ => ⟨e v ▸ a, b, c⟩

theorem RunsTo.nil {T : Addr} {m : Mem} : RunsTo T m (.block []) id := fun _ _ hm _ H =>
  WP.block_nil ⟨H, hm, Keep.refl _ _⟩

theorem RunsTo.seq {T : Addr} {m : Mem} {c₁ c₂ : Prog isa} {g₁ g₂ : Spec.Rc2.State → Spec.Rc2.State}
    (h₁ : RunsTo T m c₁ g₁) (h₂ : RunsTo T m c₂ g₂) : RunsTo T m (.seq c₁ c₂) (fun v => g₂ (g₁ v)) :=
  fun u E hm v H => WP.seq <| WP.mono (h₁ u E hm v H) fun t ⟨a, b, k⟩ =>
    WP.mono (h₂ t (E.keep k (by decide)) b _ a) fun t' ⟨a', b', k'⟩ =>
      ⟨a', b', (k.trans k').mono roundRegs_append⟩

theorem RunsTo.append {T : Addr} {m : Mem} {l₁ l₂ : List Instr} {g₁ g₂ : Spec.Rc2.State → Spec.Rc2.State}
    (h₁ : RunsTo T m (.block l₁) g₁) (h₂ : RunsTo T m (.block l₂) g₂) :
    RunsTo T m (.block (l₁ ++ l₂)) (fun v => g₂ (g₁ v)) := fun u E hm v H => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ u E hm v H) fun t ⟨a, b, k⟩ =>
    WP.mono (h₂ t (E.keep k (by decide)) b _ a) fun t' ⟨a', b', k'⟩ =>
      ⟨a', b', (k.trans k').mono roundRegs_append⟩

theorem RunsTo.foldr {T : Addr} {m : Mem} (f : Nat → Prog isa) (g : Nat → Spec.Rc2.State → Spec.Rc2.State)
    (l : List Nat) (h : ∀ i ∈ l, RunsTo T m (f i) (g i)) :
    RunsTo T m (l.foldr (fun i rest => .seq (f i) rest) (.block [])) (fun v => l.foldl (fun v i => g i v) v) := by
  induction l with
  | nil => exact RunsTo.nil
  | cons i l ih =>
    exact (RunsTo.seq (h i (by simp)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))).of_eq fun _ => rfl

theorem RunsTo.flatMap {T : Addr} {m : Mem} (f : Nat → List Instr) (g : Nat → Spec.Rc2.State → Spec.Rc2.State)
    (l : List Nat) (h : ∀ i ∈ l, RunsTo T m (.block (f i)) (g i)) :
    RunsTo T m (.block (l.flatMap f)) (fun v => l.foldl (fun v i => g i v) v) := by
  induction l with
  | nil => exact RunsTo.nil
  | cons i l ih =>
    rw [List.flatMap_cons]
    exact (RunsTo.append (h i (by simp)) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))).of_eq fun _ => rfl

theorem mix_regs : ∀ i < 4, ∀ r ∈ [Reg.a7, .t0, .t1, .t2, wordReg i], r ∈ roundRegs := by decide
theorem mash_regs : ∀ i < 4, ∀ r ∈ [Reg.a7, .t3, .t0, .t1, .t2, wordReg i], r ∈ roundRegs := by decide

theorem mix_runsTo {T : Addr} {m : Mem} {j i : Nat} (hj : j < 64) (hi : i < 4) :
    RunsTo T m (.block (mix j i)) (Spec.Rc2.mix (Spec.Rc2.scheduleAt m T) j i) := fun u E hm _ H =>
  WP.mono (mix_run u E H hj hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mix_regs i hi)⟩

theorem reverseMix_runsTo {T : Addr} {m : Mem} {j i : Nat} (hj : j < 64) (hi : i < 4) :
    RunsTo T m (.block (reverseMix j i)) (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m T) j i) := fun u E hm _ H =>
  WP.mono (reverseMix_run u E H hj hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mix_regs i hi)⟩

theorem mash_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {i : Nat} (hi : i < 4) :
    RunsTo T m (mash d i) (mashSpec d (Spec.Rc2.scheduleAt m T) i) := fun u E hm _ H =>
  WP.mono (mash_run u E H d hi) fun _ ⟨a, b, k⟩ => ⟨hm ▸ a, b.trans hm, k.mono (mash_regs i hi)⟩

def mixRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat) (v : Spec.Rc2.State) :
    Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mixRound k j v
  | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat) (v : Spec.Rc2.State) :
    Spec.Rc2.State :=
  if j = 4 ∨ j = 10 then mashRoundSpec d k (mixRoundSpec d k j v) else mixRoundSpec d k j v

theorem mixRound_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {j : Nat} (hj : j < 16) :
    RunsTo T m (.block (mixRound d j)) (mixRoundSpec d (Spec.Rc2.scheduleAt m T) j) := by
  cases d with
  | encrypt =>
    refine (RunsTo.flatMap (fun i => mix (4 * j + i) i)
      (fun i => Spec.Rc2.mix (Spec.Rc2.scheduleAt m T) (4 * j + i) i) (List.range 4) fun i hi => ?_).of_eq fun _ => rfl
    have := List.mem_range.1 hi
    exact mix_runsTo (by omega_using [hj, this]) this
  | decrypt =>
    refine (RunsTo.flatMap (fun i => reverseMix (4 * (15 - j) + i) i)
      (fun i => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m T) (4 * (15 - j) + i) i) [3, 2, 1, 0]
      fun i hi => ?_).of_eq fun _ => rfl
    have : i < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
    exact reverseMix_runsTo (by omega_using [this]) this

theorem order_lt (d : Spec.Rc2.Direction) : ∀ i ∈ order d, i < 4 := by cases d <;> decide

theorem mashRound_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) :
    RunsTo T m (mashRound d) (mashRoundSpec d (Spec.Rc2.scheduleAt m T)) :=
  (RunsTo.foldr _ _ _ fun i hi => mash_runsTo d (order_lt d i hi)).of_eq fun _ => by cases d <;> rfl

theorem round_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) {j : Nat} (hj : j < 16) :
    RunsTo T m (round d j) (roundSpec d (Spec.Rc2.scheduleAt m T) j) := by
  unfold round
  by_cases h : j = 4 ∨ j = 10
  · rw [ite_eq_left h]
    exact (RunsTo.seq (mixRound_runsTo d hj) (mashRound_runsTo d)).of_eq fun v => by
      simp only [roundSpec, ite_eq_left h]
  · rw [ite_eq_right h]
    exact (RunsTo.seq (mixRound_runsTo d hj) RunsTo.nil).of_eq fun v => by
      simp only [roundSpec, ite_eq_right h, id]

theorem rounds_runsTo {T : Addr} {m : Mem} (d : Spec.Rc2.Direction) :
    RunsTo T m (rounds d) (fun v => (List.range 16).foldl (fun v j => roundSpec d (Spec.Rc2.scheduleAt m T) j v) v) :=
  RunsTo.foldr _ _ _ fun _ hj => round_runsTo d (List.mem_range.1 hj)

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

end VG.Proof.Rc2.RISCV64

end

end

/-! # Verified RC2 block encryption and decryption on RISC-V

The rounds read the schedule (`rounds_runsTo`) at `a2`, between the
block's load and store: the schedule itself if it is aligned, else its copy
in the working space (`copyLoop_ok`), as `placeSchedule_run` proves.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-- The block contract as the code sees it. -/
def blockC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let data : Region := ⟨s.gpr .a1, 8⟩
    let scratch : Region := ⟨s.gpr .a2, 256⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 256 ≤ 2 ^ 64 ∧
      key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .a1) =
    cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .a0)) (Spec.Rc2.blockAt s.mem (s.gpr .a1))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem scheduleAt_copy {m m' : Mem} {S D : Addr}
    (h : ∀ i < 128, m' (D + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i)) :
    Spec.Rc2.scheduleAt m' D = Spec.Rc2.scheduleAt m S := by
  apply Vector.ext; intro i hi
  simp only [Spec.Rc2.scheduleAt, Vector.getElem_ofFn]
  rw [h _ (by omega_using [hi]), h _ (by omega_using [hi])]

/-- The schedule's copy: its bytes in the working space, the rest of memory
as it was. -/
theorem copySchedule_run (s : State) (hrd : s.rd = [⟨s.gpr .a0, 128⟩])
    (hwr : ∀ i < 128, InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr .a2) 128 (s.gpr .a0) 128) :
    WP isa copySchedule s fun t =>
      (∀ i < 128, t.mem (s.gpr .a2 + BitVec.ofNat 64 i) = s.mem (s.gpr .a0 + BitVec.ofNat 64 i)) ∧
      Frame [⟨s.gpr .a2, 128⟩] s.mem t.mem ∧ Keep [.t3, .t4, .t5, .a7] s t := by
  unfold copySchedule
  apply WP.seq
  refine WP.mono (WP.keep [.t3, .t4, .t5] (Q := fun u => u.gpr .t3 = s.gpr .a0 ∧ u.gpr .t4 = s.gpr .a2 ∧
      u.gpr .t5 = BitVec.ofNat 64 128 ∧ u.mem = s.mem) (by rrun) (by rfl) rfl) fun u ⟨⟨u3, u4, u5, um⟩, uk⟩ => ?_
  refine WP.mono (copyLoop_ok (tmp := .a7) (src := .t3) (dst := .t4) (cnt := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) u (N := 128) (by decide) (by decide) u5
    (fun i hi => by
      rw [uk.2.1, uk.2.2, u3, hrd]
      exact ⟨⟨s.gpr .a0, 128⟩, List.mem_append_left _ (List.mem_singleton_self _),
        Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => by rw [uk.2.2, u4]; exact hwr i hi) (by rw [u3, u4]; exact hsep))
    fun t ⟨tc, tf, tk⟩ => ⟨fun i hi => by rw [← u4, tc i hi, u3, um], by rw [← um, ← u4]; exact tf,
      (uk.trans tk).mono (by decide)⟩

/-- The schedule the rounds read, at `a2`: aligned, readable and holding the
schedule, the schedule itself or its copy; memory is changed only in the
working space's first 128 bytes. -/
theorem placeSchedule_run (s : State) (hrd : s.rd = [⟨s.gpr .a0, 128⟩])
    (hwr : ∀ i < 128, InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr .a2) 128 (s.gpr .a0) 128) (hal : (s.gpr .a2).toNat % 8 = 0)
    (hin : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .a2 + BitVec.ofNat 64 o) n) :
    WP isa placeSchedule s fun t =>
      (t.gpr .a2).toNat % 8 = 0 ∧
      (∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (t.gpr .a2 + BitVec.ofNat 64 o) n) ∧
      Spec.Rc2.scheduleAt t.mem (t.gpr .a2) = Spec.Rc2.scheduleAt s.mem (s.gpr .a0) ∧
      Frame [⟨s.gpr .a2, 128⟩] s.mem t.mem ∧ Keep [.t0, .t3, .t4, .t5, .a7, .a2] s t := by
  unfold placeSchedule
  apply WP.seq
  refine WP.mono (WP.keep [.t0] (Q := fun u => u.gpr .t0 = s.gpr .a0 &&& 7#64 ∧ u.mem = s.mem) (by rrun)
    (by rfl) rfl) fun u ⟨⟨u0, um⟩, uk⟩ => ?_
  have ga0 : u.gpr .a0 = s.gpr .a0 := uk.gpr (by decide)
  have ga2 : u.gpr .a2 = s.gpr .a2 := uk.gpr (by decide)
  refine WP.ite _ (rfl : isa.eval (.zero .t0) u = some (u.gpr .t0 == 0)) (fun hz => ?_) (fun hnz => ?_)
  · have h0 : s.gpr .a0 &&& 7#64 = 0 := by rw [← u0]; simpa using hz
    have hal0 : (s.gpr .a0).toNat % 8 = 0 := by
      have e := congrArg BitVec.toNat h0
      rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at e
      exact e
    refine WP.mono (WP.keep [.a2] (Q := fun t => t.gpr .a2 = s.gpr .a0 ∧ t.mem = s.mem) (by rrun [ga0, um])
      (by rfl) rfl) fun t ⟨⟨t2, tm⟩, tk⟩ => ?_
    refine ⟨by rw [t2]; exact hal0, fun o n hn => ?_, by rw [t2, tm], by rw [tm]; exact Frame.refl _ _,
      (uk.trans tk).mono (by decide)⟩
    rw [t2, hrd]
    exact ⟨⟨s.gpr .a0, 128⟩, List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ hn (by omega_using [hn])⟩
  · refine WP.mono (copySchedule_run u (by rw [uk.2.1, ga0]; exact hrd) (fun i hi => by
        rw [uk.2.2, ga2]; exact hwr i hi) (by rw [ga0, ga2]; exact hsep)) fun t ⟨tc, tf, tk⟩ => ?_
    have t2 : t.gpr .a2 = s.gpr .a2 := by rw [tk.gpr (by decide), ga2]
    refine ⟨by rw [t2]; exact hal, by rw [t2]; exact hin, ?_, by rw [← um, ← ga2]; exact tf,
      (uk.trans tk).mono (by decide)⟩
    rw [t2, ← ga2, ← ga0, ← um]
    exact scheduleAt_copy tc

theorem block_wp (d : Spec.Rc2.Direction) (s : State) (hs : (blockC d).pre s) :
    WP isa (blockCode d) s fun s' => (blockC d).post s s' := by
  obtain ⟨hrd, hwr, hal, hfit1, hfit2, hks, hds⟩ := hs
  have inScratch : ∀ o n, o + n ≤ 256 → InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_using [h])⟩
  have inData : ∀ o n, o + n ≤ 8 → InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_using [h])⟩
  unfold blockCode
  apply WP.seq
  refine WP.mono (placeSchedule_run s hrd (fun i hi => inScratch i 1 (by omega_using [hi]))
    (hks.symm.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
    (Region.contains_self _ _)) hal (fun o n hn => by
      obtain ⟨r, hr, hc⟩ := inScratch o n (by omega_using [hn]); exact ⟨r, List.mem_append_right _ hr, hc⟩))
    fun t₀ ⟨al₀, rd₀, K₀, f₀, k₀⟩ => ?_
  have p1₀ : t₀.gpr .a1 = s.gpr .a1 := k₀.gpr (by decide)
  have B₀ : Spec.Rc2.blockAt t₀.mem (s.gpr .a1) = Spec.Rc2.blockAt s.mem (s.gpr .a1) :=
    Proof.Rc2.blockAt_frame f₀ _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hds.sub_right fun a h => by simp only [Region.Contains] at h ⊢; omega_using [h]
  apply WP.seq
  refine WP.mono (blockLoad_run t₀ (by
      rw [p1₀, k₀.2.1, k₀.2.2]
      obtain ⟨r, hr, hc⟩ := inData 0 4 (by omega_using [])
      rw [BitVec.add_zero] at hc
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [p1₀, k₀.2.1, k₀.2.2]
        obtain ⟨r, hr, hc⟩ := inData 4 4 (by omega_using []); exact ⟨r, List.mem_append_right _ hr, hc⟩))
    fun t₁ ⟨H₁, m₁, k₁⟩ => ?_
  apply WP.seq
  have E : KeyEnv (t₀.gpr .a2) t₁ := ⟨k₁.gpr (by decide), al₀, fun o n hn => by
    rw [k₁.2.1, k₁.2.2, k₀.2.1, k₀.2.2]; exact rd₀ o n hn⟩
  refine WP.mono (rounds_runsTo d t₁ E rfl _ H₁) fun t₂ ⟨H₂, m₂, k₂⟩ => ?_
  have p4 : t₂.gpr .a1 = s.gpr .a1 := by rw [k₂.gpr (by decide), k₁.gpr (by decide), p1₀]
  refine WP.mono (blockStore_run t₂ H₂
    (by rw [p4, k₂.2.2, k₁.2.2, k₀.2.2]; simpa using inData 0 4 (by omega_using []))
    (by rw [p4, k₂.2.2, k₁.2.2, k₀.2.2]; exact inData 4 4 (by omega_using [])))
    fun t₃ ⟨m₃, _⟩ => ?_
  change Spec.Rc2.blockAt t₃.mem (s.gpr .a1) = _
  rw [m₃, p4, m₂, Proof.Rc2.blockAt_write64, cipher_rounds, m₁, K₀, p1₀, B₀]

/-- The registers the block functions write: no preserved register, nor `ra`. -/
def blockRegs : List Reg := [.a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5]

theorem block_ok (d : Spec.Rc2.Direction) (hw : writesOnly blockRegs (blockCode d) = true)
    (hn : callFree (blockCode d) = true) (s : State) (hs : (blockC d).pre s) :
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep blockRegs (block_wp d s hs) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

end VG.Proof.Rc2.RISCV64

end

end

/-! # RC2-CBC on RISC-V: the calls of the block function -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

theorem block_exec (d : Spec.Rc2.Direction) : ∀ s, (blockC d).pre s →
    ∃ t s', Exec isa (blockCode d) s t s' ∧ abiPreserved s s' ∧ (blockC d).post s s' := by
  cases d
  · exact block_ok .encrypt (by lit_decide) (by lit_decide)
  · exact block_ok .decrypt (by lit_decide) (by lit_decide)

theorem blockCall_eq (d : Spec.Rc2.Direction) :
    ∃ nm, blockCall d = .call nm (blockCode d) := by cases d <;> exact ⟨_, rfl⟩

theorem blockCode_noFrames (d : Spec.Rc2.Direction) : (blockCode d).noFrames = true := by
  cases d
  · exact (by lit_decide : encryptBlock.noFrames = true)
  · exact (by lit_decide : decryptBlock.noFrames = true)

/-- A call of the block function on the block at `p`, with the schedule at
`T` and the working space at `W`. -/
theorem call_run (d : Spec.Rc2.Direction) (u : State) {T p W : Addr} (h3 : u.gpr .a0 = T) (h4 : u.gpr .a1 = p)
    (h5 : u.gpr .a2 = W) (hal : W.toNat % 8 = 0) (hfp : p.toNat + 8 ≤ 2 ^ 64) (hfw : W.toNat + 256 ≤ 2 ^ 64)
    (hTW : (⟨T, 128⟩ : Region).Disjoint ⟨W, 256⟩) (hpW : (⟨p, 8⟩ : Region).Disjoint ⟨W, 256⟩)
    (hc : Covers ([⟨T, 128⟩] ++ [⟨p, 8⟩, ⟨W, 256⟩]) (u.rd ++ u.wr))
    (hw : Covers [⟨p, 8⟩, ⟨W, 256⟩] u.wr) :
    WP isa (blockCall d) u fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧
      Frame [⟨p, 8⟩, ⟨W, 256⟩] u.mem u'.mem ∧ (∀ r ∈ preserved, u'.gpr r = u.gpr r) ∧
      Spec.Rc2.blockAt u'.mem p = cipher d (Spec.Rc2.scheduleAt u.mem T) (Spec.Rc2.blockAt u.mem p) := by
  obtain ⟨nm, e⟩ := blockCall_eq d
  rw [e]
  have e3 : u.callEntry.gpr .a0 = T := by rw [State.callEntry_gpr u (by decide), h3]
  have e4 : u.callEntry.gpr .a1 = p := by rw [State.callEntry_gpr u (by decide), h4]
  have e5 : u.callEntry.gpr .a2 = W := by rw [State.callEntry_gpr u (by decide), h5]
  refine WP.call (k := blockC d) (block_exec d) (rd := [⟨T, 128⟩]) (wr := [⟨p, 8⟩, ⟨W, 256⟩]) ?_ hc hw
    (fun s' hr hwr _ hf hp _ hpost => ⟨hr, hwr, hf, hp, ?_⟩) (blockCode_noFrames d)
  · show [(⟨T, 128⟩ : Region)] = [⟨u.callEntry.gpr .a0, 128⟩] ∧
      [(⟨p, 8⟩ : Region), ⟨W, 256⟩] = [⟨u.callEntry.gpr .a1, 8⟩, ⟨u.callEntry.gpr .a2, 256⟩] ∧
      (u.callEntry.gpr .a2).toNat % 8 = 0 ∧ (u.callEntry.gpr .a1).toNat + 8 ≤ 2 ^ 64 ∧
      (u.callEntry.gpr .a2).toNat + 256 ≤ 2 ^ 64 ∧
      (⟨u.callEntry.gpr .a0, 128⟩ : Region).Disjoint ⟨u.callEntry.gpr .a2, 256⟩ ∧
      (⟨u.callEntry.gpr .a1, 8⟩ : Region).Disjoint ⟨u.callEntry.gpr .a2, 256⟩
    rw [e3, e4, e5]
    exact ⟨rfl, rfl, hal, hfp, hfw, hTW, hpW⟩
  · have := hpost
    simp only [blockC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem] at this
    rw [e3, e4] at this
    exact this

end VG.Proof.Rc2.RISCV64.Cbc

end

end

/-! ### `Rc2.RISCV64.Cbc.Step`, which only this module used -/

section

/-!
# RC2-CBC on RISCV64: one block

`body_run`: an iteration of the loop takes the invariant `Inv` from `j` blocks
done to `j + 1`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

/-- The buffers: the schedule at `T`, the chaining value at `I`, `n` blocks
at `D` and the working space at `W`, apart, not wrapping around, the working
space aligned. -/
structure Regions (T I D W : Addr) (n : Nat) : Prop where
  TI : (⟨T, 128⟩ : Region).Disjoint ⟨I, 8⟩
  TD : (⟨T, 128⟩ : Region).Disjoint ⟨D, 8 * n⟩
  TW : (⟨T, 128⟩ : Region).Disjoint ⟨W, 512⟩
  ID : (⟨I, 8⟩ : Region).Disjoint ⟨D, 8 * n⟩
  IW : (⟨I, 8⟩ : Region).Disjoint ⟨W, 512⟩
  DW : (⟨D, 8 * n⟩ : Region).Disjoint ⟨W, 512⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  fitW : W.toNat + 512 ≤ 2 ^ 64
  al : W.toNat % 8 = 0

/-- After `j` of the `n` blocks, from memory `m₀` and with our caller's
registers `g`. -/
structure Inv (d : Spec.Rc2.Direction) (T I D W : Addr) (n : Nat) (g : Reg → BitVec 64) (m₀ : Mem)
    (s₀ : State) (j : Nat) (t : State) : Prop where
  rd : t.rd = [⟨T, 128⟩]
  wr : t.wr = [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]
  s1 : t.gpr .s1 = T
  s2 : t.gpr .s2 = I
  s3 : t.gpr .s3 = D + BitVec.ofNat 64 (8 * j)
  s4 : t.gpr .s4 = BitVec.ofNat 64 (n - j)
  s5 : t.gpr .s5 = W
  pres : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → t.gpr r = s₀.gpr r
  saved : Spill.Saved W g saved t.mem
  sched : Spec.Rc2.scheduleAt t.mem T = Spec.Rc2.scheduleAt m₀ T
  done : Spec.Rc2.blocksAt t.mem D j =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).1
  iv : Spec.Rc2.blockAt t.mem I =
    (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I) (Spec.Rc2.blocksAt m₀ D j)).2
  rest : ∀ i, j ≤ i → i < n → Spec.Rc2.blockAt t.mem (D + BitVec.ofNat 64 (8 * i)) =
    Spec.Rc2.blockAt m₀ (D + BitVec.ofNat 64 (8 * i))

theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide
theorem saved_in : ∀ p ∈ saved, 256 ≤ p.2 ∧ p.2 + 8 ≤ 312 := by decide

/-- What a step leaves alone: anything apart from the block, the chaining
value and the block function's working space. -/
theorem step_frame {T I D W : Addr} {n j : Nat} (R : Regions T I D W n) (hj : j < n) {m m' : Mem}
    (F : Frame [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] m m') :
    Spec.Rc2.scheduleAt m' T = Spec.Rc2.scheduleAt m T ∧
    (∀ g, Spill.Saved W g saved m → Spill.Saved W g saved m') ∧
    (∀ i, i < n → i ≠ j → Spec.Rc2.blockAt m' (D + BitVec.ofNat 64 (8 * i)) =
      Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * i))) ∧
    Spec.Rc2.blocksAt m' D j = Spec.Rc2.blocksAt m D j := by
  have hf := R.fit
  obtain bj : Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  obtain W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨Proof.Rc2.scheduleAt_frame F T ?_, fun g sv => sv.frame F ?_, fun i hi hne => Proof.Rc2.blockAt_frame F _ ?_,
    Proof.Rc2.blocksAt_frame F D j ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact R.TD.sub_right bj
    · exact R.TI
    · exact R.TW.sub_right W256
  · intro p hp r hr
    obtain hb := saved_in p hp
    obtain slot : Region.Sub ⟨W + BitVec.ofNat 64 p.2, 8⟩ ⟨W, 512⟩ := Offset.sub_base W (by omega_using [hb])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (R.DW.sub_left bj).symm.sub_left slot
    · exact (R.IW.symm.sub_left slot)
    · exact Offset.disjoint_base W (by omega_using [hb]) (by omega_using [hb])
  · have bi : Region.Sub ⟨D + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hi])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.disjoint D (by omega_using [hne]) (by omega_using [hf, hi]) (by omega_using [hj, hf])
    · exact (R.ID.sub_right bi).symm
    · exact (R.DW.sub_left bi).sub_right W256
  · have bp : Region.Sub ⟨D, 8 * j⟩ ⟨D, 8 * n⟩ := Region.sub_prefix (by omega_using [hj])
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact Offset.base_disjoint D (by omega_using []) (by omega_using [hj, hf])
    · exact (R.ID.sub_right bp).symm
    · exact (R.DW.sub_left bp).sub_right W256

theorem blocksAt_one (m : Mem) (p : Addr) : Spec.Rc2.blocksAt m p 1 = [Spec.Rc2.blockAt m p] := by
  simp [Spec.Rc2.blocksAt]

/-- The done blocks, one more. -/
theorem done_succ (m : Mem) (D : Addr) (j : Nat) :
    Spec.Rc2.blocksAt m D (j + 1) = Spec.Rc2.blocksAt m D j ++ [Spec.Rc2.blockAt m (D + BitVec.ofNat 64 (8 * j))] := by
  rw [Proof.Rc2.blocksAt_add, blocksAt_one]

theorem covers {T I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers ([⟨T, 128⟩] ++ [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩])
      ([⟨T, 128⟩] ++ [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩]) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega_using [hj]⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

theorem covers_wr {I D W : Addr} {n j : Nat} (hj : j < n) :
    Covers [⟨D + BitVec.ofNat 64 (8 * j), 8⟩, ⟨W, 256⟩] [⟨I, 8⟩, ⟨D, 8 * n⟩, ⟨W, 512⟩] := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨D, 8 * n⟩, by simp, 8 * j, rfl, by simp; omega_using [hj]⟩
  · exact ⟨⟨W, 512⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

end VG.Proof.Rc2.RISCV64.Cbc

end

end


/-! # RC2-CBC on RISCV64: an iteration of the loop -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

theorem count_sub {n j : Nat} (hj : j < n) :
    BitVec.ofNat 64 (n - j) - 1#64 = BitVec.ofNat 64 (n - (j + 1)) := by
  rw [Offset.ofNat_sub_ofNat (by omega_using [hj])]; congr 1

theorem preserved_not : ∀ r ∈ preserved, r ∉ saved.map Prod.fst →
    r ∉ [Reg.t0, .a7, .t1, .t2, .a0, .a1, .a2, .s3, .s4, .s6] := by decide

theorem enc_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .encrypt iv [b] =
      ([Spec.Rc2.encryptBlock k (Proof.Rc2.xorBlock b iv)], Spec.Rc2.encryptBlock k (Proof.Rc2.xorBlock b iv)) := rfl

theorem dec_spec (k : Spec.Rc2.Schedule) (iv b : Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .decrypt iv [b] = ([Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock k b) iv], b) := rfl

theorem body_run (d : Spec.Rc2.Direction) {T I D W : Addr} {n : Nat} {g : Reg → BitVec 64} {m₀ : Mem} {s₀ : State}
    (R : Regions T I D W n) {j : Nat} (hj : j < n) (t : State) (H : Inv d T I D W n g m₀ s₀ j t) :
    WP isa (body d) t fun t' => Inv d T I D W n g m₀ s₀ (j + 1) t' ∧
      (t'.gpr .s4 != (0 : BitVec 64)) = !decide (j + 1 = n) := by
  have hf := R.fit
  let p := D + BitVec.ofNat 64 (8 * j)
  obtain pIn : InRegions t.wr p 8 := by
    rw [H.wr]; exact ⟨⟨D, 8 * n⟩, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hf])⟩
  obtain pIn' : InRegions (t.rd ++ t.wr) p 8 := by
    obtain ⟨r, hr, hc⟩ := pIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain iIn : InRegions t.wr I 8 := by rw [H.wr]; exact ⟨⟨I, 8⟩, by simp, Region.contains_self _ _⟩
  obtain iIn' : InRegions (t.rd ++ t.wr) I 8 := by
    obtain ⟨r, hr, hc⟩ := iIn; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain bj : Region.Sub ⟨p, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_using [hj])
  obtain pI : (⟨p, 8⟩ : Region).Disjoint ⟨I, 8⟩ := (R.ID.sub_right bj).symm
  have r28 : t.gpr .s3 = p := H.s3
  obtain b₀ : Spec.Rc2.blockAt t.mem p = Spec.Rc2.blockAt m₀ p := H.rest j (Nat.le_refl _) hj
  obtain hpt : p.toNat = D.toNat + 8 * j := by
    simp only [p, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 8 * j < 2 ^ 64 by omega_using [hj, hf]), Nat.mod_eq_of_lt (by omega_using [hj, hf])]
  obtain W256 : Region.Sub ⟨W, 256⟩ ⟨W, 512⟩ := Region.sub_prefix (by decide)
  have hfw := R.fitW
  obtain spec := Proof.Rc2.cbc_append (Spec.Rc2.scheduleAt m₀ T) d (Spec.Rc2.blockAt m₀ I)
    (Spec.Rc2.blocksAt m₀ D j) [Spec.Rc2.blockAt m₀ p]
  unfold body
  cases d with
  | encrypt =>
    apply WP.seq
    refine WP.mono (beforeEnc_run t H.s1 H.s2 r28 H.s5 pIn' pIn iIn')
      fun t₁ ⟨a3, a4, a5, m₁, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .encrypt t₁ a3 a4 a5 R.al (by omega_using [hj, hf, hpt]) (by omega_using [hfw]) (R.TW.sub_right W256)
      ((R.DW.sub_left bj).sub_right W256) (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    obtain g2 : ∀ r, r ∈ preserved → r ∉ [Reg.t0, .a7, .t1, .t2, .a0, .a1, .a2] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    obtain h27 : t₂.gpr .s2 = I := by rw [g2 _ (by decide) (by decide), H.s2]
    obtain h28 : t₂.gpr .s3 = p := by rw [g2 _ (by decide) (by decide), H.s3]
    obtain h29 : t₂.gpr .s4 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.s4]
    obtain pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    obtain iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    refine WP.mono (afterEnc_run t₂ h27 h28 h29 pIn₂ iIn₂) fun t₃ ⟨a28, a29, m₃, k₃⟩ => ?_
    -- the frame of the whole step
    obtain F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      refine Frame.trans (Frame.trans ?_ (F₂.mono (by simp))) ?_
      · rw [m₁]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
      · rw [m₃]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    -- the new block and chaining value
    obtain out : Spec.Rc2.blockAt t₂.mem p =
        Spec.Rc2.encryptBlock (Spec.Rc2.scheduleAt m₀ T) (Proof.Rc2.xorBlock (Spec.Rc2.blockAt m₀ p)
          (Spec.Rc2.blockAt t.mem I)) := by
      obtain hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by
        rw [m₁, Proof.Rc2.scheduleAt_frame (Proof.Rc2.frame_store64 _ _ _) T (by simpa using R.TD.sub_right bj),
          H.sched]
      rw [c₂, hs₁, m₁, Proof.Rc2.blockAt_xor, b₀]; rfl
    obtain b₃ : Spec.Rc2.blockAt t₃.mem p = Spec.Rc2.blockAt t₂.mem p := by
      rw [m₃]; exact Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI)
    obtain i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt t₂.mem p := by rw [m₃, Proof.Rc2.blockAt_copy]
    refine ⟨⟨by rw [k₃.2.1, rd₂, k₁.2.1, H.rd], by rw [k₃.2.2, wr₂, k₁.2.2, H.wr],
      by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s1], by rw [k₃.gpr (by decide), h27],
      by rw [a28, Offset.add_add]; congr 2,
      by rw [a29, count_sub hj], by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s5],
      fun r hr hn => ?_, fV g H.saved, by rw [fS, H.sched], ?_, ?_, fun i hi hn => ?_⟩, ?_⟩
    · have hn' := preserved_not r hr hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
      rw [k₃.gpr (by simp [hn']), g2 r hr (by simp [hn']), H.pres r hr hn]
    · rw [done_succ, done_succ, fD, H.done, spec, enc_spec, ← H.iv, b₃, out]
    · rw [done_succ, spec, enc_spec, ← H.iv, i₃, out]
    · rw [fB i hn (by omega_using [hi]), H.rest i (by omega_using [hi]) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero' (by omega_using [hf])]
      congr 1
      exact decide_eq_decide.mpr (by omega_using [hj])
  | decrypt =>
    apply WP.seq
    refine WP.mono (beforeDec_run t H.s1 r28 H.s5 pIn') fun t₁ ⟨a3, a4, a5, a31, m₁, k₁⟩ => ?_
    apply WP.seq
    refine WP.mono (call_run .decrypt t₁ a3 a4 a5 R.al (by omega_using [hj, hf, hpt]) (by omega_using [hfw]) (R.TW.sub_right W256)
      ((R.DW.sub_left bj).sub_right W256) (by rw [k₁.2.1, k₁.2.2, H.rd, H.wr]; exact covers hj)
      (by rw [k₁.2.2, H.wr]; exact covers_wr hj)) fun t₂ ⟨rd₂, wr₂, F₂, P₂, c₂⟩ => ?_
    obtain g2 : ∀ r, r ∈ preserved → r ∉ [Reg.s6, .a7, .t1, .a0, .a1, .a2] → t₂.gpr r = t.gpr r := fun r hr hn => by
      rw [P₂ r hr, k₁.gpr hn]
    obtain h27 : t₂.gpr .s2 = I := by rw [g2 _ (by decide) (by decide), H.s2]
    obtain h28 : t₂.gpr .s3 = p := by rw [g2 _ (by decide) (by decide), H.s3]
    obtain h29 : t₂.gpr .s4 = BitVec.ofNat 64 (n - j) := by rw [g2 _ (by decide) (by decide), H.s4]
    obtain h31 : t₂.gpr .s6 = t.mem.readW p 64 := by rw [P₂ _ (by decide), a31]
    obtain pIn₂ : InRegions (t₂.rd ++ t₂.wr) p 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact pIn'
    obtain pW₂ : InRegions t₂.wr p 8 := by rw [wr₂, k₁.2.2]; exact pIn
    obtain iIn₂ : InRegions t₂.wr I 8 := by rw [wr₂, k₁.2.2]; exact iIn
    obtain iIn₂' : InRegions (t₂.rd ++ t₂.wr) I 8 := by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact iIn'
    refine WP.mono (afterDec_run t₂ h27 h28 h29 h31 pIn₂ pW₂ iIn₂' iIn₂) fun t₃ ⟨a28, a29, m₃, k₃⟩ => ?_
    obtain F : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t.mem t₃.mem := by
      rw [← m₁]
      refine Frame.trans (F₂.mono (by simp)) ?_
      rw [m₃]
      obtain f₁ : Frame [⟨p, 8⟩, ⟨I, 8⟩, ⟨W, 256⟩] t₂.mem
          (t₂.mem.writeW p (t₂.mem.readW p 64 ^^^ t₂.mem.readW I 64)) :=
        (Frame.refl _ _).writeW (r := ⟨p, 8⟩) (by simp) _ (Region.contains_self _ _)
      exact f₁.writeW (r := ⟨I, 8⟩) (by simp) _ (Region.contains_self _ _)
    obtain ⟨fS, fV, fB, fD⟩ := step_frame R hj F
    obtain i₂ : Spec.Rc2.blockAt t₂.mem I = Spec.Rc2.blockAt t.mem I := by
      rw [Proof.Rc2.blockAt_frame F₂ I (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact pI.symm
        · exact R.IW.sub_right (Region.sub_prefix (by decide))), m₁]
    obtain hs₁ : Spec.Rc2.scheduleAt t₁.mem T = Spec.Rc2.scheduleAt m₀ T := by rw [m₁, H.sched]
    obtain b₃ : Spec.Rc2.blockAt t₃.mem p =
        Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt m₀ T) (Spec.Rc2.blockAt m₀ p))
          (Spec.Rc2.blockAt t.mem I) := by
      rw [m₃, Proof.Rc2.blockAt_frame (Proof.Rc2.frame_store64 _ _ _) _ (by simpa using pI),
        Proof.Rc2.blockAt_xor, i₂, c₂, hs₁, m₁, b₀]; rfl
    obtain i₃ : Spec.Rc2.blockAt t₃.mem I = Spec.Rc2.blockAt m₀ p := by
      rw [m₃, Proof.Rc2.blockAt_store64, ← Proof.Rc2.blockAt_read64, b₀]
    refine ⟨⟨by rw [k₃.2.1, rd₂, k₁.2.1, H.rd], by rw [k₃.2.2, wr₂, k₁.2.2, H.wr],
      by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s1], by rw [k₃.gpr (by decide), h27],
      by rw [a28, Offset.add_add]; congr 2,
      by rw [a29, count_sub hj], by rw [k₃.gpr (by decide), g2 _ (by decide) (by decide), H.s5],
      fun r hr hn => ?_, fV g H.saved, by rw [fS, H.sched], ?_, ?_, fun i hi hn => ?_⟩, ?_⟩
    · have hn' := preserved_not r hr hn
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
      rw [k₃.gpr (by simp [hn']), g2 r hr (by simp [hn']), H.pres r hr hn]
    · rw [done_succ, done_succ, fD, H.done, spec, dec_spec, ← H.iv, b₃]
    · rw [done_succ, spec, dec_spec, i₃]
    · rw [fB i hn (by omega_using [hi]), H.rest i (by omega_using [hi]) hn]
    · rw [a29, count_sub hj, ofNat_bne_zero' (by omega_using [hf])]
      congr 1
      exact decide_eq_decide.mpr (by omega_using [hj])

end VG.Proof.Rc2.RISCV64.Cbc

end

end

/-! # Verified RC2-CBC on RISCV64 -/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64 VG.Impl.Rc2.RISCV64.Cbc

/-- The CBC contract as the code sees it. -/
def cbcC (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a1, 8⟩
    let data : Region := ⟨s.gpr .a2, 8 * (s.gpr .a3).toNat⟩
    let buf : Region := ⟨s.gpr .a4, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ (s.gpr .a4).toNat % 8 = 0 ∧ key.Disjoint iv ∧ key.Disjoint data ∧
      key.Disjoint buf ∧ iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .a2).toNat + 8 * (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + 512 ≤ 2 ^ 64
  post s s' :=
    let result := Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt s.mem (s.gpr .a0)) d (Spec.Rc2.blockAt s.mem (s.gpr .a1))
      (Spec.Rc2.blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .a2) (s.gpr .a3).toNat = result.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .a1) = result.2
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

theorem save_eq : save = Spill.saveCode .a4 saved := rfl
theorem restore_eq : restore = Spill.restoreCode .s5 saved := rfl

theorem cbc_wp (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    WP isa (cbc d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.gpr .ra = s.gpr .ra ∧
      (cbcC d).post s s' := by
  obtain ⟨hrd, hwr, hal, TI, TD, TW, ID, IW, DW, fit, fitW⟩ := hs
  let T := s.gpr .a0
  let I := s.gpr .a1
  let D := s.gpr .a2
  let n := (s.gpr .a3).toNat
  let W := s.gpr .a4
  have R : Regions T I D W n := ⟨TI, TD, TW, ID, IW, DW, fit, fitW, hal⟩
  let g := s.gpr
  have wW : ∀ p ∈ saved, InRegions s.wr (s.gpr .a4 + BitVec.ofNat 64 p.2) 8 := fun p hp => by
    have hb := saved_in p hp
    rw [hwr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold cbc
  apply WP.seq
  rw [save_eq]
  refine Spill.save_ok hal saved_fits wW ?_
  let M₀ := Spill.saveMem s.mem (s.gpr .a4) g saved
  have F₀ : Frame [⟨W, 512⟩] s.mem M₀ := Spill.saveMem_frame_base (fun p hp => by have := saved_in p hp; omega_arith)
    (by decide) _ _ _
  refine WP.mono (WP.keep [.s1, .s2, .s3, .s4, .s5] (c := .block setup) (Q := fun t =>
      t.gpr .s1 = T ∧ t.gpr .s2 = I ∧ t.gpr .s3 = D ∧ t.gpr .s4 = s.gpr .a3 ∧ t.gpr .s5 = W ∧ t.mem = M₀)
    (by unfold setup; rrun [mov, T, I, D, W, M₀, g]) (by rfl) rfl)
    fun t₀ ⟨⟨a26, a27, a28, a29, a30, m₀⟩, k₀⟩ => ?_
  have H₀ : Inv d T I D W n g M₀ s 0 t₀ := by
    refine ⟨by rw [k₀.2.1]; exact hrd, by rw [k₀.2.2]; exact hwr, a26, a27, by rw [a28]; simp, by
      rw [a29, Nat.sub_zero]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm, a30,
      fun r hr hn => ?_, by rw [m₀]; exact Spill.saveMem_saved (by decide) _ _ _, by rw [m₀], by rw [m₀]; rfl,
      by rw [m₀]; rfl, fun i _ _ => by rw [m₀]⟩
    rw [k₀.gpr (by revert hn; revert r; decide)]
  apply WP.seq
  have loop : WP isa (.ite (.zero .s4) (.block []) (.loop (body d) (.nonzero .s4))) t₀
      (Inv d T I D W n g M₀ s n) := by
    have hz : isa.eval (.zero .s4) t₀ = some (decide (n = 0)) := by
      rw [Steps.eval_zero, H₀.s4, Nat.sub_zero, Steps.ofNat_beq_zero (by omega_arith)]
    refine WP.ite _ hz (fun h => WP.block_nil ?_) (fun h => countLoop _ _ _ n
      (fun j hj t H => body_run d R hj t H) 0 (by have := of_decide_eq_false h; omega_arith) t₀ H₀)
    have e : n = 0 := of_decide_eq_true h
    rw [e]; rw [e] at H₀; exact H₀
  refine WP.mono loop fun t H => ?_
  rw [restore_eq]
  refine WP.mono (Spill.restore_wp hal H.s5 saved_fits (by decide) (fun p hp => ?_) H.saved)
    fun t' Rs => ⟨fun r hr => ?_, ?_, ?_⟩
  · have hb := saved_in p hp
    rw [H.rd, H.wr]
    exact ⟨⟨W, 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · by_cases h : r ∈ saved.map Prod.fst
    · exact Rs.gpr_of (.inl h)
    · rw [Rs.other r h, H.pres r hr h]
  · exact Rs.gpr_of (.inl (by decide))
  · have hS : Spec.Rc2.scheduleAt M₀ T = Spec.Rc2.scheduleAt s.mem T :=
      Proof.Rc2.scheduleAt_frame F₀ T (by simpa using TW)
    have hI : Spec.Rc2.blockAt M₀ I = Spec.Rc2.blockAt s.mem I := Proof.Rc2.blockAt_frame F₀ I (by simpa using IW)
    have hD : Spec.Rc2.blocksAt M₀ D n = Spec.Rc2.blocksAt s.mem D n :=
      Proof.Rc2.blocksAt_frame F₀ D n (by simpa using DW)
    show Spec.Rc2.blocksAt t'.mem D n = _ ∧ Spec.Rc2.blockAt t'.mem I = _
    rw [Rs.mem, H.done, H.iv, hS, hI, hD]
    exact ⟨rfl, rfl⟩

theorem cbc_ok (d : Spec.Rc2.Direction) (s : State) (hs : (cbcC d).pre s) :
    ∃ t s', Exec isa (cbc d) s t s' ∧ abiPreserved s s' ∧ (cbcC d).post s s' := by
  obtain ⟨t, s', he, ⟨hp, hra, hq⟩, _, _, hsp⟩ := WP.rdwr (cbc_wp d s hs)
  exact ⟨t, s', he, ⟨hp, hsp, hra⟩, hq⟩

end VG.Proof.Rc2.RISCV64.Cbc

end

end

/-! # RC2-CBC in place on RISCV64, with wiped stack working space -/
-- separate module: exporting CBC does not rebuild its existing streaming callers.

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Cbc

open VG VG.RISCV64

def scratchSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩]

def frameSat : State := { scratchSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩] }

theorem encryptChained_ct : ConstantTime isa (cbcC .encrypt).pre (cbcC .encrypt).pub Impl.Rc2.RISCV64.Cbc.encrypt := by
  refine VG.Taint.constantTime (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptChained_verified :
    Verified RISCV64.target Impl.Rc2.RISCV64.Cbc.encrypt (Proof.Rc2.cbcEncChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := cbcC .encrypt) (cbc_ok .encrypt) encryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := by sig_implies_sat [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] [scratchSat] using scratchSat }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcEncChainedPost_of_blocks (r := 0) h.1 h.2

theorem encryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcEncryptChainedContract abi 512).pre s := by
  implies_sat [Spec.Rc2.cbcEncryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argRegs]
    [frameSat, scratchSat] using frameSat

theorem encryptChained_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.encrypt)
      (Spec.Rc2.cbcEncryptChainedContract abi 512) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 512) encryptChained_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcEncChainedPostOut_local _) encryptChainedFrameSat

theorem decryptChained_ct : ConstantTime isa (cbcC .decrypt).pre (cbcC .decrypt).pub Impl.Rc2.RISCV64.Cbc.decrypt := by
  refine VG.Taint.constantTime (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h₀, h₁, h₂, h₃, h₄, hsp⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptChained_verified :
    Verified RISCV64.target Impl.Rc2.RISCV64.Cbc.decrypt (Proof.Rc2.cbcDecChainedScratchContract abi 64) := by
  refine Verified.of_correct (k := cbcC .decrypt) (cbc_ok .decrypt) decryptChained_ct {
    pre := by sig_implies_pre [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    post := ?_
    pub := by sig_implies_pub [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    sat := by sig_implies_sat [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] [scratchSat] using scratchSat }
  intro s s' _ h
  sig_post [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, cbcC, abi, argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact Proof.Rc2.cbcDecChainedPost_of_blocks (r := 0) h.1 h.2

theorem decryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcDecryptChainedContract abi 512).pre s := by
  implies_sat [Spec.Rc2.cbcDecryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argRegs]
    [frameSat, scratchSat] using frameSat

theorem decryptChained_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a4 64 Impl.Rc2.RISCV64.Cbc.decrypt)
      (Spec.Rc2.cbcDecryptChainedContract abi 512) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 512) decryptChained_verified (by decide) (by decide) (by decide)
    (Proof.Rc2.cbcDecChainedPostOut_local _) decryptChainedFrameSat

end VG.Proof.Rc2.RISCV64.Cbc
