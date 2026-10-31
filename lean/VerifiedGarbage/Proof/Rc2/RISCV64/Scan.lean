module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Impl.Rc2.RISCV64.Lookup
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

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
      show ¬ (63 < 63 - c) by omega, decide_false, Bool.not_false, show 63 - (63 - c) = c by omega]
  rw [show (if 63 + i < 64 then (q <<< (63 - c)).getLsbD (63 + i) else (q <<< (63 - c)).getLsbD (64 - 1)) =
    (q <<< (63 - c)).getLsbD 63 by split; (congr 1; omega); rfl, key]
  cases q.getLsbD c
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true, show ¬ 64 ≤ i by omega, decide_false,
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
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
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
  rrun [hT, h3, hr, hal, b0, b12, b13, Ne.symm b0, Ne.symm b12, Ne.symm b13, show 63 - k < 64 by omega,
    show 8 * k < 2048 by omega]

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
    have r0 := hr 0 (by omega)
    simp only [Nat.mul_zero, BitVec.add_zero] at r0
    refine WP.mono (WP.keep [.a7, .t1, .t2] (row0_run R u ((hk.gpr nb).trans hT) h3 hal
      (by rw [hrd]; exact r0)) (by rfl) rfl) fun t ⟨⟨t1, tm⟩, tk⟩ =>
        ⟨?_, by rw [tk.gpr (by decide), h3], (hk.trans tk).mono (by decide), tm.trans hm⟩
    rw [t1, row_mask _ (by decide), keep_or, hm]
    by_cases h : (s₀.gpr .t0).toNat / 8 = 0
    · rw [ite_eq_left h, ite_eq_left (by omega), h, Nat.mul_zero, BitVec.add_zero]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  | succ n ih =>
    intro hn
    rw [rowsCode_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun v V => ?_
    have hrd : v.rd ++ v.wr = s₀.rd ++ s₀.wr := by rw [V.keep.2.1, V.keep.2.2]
    refine WP.mono (WP.keep [.a7, .t1, .t2] (row_run R v (k := n + 1) (by omega) ((V.keep.gpr nb).trans hT)
      V.bit (Spill.al8 hal (by omega)) (by rw [hrd]; exact hr _ hn)) (by rfl) rfl) fun t ⟨⟨t1, tm⟩, tk⟩ =>
        ⟨?_, by rw [tk.gpr (by decide), V.bit], (V.keep.trans tk).mono (by decide), tm.trans V.mem⟩
    rw [t1, V.acc, row_mask _ (by omega), keep_or, V.mem]
    by_cases h1 : (s₀.gpr .t0).toNat / 8 = n + 1
    · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left (by omega), h1, BitVec.zero_or]
    · by_cases h2 : (s₀.gpr .t0).toNat / 8 < n + 1
      · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left (by omega), BitVec.or_zero]
      · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by omega), BitVec.or_zero]

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
  rw [exec_logicImm (by unfold imm12; omega), BitVec.ofInt_natCast]

theorem lane_run (u : State) {laneBits : Nat} (hb : laneBits < 2048)
    (hlane : (u.gpr .t0 &&& BitVec.ofNat 64 laneBits).toNat = (u.gpr .t0).toNat % 8) :
    WP isa (.block (laneCode laneBits)) u fun t =>
      t.gpr .t1 = u.gpr .t1 >>> (8 * ((u.gpr .t0).toNat % 8)) ∧ t.mem = u.mem := by
  unfold laneCode
  rrun [↓exec_andi_nat, hb]
  have := Nat.mod_lt (u.gpr .t0).toNat (by decide : 8 > 0)
  rw [BitVec.toNat_shiftLeft, hlane, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
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
  refine WP.mono (WP.keep [.t2, .t3] (rowBit_run s (by omega)) (by rfl) rfl) fun u ⟨⟨u3, um⟩, uk⟩ => ?_
  refine WP.mono (rows_run R hT hal u3 (uk.mono (by decide)) um hrows.2 hr (rows - 1) (by omega)) fun v V => ?_
  have q : v.gpr .t0 = s.gpr .t0 := V.keep.gpr (by decide)
  refine WP.mono (WP.keep [.t1, .t2] (lane_run v hb (by rw [q]; exact hlane)) (by rfl) rfl)
    fun w ⟨⟨w1, wm⟩, wk⟩ => ?_
  refine WP.mono (WP.keep [.t1] (Q := fun t => t.gpr .t1 = ((w.gpr .t1).setWidth bits).setWidth 64 ∧
      t.mem = w.mem) (by unfold mask; rrun [show 64 - bits < 64 by omega_arith]; exact shl_shr _ hbits.2)
    (by rfl) rfl) fun t ⟨⟨t11, tm⟩, tk⟩ =>
      ⟨?_, ((V.keep.trans wk).trans tk).mono (by decide), by rw [tm, wm, V.mem]⟩
  rw [t11, w1, V.acc, q, ite_eq_left (by omega)]

end VG.Proof.Rc2.RISCV64
