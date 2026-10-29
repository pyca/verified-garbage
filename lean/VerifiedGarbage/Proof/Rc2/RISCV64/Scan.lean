module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
public import VerifiedGarbage.Impl.Rc2.RISCV64.Lookup
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# RC2 on RISC-V: the table scan

`scan_run`: `scan base rp rows lanes bits` leaves in `t1` the doubleword
of the table at `base` that holds byte offset `q` (in `t0`), shifted right
by `q`'s byte offset in it and kept to `bits` bits: the entry at `q`.
As on PPC64LE (`Proof/Rc2/PPC64LE/Scan.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

/-! ## The rows -/

/-- Row `k` holds offset `q` exactly when `(q XOR 8k) >> 3` is zero. -/
theorem row_hit (q : BitVec 64) {k : Nat} (hk : k < 2 ^ 58) :
    ((q ^^^ BitVec.ofNat 64 (8 * k)) >>> 3).toNat = 0 ↔ q.toNat / 8 = k := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_xor, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega_arith), Nat.shiftRight_xor_distrib]
  have e : (8 * k) >>> 3 = k := by rw [Nat.shiftRight_eq_div_pow]; omega_arith
  rw [e, Nat.shiftRight_eq_div_pow, show 2 ^ 3 = 8 from rfl]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases a : (q.toNat / 8).testBit i <;> cases b : k.testBit i <;> simp_all
  · intro h; rw [h, Nat.xor_self]

/-- The row's mask: zero if the row holds the entry, else all ones. -/
theorem rowMask_eq (v : BitVec 64) (h : v.toNat < 2 ^ 63) :
    ((v - 1#64) >>> 63) - 1#64 = if v.toNat = 0 then 0#64 else BitVec.allOnes 64 := by
  by_cases e : v.toNat = 0
  · have : v = 0#64 := BitVec.eq_of_toNat_eq (by simp [e])
    subst this; decide
  · rw [ite_eq_right e]
    have : (v - 1#64) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega_arith
    rw [this]; decide

theorem keep_row (d : BitVec 64) (c : Prop) [Decidable c] :
    d ^^^ (d &&& (if c then 0#64 else BitVec.allOnes 64)) = if c then d else 0#64 := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h, BitVec.and_zero, BitVec.xor_zero]
  · rw [ite_eq_right h, ite_eq_right h, BitVec.and_allOnes, BitVec.xor_self]

/-- The scan's start, row and lanes need these of their registers. -/
structure ScanRegs (base rp : Reg) : Prop where
  b0 : base ≠ .a7
  b10 : base ≠ .t0
  b11 : base ≠ .t1
  b12 : base ≠ .t2
  p0 : rp ≠ .a7
  p10 : rp ≠ .t0
  p11 : rp ≠ .t1
  p12 : rp ≠ .t2
  pb : rp ≠ base

/-- One row, `k`: the doubleword at `rp = T + 8k`, kept if it holds `q`. -/
theorem row_run {base rp : Reg} (R : ScanRegs base rp) (u : State) {T : Addr} {k : Nat} (hk : k < 32)
    (hT : u.gpr base = T) (hp : u.gpr rp = T + BitVec.ofNat 64 (8 * k))
    (hal : (T + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0)
    (hr : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (scanRow base rp)) u fun t =>
      t.gpr .t1 = u.gpr .t1 ||| (if (u.gpr .t0).toNat / 8 = k then
        u.mem.readW (T + BitVec.ofNat 64 (8 * k)) 64 else 0#64) ∧
      t.gpr .a7 = BitVec.ofNat 64 (8 * k) ∧ t.gpr rp = T + BitVec.ofNat 64 (8 * k) - BitVec.ofNat 64 8 ∧
      t.mem = u.mem := by
  have hv : (((u.gpr .t0) ^^^ BitVec.ofNat 64 (8 * k)) >>> 3).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := ((u.gpr .t0) ^^^ BitVec.ofNat 64 (8 * k)).isLt; omega_arith
  have e : T + BitVec.ofNat 64 (8 * k) - T = BitVec.ofNat 64 (8 * k) := Offset.add_sub_cancel_left _ _
  have b0 := R.b0; have b10 := R.b10; have b11 := R.b11; have b12 := R.b12
  have p0 := R.p0; have p10 := R.p10; have p11 := R.p11; have p12 := R.p12; have pb := R.pb
  unfold scanRow
  rrun [hT, hp, hr, hal, e, b0, b10, b11, b12, p0, p10, p11, p12, pb, Ne.symm b0, Ne.symm b10, Ne.symm b11,
    Ne.symm b12, Ne.symm p0, Ne.symm p10, Ne.symm p11, Ne.symm p12, Ne.symm pb]
  rw [rowMask_eq _ hv, keep_row]
  by_cases h : (u.gpr .t0).toNat / 8 = k
  · rw [ite_eq_left ((row_hit _ (by omega_arith)).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((row_hit _ (by omega_arith)).mp h')), ite_eq_right h]

/-- Before row `k`, the rows above it scanned. -/
structure RowInv (base rp : Reg) (s₀ : State) (T : Addr) (k : Nat) (u : State) : Prop where
  acc : u.gpr .t1 = if k < (s₀.gpr .t0).toNat / 8 then
    s₀.mem.readW (T + BitVec.ofNat 64 (8 * ((s₀.gpr .t0).toNat / 8))) 64 else 0#64
  ptr : u.gpr rp = T + BitVec.ofNat 64 (8 * k)
  keep : Keep [.a7, .t1, .t2, rp] s₀ u
  mem : u.mem = s₀.mem

/-- The rows from `k` down: `t1` is the doubleword holding `q`. -/
theorem rows_run {base rp : Reg} (R : ScanRegs base rp) {s₀ : State} {T : Addr} (hT : s₀.gpr base = T)
    (hal : T.toNat % 8 = 0) {rows : Nat} (hrows : rows ≤ 32) (_hq : (s₀.gpr .t0).toNat < 8 * rows)
    (hr : ∀ k < rows, InRegions (s₀.rd ++ s₀.wr) (T + BitVec.ofNat 64 (8 * k)) 8) :
    ∀ k < rows, ∀ u, RowInv base rp s₀ T k u →
      WP isa (.loop (.block (scanRow base rp)) (.nonzero .a7)) u fun t =>
        t.gpr .t1 = s₀.mem.readW (T + BitVec.ofNat 64 (8 * ((s₀.gpr .t0).toNat / 8))) 64 ∧
        Keep [.a7, .t1, .t2, rp] s₀ t ∧ t.mem = s₀.mem := by
  intro k hk u I
  refine WP.loop (M := isa) (fun n v => n < rows ∧ RowInv base rp s₀ T n v) (fun n v ⟨hn, J⟩ => ?_) k u ⟨hk, I⟩
  have nb : base ∉ [Reg.a7, .t1, .t2, rp] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨R.b0, R.b11, R.b12, Ne.symm R.pb⟩
  have n10 : Reg.t0 ∉ [Reg.a7, .t1, .t2, rp] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, by decide, by decide, Ne.symm R.p10⟩
  have hb : v.gpr base = T := by rw [J.keep.gpr nb]; exact hT
  have q : v.gpr .t0 = s₀.gpr .t0 := J.keep.gpr n10
  refine WP.mono (WP.keep [.a7, .t1, .t2, rp] (row_run R v (k := n) (by omega_arith) hb J.ptr
    (Spill.al8 hal (by omega_arith))
    (by rw [J.keep.2.1, J.keep.2.2]; exact hr n hn)) (by
      simp [writesOnly, Code.allInstrs_eq, instrs, scanRow, dstOf]) rfl) fun w ⟨⟨w11, w0, wp, wm⟩, wk⟩ => ?_
  have acc' : w.gpr .t1 = if n ≤ (s₀.gpr .t0).toNat / 8 then
      s₀.mem.readW (T + BitVec.ofNat 64 (8 * ((s₀.gpr .t0).toNat / 8))) 64 else 0#64 := by
    rw [w11, J.acc, q, J.mem]
    by_cases h1 : (s₀.gpr .t0).toNat / 8 = n
    · rw [ite_eq_right (by omega_arith), ite_eq_left h1, ite_eq_left (by omega_arith), h1, BitVec.zero_or]
    · by_cases h2 : n < (s₀.gpr .t0).toNat / 8
      · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left (by omega_arith), BitVec.or_zero]
      · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by omega_arith), BitVec.or_zero]
  rw [Steps.eval_nonzero, w0, ofNat_bne_zero' (by omega_arith)]
  by_cases h0 : n = 0
  · subst h0
    left
    refine ⟨by simp, ?_, (J.keep.trans wk).mono (by simp), wm.trans J.mem⟩
    rw [acc', ite_eq_left (Nat.zero_le _)]
  · right
    refine ⟨by simp; omega_arith, n - 1, by omega_arith, by omega_arith,
      ⟨?_, ?_, (J.keep.trans wk).mono (by simp), wm.trans J.mem⟩⟩
    · rw [acc']
      by_cases h : n ≤ (s₀.gpr .t0).toNat / 8
      · rw [ite_eq_left h, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right h, ite_eq_right (by omega_arith)]
    · rw [wp, show 8 * n = 8 * (n - 1) + 8 by omega_arith, ← Offset.add_add, BitVec.add_sub_cancel]

/-! ## The lane -/

theorem bitMask_eq (q : BitVec 64) {c : Nat} (hc : c < 64) :
    (q <<< (63 - c)) >>> 63 - 1#64 = if q.getLsbD c then 0#64 else BitVec.allOnes 64 := by
  have e : (q <<< (63 - c)) >>> 63 = if q.getLsbD c then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
        show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
        show ¬ (63 < 63 - c) by omega_arith, decide_false, Bool.not_false,
        show 63 - (63 - c) = c by omega_arith]
      cases q.getLsbD c <;> rfl
    · have : (q <<< (63 - c) >>> 63).getLsbD i = false := by
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
        simp only [show ¬ (63 + i < 64) by omega_arith, decide_false, Bool.false_and]
      rw [this]
      cases q.getLsbD c
      · simp
      · simp [h0]
  rw [e]
  cases q.getLsbD c <;> decide

theorem select_eq (x r : BitVec 64) (b : Bool) :
    ((x ^^^ r) &&& (if b then 0#64 else BitVec.allOnes 64)) ^^^ r = if b then r else x := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, BitVec.and_allOnes]
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · simp

theorem condShift_run (u : State) {c : Nat} (hc : c < 3) :
    WP isa (.block (condShift c)) u fun t =>
      t.gpr .t1 = (if (u.gpr .t0).getLsbD c then u.gpr .t1 >>> (8 * 2 ^ c) else u.gpr .t1) ∧
        t.mem = u.mem := by
  unfold condShift
  rrun [show 63 - c < 64 by omega_arith, show 8 * 2 ^ c < 64 by
    rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide]
  rw [bitMask_eq _ (by omega_arith), select_eq]

/-- The shift the lanes `ls` select for `q`. -/
def shiftSum (q : BitVec 64) : List Nat → Nat
  | [] => 0
  | c :: ls => (if q.getLsbD c then 8 * 2 ^ c else 0) + shiftSum q ls

theorem lanes_run (ls : List Nat) (hl : ∀ c ∈ ls, c < 3) :
    ∀ (u : State) (x : BitVec 64) (a : Nat), u.gpr .t1 = x >>> a →
      WP isa (.block (ls.flatMap condShift)) u fun t =>
        t.gpr .t1 = x >>> (a + shiftSum (u.gpr .t0) ls) ∧ t.gpr .t0 = u.gpr .t0 ∧
          t.mem = u.mem ∧ Keep [.a7, .t1, .t2] u t := by
  induction ls with
  | nil => intro u x a h; exact WP.block_nil ⟨by simpa [shiftSum] using h, rfl, rfl, Keep.refl _ _⟩
  | cons c ls ih =>
    intro u x a h
    rw [List.flatMap_cons, WP.block_append_iff]
    have hc : c < 3 := hl c List.mem_cons_self
    refine WP.mono (WP.keep [.a7, .t1, .t2] (condShift_run u hc) (by rfl) rfl) fun v ⟨⟨v11, vm⟩, vk⟩ => ?_
    have q : v.gpr .t0 = u.gpr .t0 := vk.gpr (by decide)
    have e : v.gpr .t1 = x >>> (a + (if (u.gpr .t0).getLsbD c then 8 * 2 ^ c else 0)) := by
      rw [v11, h]
      by_cases hb : (u.gpr .t0).getLsbD c
      · simp only [hb, ite_true]; rw [BitVec.shiftRight_add]
      · simp only [hb, Bool.false_eq_true, ite_false, Nat.add_zero]
    refine WP.mono (ih (fun c' h' => hl c' (List.mem_cons_of_mem _ h')) v x _ e)
      fun t ⟨t11, t10, tm, tk⟩ => ⟨?_, by rw [t10, q], by rw [tm, vm], (vk.trans tk).mono (by decide)⟩
    rw [t11, q]; simp only [shiftSum]; congr 1; omega_arith

theorem shl_shr (x : BitVec 64) {n : Nat} (hn : n ≤ 64) :
    (x <<< (64 - n)) >>> (64 - n) = (x.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i < n
  · simp [h, hi]; intro _; omega_arith
  · simp [h]; intro _; omega_arith

/-- The whole scan. -/
theorem scan_run {base rp : Reg} (R : ScanRegs base rp) (s : State) {T : Addr} (hT : s.gpr base = T)
    (hal : T.toNat % 8 = 0)
    {rows : Nat} (hrows : 1 ≤ rows ∧ rows ≤ 32) {lanes : List Nat} (hl : ∀ c ∈ lanes, c < 3)
    {bits : Nat} (hbits : 1 ≤ bits ∧ bits ≤ 64)
    (hq : (s.gpr .t0).toNat < 8 * rows)
    (hsum : shiftSum (s.gpr .t0) lanes = 8 * ((s.gpr .t0).toNat % 8))
    (hr : ∀ k < rows, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (scan base rp rows lanes bits) s fun t =>
      t.gpr .t1 = (((s.mem.readW (T + BitVec.ofNat 64 (8 * ((s.gpr .t0).toNat / 8))) 64) >>>
        (8 * ((s.gpr .t0).toNat % 8))).setWidth bits).setWidth 64 ∧
      Keep [.a7, .t1, .t2, rp] s t ∧ t.mem = s.mem := by
  have b11 := R.b11; have p11 := R.p11; have pb := R.pb
  unfold scan
  apply WP.seq
  refine WP.mono (WP.keep [.t1, rp] (Q := fun t => t.gpr .t1 = 0#64 ∧
      t.gpr rp = T + BitVec.ofNat 64 (8 * (rows - 1)) ∧ t.mem = s.mem) (by
        unfold scanStart
        rrun [hT, R.b0, b11, p11, Ne.symm p11, show 8 * (rows - 1) < 2048 by omega_arith]) (by
      simp [writesOnly, Code.allInstrs_eq, instrs, scanStart, dstOf]) rfl) fun u ⟨⟨u11, up, um⟩, uk⟩ => ?_
  apply WP.seq
  refine WP.mono (rows_run R hT hal hrows.2 hq hr (rows - 1) (by omega_arith) u
    ⟨by rw [u11, ite_eq_right (by omega_arith)], up, uk.mono (by simp), um⟩) fun v ⟨v11, vk, vm⟩ => ?_
  have q : v.gpr .t0 = s.gpr .t0 := vk.gpr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, by decide, by decide, Ne.symm R.p10⟩)
  rw [WP.block_append_iff]
  refine WP.mono (lanes_run lanes hl v
    (s.mem.readW (T + BitVec.ofNat 64 (8 * ((s.gpr .t0).toNat / 8))) 64) 0
      (by rw [BitVec.ushiftRight_zero]; exact v11)) fun w ⟨w11, w10, wm, wk⟩ => ?_
  refine WP.mono (WP.keep [.t1] (Q := fun t => t.gpr .t1 = ((w.gpr .t1).setWidth bits).setWidth 64 ∧
      t.mem = w.mem) (by unfold mask; rrun [show 64 - bits < 64 by omega_arith]; exact shl_shr _ hbits.2)
    (by rfl) rfl) fun t ⟨⟨t11, tm⟩, tk⟩ =>
      ⟨?_, ((vk.trans wk).trans tk).mono (by simp), by rw [tm, wm, vm]⟩
  rw [t11, w11, q, hsum, Nat.zero_add]

end VG.Proof.Rc2.RISCV64
