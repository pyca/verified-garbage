module

public import VerifiedGarbage.Impl.Scan.Arm
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Constant-time table lookups on ARMv7: choosing a row of eight words

`start` leaves the one-hot word of the index's row in `r2` and clears the
columns (`start_ok`); `rows` then leaves in column `c` the word of column `c`
of that row, negated in the columns that accumulate by `mla` (`rows_ok`,
`val`).
-/

@[expose] public section

namespace VG.Proof.Scan.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Scan.Arm

/-! ## Running blocks -/

/-- An immediate below 256 is encodable (no rotation). -/
theorem encodable_lt {v : BitVec 32} (h : v.toNat < 256) : encodable v = true := by
  unfold encodable
  rw [List.any_eq_true]
  exact ⟨0, by decide, by
    have hz : v.rotateLeft (2 * 0) = v := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [hi]
    rw [hz]; exact decide_eq_true h⟩

/-- `s` with the memory `m`, kept folded in symbolic execution. -/
abbrev putMem (s : State) (m : Mem) : State := { s with mem := m }

/-- `s` with the flags of `x - y`, kept folded. -/
abbrev putSub (s : State) (x y : BitVec 32) : State := subFlags s x y

section
variable {s : State}

/-- The value a data-processing instruction computes. -/
def dpv : DpOp → BitVec 32 → BitVec 32 → BitVec 32
  | .add, x, y => x + y | .sub, x, y => x - y | .and, x, y => x &&& y | .orr, x, y => x ||| y
  | .eor, x, y => x ^^^ y | .bic, x, y => x &&& ~~~y

/-- The value of a shifted register. -/
def shv : Shift → BitVec 32 → Nat → BitVec 32
  | .lsl, x, k => x <<< k | .lsr, x, k => x >>> k | .ror, x, k => x.rotateRight k

theorem exec_dpE {op : DpOp} {d n : Reg} {v : BitVec 32} (h : encodable v = true) :
    exec (.dp op d n (.imm v)) s = some (s.setReg d (dpv op (s.gpr n) v)) := by
  cases op <;> simp only [exec, Op2.eval, h, ite_true, Option.map_some, dpv]

theorem exec_dpI {op : DpOp} {d n : Reg} {v : BitVec 32} (h : v.toNat < 256) :
    exec (.dp op d n (.imm v)) s = some (s.setReg d (dpv op (s.gpr n) v)) := exec_dpE (encodable_lt h)

theorem exec_dpR {op : DpOp} {d n m : Reg} :
    exec (.dp op d n (.reg m)) s = some (s.setReg d (dpv op (s.gpr n) (s.gpr m))) := by
  cases op <;> rfl

theorem exec_dpS {op : DpOp} {d n m : Reg} {sh : Shift} {k : Nat} (h : 1 ≤ k ∧ k ≤ 31) :
    exec (.dp op d n (.shifted m sh k)) s = some (s.setReg d (dpv op (s.gpr n) (shv sh (s.gpr m) k))) := by
  cases op <;> cases sh <;> simp only [exec, Op2.eval, h, and_self, ite_true, Option.map_some, dpv, shv]

theorem exec_movI {d : Reg} {v : BitVec 32} (h : v.toNat < 256) :
    exec (.mov d (.imm v)) s = some (s.setReg d v) := by
  simp only [exec, Op2.eval, encodable_lt h, ite_true, Option.map_some]

theorem exec_movS {d m : Reg} {sh : Shift} {k : Nat} (h : 1 ≤ k ∧ k ≤ 31) :
    exec (.mov d (.shifted m sh k)) s = some (s.setReg d (shv sh (s.gpr m) k)) := by
  cases sh <;> simp only [exec, Op2.eval, h, and_self, ite_true, Option.map_some, shv]

theorem exec_subsI {d n : Reg} {v : BitVec 32} (h : v.toNat < 256) :
    exec (.subs d n (.imm v)) s = some ((putSub s (s.gpr n) v).setReg d (s.gpr n - v)) := by
  simp only [exec, Op2.eval, encodable_lt h, ite_true, Option.map_some, putSub]

theorem exec_mul {d n m : Reg} : exec (.mul d n m) s = some (s.setReg d (s.gpr n * s.gpr m)) := rfl

theorem exec_mla {d n m a : Reg} :
    exec (.mla d n m a) s = some (s.setReg d (s.gpr n * s.gpr m + s.gpr a)) := rfl

theorem exec_ldr' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4) :
    exec (.ldr t n off) s =
      some (s.setReg t (s.mem.readW (State.addr (s.gpr n + BitVec.ofNat 32 off)) 32)) := exec_ldr ho h

theorem exec_str' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4) :
    exec (.str t n off) s =
      some (putMem s (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t))) := exec_str ho h

end

section
variable (s : State)

theorem gpr_mem (m : Mem) (r : Reg) : (putMem s m).gpr r = s.gpr r := rfl
theorem mem_mem (m : Mem) : (putMem s m).mem = m := rfl
theorem rd_mem (m : Mem) : (putMem s m).rd = s.rd := rfl
theorem wr_mem (m : Mem) : (putMem s m).wr = s.wr := rfl
theorem sp_mem (m : Mem) : (putMem s m).sp = s.sp := rfl
theorem z_mem (m : Mem) : (putMem s m).z = s.z := rfl

theorem gpr_sub (x y : BitVec 32) (r : Reg) : (putSub s x y).gpr r = s.gpr r := rfl
theorem mem_sub (x y : BitVec 32) : (putSub s x y).mem = s.mem := rfl
theorem rd_sub (x y : BitVec 32) : (putSub s x y).rd = s.rd := rfl
theorem wr_sub (x y : BitVec 32) : (putSub s x y).wr = s.wr := rfl
theorem sp_sub (x y : BitVec 32) : (putSub s x y).sp = s.sp := rfl
theorem z_sub (x y : BitVec 32) : (putSub s x y).z = (x - y == 0) := rfl

end

/-- `srun [facts]`: symbolic execution of a block by `simp`, one instruction
at a time, the state a chain of `State.setReg`s, flag updates and memory
updates whose registers `RegUpd` reads. -/
tactic_template "srun" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp only [runBlock_cons, runStep_some, runBlock_nil,
                         exec_dpI, exec_dpR, exec_dpS, exec_movI, exec_movS, exec_mul, exec_mla, dpv, shv,
                         exec_subsI, exec_ldr', exec_str',
                         gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg,
                         gpr_mem, mem_mem, rd_mem, wr_mem, sp_mem, z_mem, gpr_sub, mem_sub, rd_sub, wr_sub, sp_sub, z_sub,
                         BitVec.reduceToNat, Option.some.injEq, exists_eq_left',
                         ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul,
                         Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, and_self, eq_self_iff_true,
                         true_and, and_true, List.cons_append, List.nil_append, $ls,*]))

/-! ## The one-hot word and the masks -/

/-- The one-hot word of the index `x`, as `oneHot` computes it. -/
def ohVal (x : BitVec 32) : BitVec 32 :=
  (1 + (1 &&& x >>> 3)) * (1 + (1 &&& x >>> 4) <<< 2 - (1 &&& x >>> 4)) *
    (1 + (1 &&& x >>> 5) <<< 4 - (1 &&& x >>> 5)) * (1 + (1 &&& x >>> 6) <<< 8 - (1 &&& x >>> 6)) *
    (1 + (1 &&& x >>> 7) <<< 16 - (1 &&& x >>> 7))

/-- `ohVal` of the index `32 a + b`: the 256 indices, as two ranges that
`decide` evaluates. -/
theorem ohVal_split : ∀ a < 8, ∀ b < 32,
    ohVal (BitVec.ofNat 32 (32 * a + b)) = BitVec.ofNat 32 (2 ^ ((32 * a + b) / 8)) := by decide

theorem ohVal_ofNat : ∀ n < 256, ohVal (BitVec.ofNat 32 n) = BitVec.ofNat 32 (2 ^ (n / 8)) := fun n h => by
  have := ohVal_split (n / 32) (by omega_using [h]) (n % 32) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

theorem ohVal_eq {x : BitVec 32} (h : x.toNat < 256) : ohVal x = BitVec.ofNat 32 (2 ^ (x.toNat / 8)) := by
  have := ohVal_ofNat x.toNat h
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

/-- The mask of row `n`, from the one-hot word of row `h`. -/
theorem rowMask_ofNat : ∀ h < 32, ∀ n < 32,
    ((1 : BitVec 32) &&& ~~~(BitVec.ofNat 32 (2 ^ h) >>> n)) - 1 = if h = n then BitVec.allOnes 32 else 0 := by
  decide

/-! ## The registers -/

theorem colReg_ne_r0 (c : Nat) : colReg c ≠ .r0 := by unfold colReg; split <;> decide
theorem colReg_ne_r1 (c : Nat) : colReg c ≠ .r1 := by unfold colReg; split <;> decide
theorem colReg_ne_r2 (c : Nat) : colReg c ≠ .r2 := by unfold colReg; split <;> decide
theorem colReg_ne_r3 (c : Nat) : colReg c ≠ .r3 := by unfold colReg; split <;> decide
theorem colReg_ne_r12 (c : Nat) : colReg c ≠ .r12 := by unfold colReg; split <;> decide
theorem colReg_ne_lr (c : Nat) : colReg c ≠ .lr := by unfold colReg; split <;> decide

theorem colReg_inj : ∀ c < 8, ∀ e < 8, colReg c = colReg e → c = e := by decide

/-- The registers `rows` writes. -/
def rowsRegs : List Reg := [.r0, .r1, .r2, .lr, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The registers `start` writes. -/
def startRegs : List Reg := [.r1, .r2, .r3, .lr, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem colReg_mem (c : Nat) : colReg c ∈ rowsRegs := by unfold colReg; split <;> decide

/-! ## The start -/

theorem start_ok (s : State) (hx : (s.gpr .r0).toNat < 256) :
    WP isa (.block start) s fun t =>
      t.gpr .r2 = BitVec.ofNat 32 (2 ^ ((s.gpr .r0).toNat / 8)) ∧ t.gpr .r3 = 1 ∧ (∀ c < 8, t.gpr (colReg c) = 0) ∧
      (∀ q, q ∉ startRegs → t.gpr q = s.gpr q) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold start oneHot ohStep clear
  srun []
  refine ⟨?_, fun c hc => ?_, fun q hq => ?_⟩
  · rw [← ohVal_eq hx]; rfl
  · rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 by omega_using [hc]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [startRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨h1, h2, h3, hl, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hq
    simp only [h1, h2, h3, hl, h4, h5, h6, h7, h8, h9, h10, h11, ite_false]

/-! ## A word -/

/-- A column's value of a word: negated in a column that accumulates by `mla`. -/
def val (c : Nat) (x : BitVec 32) : BitVec 32 := if mlaCol c then -x else x

theorem mul_allOnes (w : BitVec 32) : w * BitVec.allOnes 32 + 0 = -w := by
  show w * BitVec.allOnes 32 + 0#32 = -w
  rw [BitVec.add_zero, ← BitVec.neg_one_eq_allOnes, BitVec.mul_neg, BitVec.mul_one]

theorem mul_zero_add (w a : BitVec 32) : w * 0 + a = a := by
  show w * 0#32 + a = a
  rw [BitVec.mul_zero, BitVec.zero_add]

theorem or_and_allOnes (w : BitVec 32) : 0 ||| w &&& BitVec.allOnes 32 = w := by
  show 0#32 ||| w &&& BitVec.allOnes 32 = w
  rw [BitVec.and_allOnes, BitVec.zero_or]

theorem or_and_zero (w a : BitVec 32) : a ||| w &&& 0 = a := by
  show a ||| w &&& 0#32 = a
  rw [BitVec.and_zero, BitVec.or_zero]

/-- The word at `off` from `lr` into column `c`, if the row's mask is all
ones (`b`); the column is zero until then. -/
theorem word_ok (s : State) {c off : Nat} (ho : off < 4096) {b : Bool}
    (hm : s.gpr .r1 = if b then BitVec.allOnes 32 else 0) (ha : b = true → s.gpr (colReg c) = 0)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 off)) 4) :
    WP isa (.block (word off c)) s fun t =>
      t.gpr (colReg c) = (if b then val c (s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 off)) 32)
        else s.gpr (colReg c)) ∧
      (∀ q, q ≠ .r0 → q ≠ colReg c → t.gpr q = s.gpr q) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp := by
  unfold word val
  cases hk : mlaCol c
  · simp only [Bool.false_eq_true, ite_false]
    srun [ho, hin, colReg_ne_r0]
    refine ⟨?_, fun q h0 hc => by simp only [h0, hc, ite_false]⟩
    rw [hm]
    cases b
    · simp only [Bool.false_eq_true, ite_false, or_and_zero]
    · simp only [ite_true, ha rfl, or_and_allOnes]
  · simp only [ite_true]
    srun [ho, hin, colReg_ne_r0]
    refine ⟨?_, fun q h0 hc => by simp only [h0, hc, ite_false]⟩
    rw [hm]
    cases b
    · simp only [Bool.false_eq_true, ite_false, mul_zero_add]
    · simp only [ite_true, ha rfl, mul_allOnes]

/-! ## A row -/

/-- The row's mask: all ones in the index's row `h`, row `n + r` being bit
`r` of the one-hot word shifted right by `n`. -/
theorem rowMask_ok (s : State) {h n r : Nat} (hh : h < 32) (hn : n + r < 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 (2 ^ h) >>> n) (h3 : s.gpr .r3 = 1) :
    WP isa (.block (rowMask r)) s fun t =>
      t.gpr .r1 = (if decide (h = n + r) then BitVec.allOnes 32 else 0) ∧ (∀ q, q ≠ .r1 → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold rowMask
  by_cases hr : r = 0
  · subst hr
    simp only [ite_true]
    srun [h2, h3]
    refine ⟨?_, fun q hq => by simp only [hq, ite_false]⟩
    rw [rowMask_ofNat h hh n hn]
    simp only [Nat.add_zero, decide_eq_true_eq]
  · rw [ite_eq_right hr]
    obtain hk : 1 ≤ r ∧ r ≤ 31 := by omega_using [hr, hn]
    srun [h2, h3, hk]
    refine ⟨?_, fun q hq => by simp only [hq, ite_false]⟩
    rw [← BitVec.shiftRight_add, rowMask_ofNat h hh (n + r) hn]
    simp only [decide_eq_true_eq]

/-- Column `c` once the rows below `n` are done: the word of the index's
row `h`, if it is one of them. -/
def colVal (tab : Nat → Nat → BitVec 32) (h n c : Nat) : BitVec 32 := if h < n then val c (tab h c) else 0

theorem colVal_succ (tab : Nat → Nat → BitVec 32) (h n c : Nat) :
    (if decide (h = n) then val c (tab n c) else colVal tab h n c) = colVal tab h (n + 1) c := by
  unfold colVal
  by_cases he : h = n
  · subst he
    rw [decide_eq_true rfl, ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _)]
  · rw [decide_eq_false he, ite_eq_right Bool.false_ne_true]
    by_cases hl : h < n
    · rw [ite_eq_left hl, ite_eq_left (by omega_using [hl])]
    · rw [ite_eq_right hl, ite_eq_right (by omega_using [hl, he])]

/-- The registers a row writes. -/
def rowRegs : List Reg := [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem colReg_mem_row (c : Nat) : colReg c ∈ rowRegs := by unfold colReg; split <;> decide

/-- Row `r` of a group, row `n + r` of the table: its words `tab (n + r)`
into the columns, if it is the index's row `h`. -/
theorem row_ok (s : State) (offs : Nat → Nat → Nat) (tab : Nat → Nat → BitVec 32) {h n r : Nat} (hh : h < 32)
    (hn : n + r < 32) (h2 : s.gpr .r2 = BitVec.ofNat 32 (2 ^ h) >>> n) (h3 : s.gpr .r3 = 1)
    (hc : ∀ c < 8, s.gpr (colReg c) = colVal tab h (n + r) c) (ho : ∀ c < 8, offs r c < 4096)
    (hin : ∀ c < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 (offs r c))) 4)
    (hv : ∀ c < 8, s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 (offs r c))) 32 = tab (n + r) c) :
    WP isa (.block (row offs r)) s fun t =>
      (∀ c < 8, t.gpr (colReg c) = colVal tab h (n + r + 1) c) ∧ (∀ q, q ∉ rowRegs → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold row
  rw [WP.block_append_iff]
  refine WP.mono (rowMask_ok s hh hn h2 h3) fun u ⟨u1, uo, um, urd, uwr, usp⟩ => ?_
  -- Words `0 … e - 1` done.
  have step : ∀ e ≤ 8, WP isa (.block ((List.range e).flatMap fun c => word (offs r c) c)) u fun t =>
      (∀ c < 8, t.gpr (colReg c) = if c < e then colVal tab h (n + r + 1) c else colVal tab h (n + r) c) ∧
      (∀ q, q ∉ rowRegs → t.gpr q = s.gpr q) ∧ t.gpr .r1 = u.gpr .r1 ∧ t.gpr .lr = s.gpr .lr ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    intro e he
    induction e with
    | zero =>
      exact WP.block_nil ⟨fun c hc' => by
        rw [ite_eq_right (Nat.not_lt_zero c), uo _ (colReg_ne_r1 c), hc c hc'],
        fun q hq => uo q fun e => hq (by rw [e]; decide), rfl, uo _ (by decide), um, urd, uwr, usp⟩
    | succ e ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      refine WP.mono (ih (by omega_using [he])) fun t ⟨tc, tk, t1, tl, tm, trd, twr, tsp⟩ => ?_
      obtain he8 : e < 8 := by omega_using [he]
      refine WP.mono (word_ok t (c := e) (ho e he8) (b := decide (h = n + r)) (by rw [t1, u1])
        (fun hb => by
          rw [tc e he8, ite_eq_right (Nat.lt_irrefl e), colVal, ite_eq_right (by
            have := of_decide_eq_true hb; omega_using [this])])
        (by rw [trd, twr, tl]; exact hin e he8)) fun v ⟨va, vo, vm, vrd, vwr, vsp⟩ => ?_
      refine ⟨fun c hc' => ?_, fun q hq => ?_, ?_, ?_, vm.trans tm, vrd.trans trd, vwr.trans twr, vsp.trans tsp⟩
      · by_cases hce : c = e
        · subst hce
          rw [ite_eq_left (Nat.lt_succ_self c), va, tm, tl, hv c hc', tc c hc', ite_eq_right (Nat.lt_irrefl c),
            colVal_succ]
        · rw [vo _ (colReg_ne_r0 c) fun e' => hce (colReg_inj c hc' e he8 e'), tc c hc']
          by_cases hlt : c < e
          · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
          · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt, hce])]
      · rw [vo q (fun e' => hq (by rw [e']; decide)) fun e' => hq (by rw [e']; exact colReg_mem_row e), tk q hq]
      · rw [vo _ (by decide) (colReg_ne_r1 e).symm, t1]
      · rw [vo _ (by decide) (colReg_ne_lr e).symm, tl]
  refine WP.mono (step 8 (Nat.le_refl _)) fun t ⟨tc, tk, _, _, tm, trd, twr, tsp⟩ =>
    ⟨fun c hc' => ?_, tk, tm, trd, twr, tsp⟩
  rw [tc c hc', ite_eq_left hc']

/-! ## The rows -/

/-- Word `c` of row `r` of group `g` of the table at `P`, in the memory `m`. -/
def wordAt (m : Mem) (P : BitVec 32) (offs : Nat → Nat → Nat) (stride g r c : Nat) : BitVec 32 :=
  m.readW (State.addr (P + BitVec.ofNat 32 (stride * g) + BitVec.ofNat 32 (offs r c))) 32

/-- What `rows` needs: the one-hot word of row `h` in `r2`, 1 in `r3`, the
table's pointer `P` in `lr` and the columns zero; the count's slot, in the
working space at `r12`, writable; the table's words readable, at offsets
`ldr` encodes, and apart from that slot; and an encodable stride. -/
structure RowsPre (offs : Nat → Nat → Nat) (stride cnt : Nat) (h : Nat) (P : BitVec 32) (s : State) : Prop where
  hh : h < 32
  r2 : s.gpr .r2 = BitVec.ofNat 32 (2 ^ h)
  r3 : s.gpr .r3 = 1
  lr : s.gpr .lr = P
  cols : ∀ c < 8, s.gpr (colReg c) = 0
  hcnt : cnt < 4096
  slot : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 cnt)) 4
  hstride : encodable (BitVec.ofNat 32 stride) = true
  hoffs : ∀ r < 8, ∀ c < 8, offs r c < 4096
  rd : ∀ g < 4, ∀ r < 8, ∀ c < 8, InRegions (s.rd ++ s.wr)
    (State.addr (P + BitVec.ofNat 32 (stride * g) + BitVec.ofNat 32 (offs r c))) 4
  dis : ∀ g < 4, ∀ r < 8, ∀ c < 8, Region.Disjoint
    ⟨State.addr (P + BitVec.ofNat 32 (stride * g) + BitVec.ofNat 32 (offs r c)), 4⟩
    ⟨State.addr (s.gpr .r12 + BitVec.ofNat 32 cnt), 4⟩

/-- The table's words as the rows index them: row `n` is row `n % 8` of group `n / 8`. -/
def tabOf (m : Mem) (P : BitVec 32) (offs : Nat → Nat → Nat) (stride : Nat) (n c : Nat) : BitVec 32 :=
  wordAt m P offs stride (n / 8) (n % 8) c

/-- The state of `rows` from `s` with `g` groups done. -/
structure RowsAt (offs : Nat → Nat → Nat) (stride cnt : Nat) (h : Nat) (P : BitVec 32) (s : State) (g : Nat)
    (v : State) : Prop where
  cols : ∀ c < 8, v.gpr (colReg c) = colVal (tabOf s.mem P offs stride) h (8 * g) c
  r2 : v.gpr .r2 = BitVec.ofNat 32 (2 ^ h) >>> (8 * g)
  lr : v.gpr .lr = P + BitVec.ofNat 32 (stride * g)
  keep : ∀ q, q ∉ rowsRegs → v.gpr q = s.gpr q
  fr : Frame [⟨State.addr (s.gpr .r12 + BitVec.ofNat 32 cnt), 4⟩] s.mem v.mem
  left : v.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 cnt)) 32 = BitVec.ofNat 32 (4 - g)
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp

theorem left_step : ∀ g < 4, BitVec.ofNat 32 (4 - g) - 1 = BitVec.ofNat 32 (4 - (g + 1)) ∧
    (BitVec.ofNat 32 (4 - g) - 1 == 0) = decide (g + 1 = 4) := by decide

/-- A group: its eight rows, then on to the next. -/
theorem group_ok {offs : Nat → Nat → Nat} {stride cnt h : Nat} {P : BitVec 32} {s v : State}
    (hp : RowsPre offs stride cnt h P s) {g : Nat} (hg : g < 4) (hv : RowsAt offs stride cnt h P s g v) :
    WP isa (.block (group offs stride cnt)) v fun w =>
      RowsAt offs stride cnt h P s (g + 1) w ∧ w.z = decide (g + 1 = 4) := by
  have hh := hp.hh
  obtain v3 : v.gpr .r3 = 1 := (hv.keep _ (by decide)).trans hp.r3
  obtain v12 : v.gpr .r12 = s.gpr .r12 := hv.keep _ (by decide)
  -- A word of the table, read in a later memory.
  have rdw (u : State) (hm : u.mem = v.mem) (r : Nat) (hr : r < 8) (c : Nat) (hc : c < 8) :
      u.mem.readW (State.addr (P + BitVec.ofNat 32 (stride * g) + BitVec.ofNat 32 (offs r c))) 32 =
        tabOf s.mem P offs stride (8 * g + r) c := by
    rw [hm, hv.fr.readW (r := ⟨State.addr (P + BitVec.ofNat 32 (stride * g) + BitVec.ofNat 32 (offs r c)), 4⟩)
      (Region.contains_self _ _) (fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'; exact hp.dis g hg r hr c hc) (by decide), tabOf, wordAt,
      show (8 * g + r) / 8 = g by omega_using [hr], show (8 * g + r) % 8 = r by omega_using [hr]]
  -- Rows `0 … e - 1` done.
  have step : ∀ e ≤ 8, WP isa (.block ((List.range e).flatMap (row offs))) v fun u =>
      (∀ c < 8, u.gpr (colReg c) = colVal (tabOf s.mem P offs stride) h (8 * g + e) c) ∧
      (∀ q, q ∉ rowRegs → u.gpr q = v.gpr q) ∧ u.mem = v.mem ∧ u.rd = v.rd ∧ u.wr = v.wr ∧ u.sp = v.sp := by
    intro e he
    induction e with
    | zero => exact WP.block_nil ⟨hv.cols, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    | succ e ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      refine WP.mono (ih (by omega_using [he])) fun u ⟨uc, uk, um, urd, uwr, usp⟩ => ?_
      obtain he8 : e < 8 := by omega_using [he]
      obtain ul : u.gpr .lr = P + BitVec.ofNat 32 (stride * g) := (uk _ (by decide)).trans hv.lr
      refine WP.mono (row_ok u offs (tabOf s.mem P offs stride) (n := 8 * g) (r := e) hh (by omega_using [hg, he8])
        ((uk _ (by decide)).trans hv.r2) ((uk _ (by decide)).trans v3) uc (hp.hoffs e he8)
        (fun c hc => by rw [ul, urd, uwr, hv.rd, hv.wr]; exact hp.rd g hg e he8 c hc)
        (fun c hc => by rw [ul]; exact rdw u um e he8 c hc)) fun w ⟨wc, wk, wm, wrd, wwr, wsp⟩ => ?_
      exact ⟨wc, fun q hq => (wk q hq).trans (uk q hq), wm.trans um, wrd.trans urd, wwr.trans uwr, wsp.trans usp⟩
  unfold group
  rw [WP.block_append_iff]
  refine WP.mono (step 8 (Nat.le_refl _)) fun u ⟨uc, uk, um, urd, uwr, usp⟩ => ?_
  obtain u12 : u.gpr .r12 = s.gpr .r12 := (uk _ (by decide)).trans v12
  have hsl := hp.slot
  obtain hsl' : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 cnt)) 4 := by
    obtain ⟨R, hR, hc⟩ := hsl; exact ⟨R, List.mem_append_right _ hR, hc⟩
  have hcnt := hp.hcnt
  have hleft := hv.left
  unfold groupEnd
  srun [exec_dpE hp.hstride, u12, urd, uwr, hv.rd, hv.wr, hsl, hsl', hcnt, um, hleft]
  obtain ⟨l1, l2⟩ := left_step g hg
  refine ⟨⟨fun c hc => ?_, ?_, ?_, fun q hq => ?_, ?_, ?_, by simp only [rd_setReg, rd_sub]; exact urd.trans hv.rd,
    by simp only [wr_setReg, wr_sub]; exact uwr.trans hv.wr,
    by simp only [sp_setReg, sp_sub]; exact usp.trans hv.sp⟩,
    l2⟩
  · simp only [gpr_setReg, gpr_sub, colReg_ne_r0, colReg_ne_r2, colReg_ne_lr, ite_false]
    rw [show 8 * (g + 1) = 8 * g + 8 by omega_arith, uc c hc]
  · simp only [gpr_setReg, gpr_sub, reduceCtorEq, ite_true, ite_false]
    rw [uk _ (by decide), hv.r2, ← BitVec.shiftRight_add]; rfl
  · simp only [gpr_setReg, gpr_sub, reduceCtorEq, ite_true, ite_false]
    rw [uk _ (by decide), hv.lr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [rowsRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain hq' : q ∉ rowRegs := by
      simp only [rowRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hq.1, hq.2.1, hq.2.2.2.2⟩
    obtain hq'' : q ∉ rowsRegs := by
      simp only [rowsRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact hq
    simp only [gpr_setReg, gpr_sub, hq.1, hq.2.2.1, hq.2.2.2.1, ite_false]
    rw [uk q hq']
    exact hv.keep q hq''
  · exact hv.fr.writeW List.mem_cons_self _ (Region.contains_self _ _)
  · show Mem.readW (Mem.writeW _ _ _) _ 32 = _
    rw [Mem.readW_writeW_self32, l1]

/-- The rows: column `c` holds the word of column `c` of the index's row
`h`, row `h % 8` of group `h / 8`, negated if `mlaCol c`. -/
theorem rows_ok {offs : Nat → Nat → Nat} {stride cnt h : Nat} {P : BitVec 32} {s : State}
    (hp : RowsPre offs stride cnt h P s) :
    WP isa (rows offs stride cnt) s fun t =>
      (∀ c < 8, t.gpr (colReg c) = val c (wordAt s.mem P offs stride (h / 8) (h % 8) c)) ∧
      (∀ q, q ∉ rowsRegs → t.gpr q = s.gpr q) ∧
      Frame [⟨State.addr (s.gpr .r12 + BitVec.ofNat 32 cnt), 4⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  have hsl := hp.slot
  have hcnt := hp.hcnt
  unfold rows
  refine WP.seq (WP.mono (Q := RowsAt offs stride cnt h P s 0) ?_ fun s₁ h₁ => ?_)
  · srun [hsl, hcnt]
    refine ⟨fun c hc => ?_, ?_, ?_, fun q hq => ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [gpr_setReg, colReg_ne_r0, ite_false]
      rw [hp.cols c hc, colVal, ite_eq_right (Nat.not_lt_zero h)]
    · simp only [gpr_setReg, reduceCtorEq, ite_false]
      exact hp.r2
    · simp only [gpr_setReg, reduceCtorEq, ite_false]
      rw [Nat.mul_zero, BitVec.add_zero]; exact hp.lr
    · simp only [rowsRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp only [gpr_setReg, hq.1, ite_false]
    · exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
    · exact Mem.readW_writeW_self32 _ _ _
  refine WP.mono (Q := RowsAt offs stride cnt h P s 4) ?_ fun t ht =>
    ⟨fun c hc => ?_, ht.keep, ht.fr, ht.rd, ht.wr, ht.sp⟩
  · refine WP.loop (M := isa) (fun n (v : State) => ∃ g, n = 4 - g ∧ g < 4 ∧ RowsAt offs stride cnt h P s g v)
      ?_ 4 s₁ ⟨0, rfl, by decide, h₁⟩
    rintro n v ⟨g, rfl, hg, hv⟩
    refine WP.mono (group_ok hp hg hv) fun w ⟨hw, wz⟩ => ?_
    by_cases he : g + 1 = 4
    · exact .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, he ▸ hw⟩
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 4 - (g + 1), by omega_using [hg], g + 1,
        rfl, by omega_using [hg, he], hw⟩
  · rw [ht.cols c hc, colVal, ite_eq_left (by have := hp.hh; omega_using [this]), tabOf]

end VG.Proof.Scan.Arm
