module

public import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Lit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Batch
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.InstancePriority
public import VerifiedGarbage.Proof.Framework.PowLit
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.Framework.AArch64.StraightV

/-! ### `TripleDes.AArch64.Bitsliced.Loop`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Bitsliced.Copy`, which only this module used -/

section

/-!
# Copying words

`copy_ok`: the loop `copy` copies `n ≥ 1` words from `A` (in `x11`) to `B`
(in `x12`), where the two areas do not overlap, and changes nothing else in
memory. `x13` counts the words left, and `x10` holds each word.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Proof.TripleDes.Bitslice (wAt)

structure CopyPre (A B : Addr) (n : Nat) (s : State) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (wAt A i) 8
  write : ∀ i < n, InRegions s.wr (wAt B i) 8
  sep : (⟨A, 8 * n⟩ : Region).Disjoint ⟨B, 8 * n⟩
  fitA : 8 * n < 2 ^ 64

theorem wAt_succ (p : Addr) (i : Nat) : wAt p i + BitVec.ofNat 64 8 = wAt p (i + 1) := by
  simp only [wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2

/-- The registers the copy changes. -/
def CopyRegs (r : Reg) : Prop := r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

structure CopyInv (A B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i < n
  src : s.gpr .x11 = wAt A i
  dst : s.gpr .x12 = wAt B i
  cnt : s.gpr .x13 = BitVec.ofNat 64 (n - i)
  copied : ∀ j < i, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, CopyRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : s.v = s₀.v

structure CopyPost (A B : Addr) (n : Nat) (s₀ s : State) : Prop where
  copied : ∀ j < n, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, CopyRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : s.v = s₀.v

theorem wAt_in {p : Addr} {i n : Nat} (hi : i < n) (hn : 8 * n < 2 ^ 64) :
    (⟨p, 8 * n⟩ : Region).Contains (wAt p i) 8 :=
  Offset.contains_base p (by omega_arith) (by omega_arith)

theorem add_ofNat_zero (a : Addr) : a + BitVec.ofNat 64 0 = a := by simp

theorem copy_ok {A B : Addr} {n : Nat} {s₀ : State} (hpre : CopyPre A B n s₀) (s : State) (i : Nat)
    (hs : CopyInv A B n s₀ i s) : WP isa copy s (CopyPost A B n s₀) := by
  refine WP.loop (M := isa) (fun m s => CopyInv A B n s₀ (n - m) s ∧ m ≤ n) ?_ (n - i) s
    ⟨by rw [show n - (n - i) = i by have := hs.le; omega_arith]; exact hs, by omega_arith⟩
  intro m s ⟨inv, hm⟩
  let j := n - m
  have hj : j < n := inv.le
  let v := s₀.mem.readW (wAt A j) 64
  have hv : s.mem.readW (wAt A j) 64 = v :=
    inv.frame.readW (wAt_in hj hpre.fitA) (by simpa using hpre.sep) (by decide)
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x11 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero, inv.src, inv.rd, inv.wr]; exact hpre.read j hj
  let s₁ := s.write .x .x10 v
  have e₁ : exec (.ldr .x .x10 .x11 0) s = some s₁ := by
    rw [exec_ldr_x ⟨by decide, by decide⟩ hr, add_ofNat_zero, inv.src, hv]
  have hw : InRegions s₁.wr (s₁.gpr .x12 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero]
    have : (s.write .x .x10 v).gpr .x12 = s.gpr .x12 := by simp [State.write]
    show InRegions s.wr ((s.write .x .x10 v).gpr .x12) 8
    rw [this, inv.dst, inv.wr]; exact hpre.write j hj
  let s₂ : State := { s₁ with mem := s₁.mem.writeW (wAt B j) v }
  have e₂ : exec (.str .x .x10 .x12 0) s₁ = some s₂ := by
    rw [exec_str_x ⟨by decide, by decide⟩ hw, add_ofNat_zero]
    have h12 : s₁.gpr .x12 = wAt B j := by
      show (s.write .x .x10 v).gpr .x12 = _; simp [State.write, inv.dst]; rfl
    have h10 : s₁.gpr .x10 = v := by show (s.write .x .x10 v).gpr .x10 = _; simp [State.write]
    rw [h12, h10]
  let s₃ := s₂.write .x .x11 (s₂.read .x .x11 + BitVec.ofNat _ 8)
  let s₄ := s₃.write .x .x12 (s₃.read .x .x12 + BitVec.ofNat _ 8)
  let s₅ := s₄.write .x .x13 (s₄.read .x .x13 - BitVec.ofNat _ 1)
  have run : runBlock isa [.ldr .x .x10 .x11 0, .str .x .x10 .x12 0, .addImm .x .x11 .x11 8,
      .addImm .x .x12 .x12 8, .subImm .x .x13 .x13 1] s = some s₅ := by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₅, run, ?_⟩
  have g₅ : ∀ r, CopyRegs r → s₅.gpr r = s.gpr r := by
    intro r ⟨h1, h2, h3, h4⟩
    simp [s₅, s₄, s₃, s₂, s₁, State.write, h1, h2, h3, h4]
  have src₅ : s₅.gpr .x11 = wAt A (j + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read, inv.src]
    exact wAt_succ A j
  have dst₅ : s₅.gpr .x12 = wAt B (j + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read, inv.dst]
    exact wAt_succ B j
  have cnt₅ : s₅.gpr .x13 = s.gpr .x13 - 1 := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read]
  have mem₅ : s₅.mem = s.mem.writeW (wAt B j) v := rfl
  have copied₅ : ∀ x < j + 1, s₅.mem.readW (wAt B x) 64 = s₀.mem.readW (wAt A x) 64 := by
    intro x hx
    rw [mem₅]
    have fit := hpre.fitA
    by_cases he : x = j
    · subst he; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact inv.copied x (by omega_arith)
  have frame₅ : Frame [⟨B, 8 * n⟩] s₀.mem s₅.mem := by
    rw [mem₅]; exact inv.frame.writeW List.mem_cons_self _ (wAt_in hj hpre.fitA)
  have regs₅ : ∀ r, CopyRegs r → s₅.gpr r = s₀.gpr r := fun r hr => (g₅ r hr).trans (inv.regs r hr)
  have cntv : s₅.gpr .x13 = BitVec.ofNat 64 (m - 1) := by
    rw [cnt₅, inv.cnt, show n - j = m by omega_arith]
    exact cnt_sub m (by omega_arith)
  have flag : isa.eval (.nonzero .x .x13) s₅ = some (m - 1 != 0) := by
    show some (s₅.read .x .x13 != 0) = _
    have hlt : m - 1 < 2 ^ 64 := by have := hpre.fitA; omega_arith
    simp only [State.read, BitVec.setWidth_eq, cntv]
    congr 1
    by_cases h0 : m - 1 = 0
    · simp [h0]
    · have hne : BitVec.ofNat 64 (m - 1) ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this; simp at this; omega_arith
      change (BitVec.ofNat 64 (m - 1) != (0 : BitVec 64)) = (m - 1 != 0)
      simp only [bne, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]
  by_cases h1 : m = 1
  · left
    refine ⟨by rw [flag, h1]; rfl, ?_⟩
    exact ⟨fun x hx => copied₅ x (by omega_arith), frame₅, regs₅, inv.rd, inv.wr, inv.sp, inv.v⟩
  · right
    refine ⟨by rw [flag]; simp; omega_arith, m - 1, by omega_arith, ⟨?_, ?_, ?_, ?_, ?_, frame₅, regs₅, inv.rd,
      inv.wr, inv.sp, inv.v⟩, by omega_arith⟩
    · omega_arith
    · rw [src₅]; congr 2; omega_arith
    · rw [dst₅]; congr 2; omega_arith
    · rw [cntv]; congr 1; omega_arith
    · intro x hx; exact copied₅ x (by omega_arith)

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

end

/-! ### `TripleDes.AArch64.Bitsliced.Ecb`, which only this module used -/

section

/-!
# The function's environment

What the function may assume (`Env`), and the facts about it and about the
loop's counters that the loop's proof (`Loop.lean`) uses.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame toNat_ofNat_of_le ecb_blocks)

/-- What the function may assume of the state it starts in: the schedule
readable, the `n` blocks of data and the scratch buffer writable, apart from
each other. -/
structure Env (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 384⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 1024⟩]
  keyData : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 384⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 1024⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega_using [hc]
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega_using [h2]

theorem Env.len {s : State} (E : Env s) : 8 * (s.gpr .x2).toNat < 2 ^ 64 :=
  len_lt_of_disjoint E.dataBuf (by simp)

theorem Env.keyIn {s : State} (E : Env s) :
    ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8 := by
  intro i hi
  rw [E.rd]
  exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem blockAt_eq_of_readW {m m' : Mem} {p p' : Addr} (h : m'.readW p' 64 = m.readW p 64) :
    blockAt m' p' = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m' p' (n := 8) hi, ← Mem.extractLsb'_read m p (n := 8) hi]
  have e : ∀ (m : Mem) (p : Addr), m.read p 8 = m.readW p 64 := fun m p => by
    simp only [Mem.readW]; rfl
  rw [e, e, h]

theorem lsr7 (m : Nat) (hm : 8 * m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> 7 = BitVec.ofNat 64 (m / 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega_using [hm]), Nat.mod_eq_of_lt (by omega_using [hm])]

theorem ofNat_ne_zero {m : Nat} (h : m < 2 ^ 64) (h0 : m ≠ 0) : BitVec.ofNat 64 m ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  simp at this
  omega_using [h0, this]

theorem eval_nonzero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · change (BitVec.ofNat 64 m != (0 : BitVec 64)) = (m != 0)
    simp only [bne, beq_eq_false_iff_ne.mpr (ofNat_ne_zero hm h0), beq_eq_false_iff_ne.mpr h0]

theorem eval_zero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr (ofNat_ne_zero hm h0), beq_eq_false_iff_ne.mpr h0]

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

end

/-!
# The loop

Each iteration of `step` runs one batch: on the next 128 blocks in place
while that many are left, else on the `n mod 128 > 0` blocks left, copied
into the scratch buffer (at `x3`), whose other lanes hold whatever the buffer
held, and copied back; then no blocks are left (`step_ok`). Every block
becomes its encryption or decryption (`ecb_correct`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.StraightV VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame)

theorem exec_movz_x {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true]
  exact congrArg (fun v => some (s.write .x d v)) (BitVec.shiftLeft_zero _)

theorem wAt_zero (p : Addr) : wAt p 0 = p := by simp [wAt]

theorem scratch_word {B : Addr} {i : Nat} (hi : i < 128) :
    (⟨B, 1024⟩ : Region).Contains (wAt B i) 8 := Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

/-- The registers the loop changes. -/
def EcbRegs (r : Reg) : Prop :=
  r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x7 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧
    r ≠ .x13

/-- `m > 0` blocks left, a multiple of 128 fewer than `n`. -/
structure EcbInv (d : Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 0 < m
  le : m ≤ n
  mod : m % 128 = n % 128
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - m)
  gpr : ∀ r, EcbRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  done : ∀ b < n - m, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) d (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - m)⟩, ⟨s₀.gpr .x3, 1024⟩] s₀.mem s.mem

/-- Every block done. -/
def EcbPost (d : Direction) (s₀ : State) (n : Nat) (s : State) : Prop :=
  ∀ b < n, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) d (blockAt s₀.mem (wAt (s₀.gpr .x1) b))

theorem step_ok (d : Direction) {s₀ : State} (E : Env s₀) {n : Nat}
    (hn : (s₀.gpr .x2).toNat = n) (m : Nat) (s : State) (h : EcbInv d s₀ n m s) :
    WP isa (step d) s (fun s' =>
      (isa.eval (Cond.nonzero .x .x2) s' = some false ∧ EcbPost d s₀ n s') ∨
      (isa.eval (Cond.nonzero .x .x2) s' = some true ∧ ∃ m' < m, EcbInv d s₀ n m' s')) := by
  have hl := E.len
  have hfit := E.fit
  rw [hn] at hl hfit
  have hpos := h.pos
  have hle := h.le
  let D := s₀.gpr .x1
  let B := s₀.gpr .x3
  let S := s₀.gpr .x0
  have g := h.gpr
  obtain hx0 : s.gpr .x0 = S := g _ (by simp [EcbRegs])
  obtain hx3 : s.gpr .x3 = B := g _ (by simp [EcbRegs])
  obtain keyData : (⟨S, 384⟩ : Region).Disjoint ⟨D, 8 * n⟩ := hn ▸ E.keyData
  obtain dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 1024⟩ := hn ▸ E.dataBuf
  have keyB : (⟨S, 384⟩ : Region).Disjoint ⟨B, 1024⟩ := E.keyBuf
  obtain dataR : (⟨D, 8 * n⟩ : Region) ∈ s.wr := by rw [h.wr, E.wr, hn]; exact List.mem_cons_self
  obtain scrR : (⟨B, 1024⟩ : Region) ∈ s.wr := by
    rw [h.wr, E.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the schedule, and the blocks not yet done, as on entry
  obtain hK : scheduleAt s.mem S = scheduleAt s₀.mem S :=
    VG.Proof.TripleDes.scheduleAt_eq_of_frame S h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact keyData.sub_right (Region.sub_prefix (by omega_arith))
      · exact keyB
  obtain hB : ∀ j, j < m → blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
    fun j hj => blockAt_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
      · exact dataB.sub_left (Offset.sub_base _ (by omega_arith))
  rw [Impl.TripleDes.AArch64.BitsliceNeon.step]
  apply WP.seq
  let s₁ := s.write .x .x10 (s.read .x .x2 >>> 7)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  obtain x10₁ : s₁.gpr .x10 = BitVec.ofNat 64 (m / 128) := by
    simp only [s₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [h.x2, lsr7 _ (by omega_arith)]
  obtain g₁ : ∀ r, r ≠ .x10 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  apply WP.seq
  apply WP.ite _ (eval_zero s₁ .x10 x10₁ (by omega_arith))
  · -- the blocks left, through the scratch buffer
    intro hz
    obtain hm : m < 128 := by simp at hz; omega_arith
    let T := wAt D (n - m)
    obtain hx1 : s₁.gpr .x1 = T := (g₁ _ (by decide)).trans h.x1
    obtain dataW : ∀ i < m, InRegions s.wr (wAt T i) 8 := fun i hi =>
      ⟨_, dataR, by rw [wAt_wAt]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    obtain scrIn : ∀ i < 128, InRegions s.wr (wAt B i) 8 := fun i hi => ⟨_, scrR, scratch_word hi⟩
    obtain subT : Region.Sub ⟨T, 8 * m⟩ ⟨D, 8 * n⟩ := Offset.sub_base _ (by omega_arith)
    obtain dataSep : (⟨T, 8 * m⟩ : Region).Disjoint ⟨B, 8 * m⟩ :=
      (dataB.sub_left subT).sub_right (Region.sub_prefix (by omega_arith))
    unfold tailIn
    apply WP.seq
    -- x11 := x1, x12 := x3, x13 := x2
    let s₂ := ((s₁.write .x .x11 (s₁.read .x .x1 + BitVec.ofNat _ 0)).write .x .x12
      ((s₁.write .x .x11 (s₁.read .x .x1 + BitVec.ofNat _ 0)).read .x .x3 + BitVec.ofNat _ 0))
    let s₂' := s₂.write .x .x13 (s₂.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₂', by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    obtain g₂ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂'.gpr r = s.gpr r := by
      intro r a b c e; simp [s₂', s₂, gpr_write, b, c, e]; exact g₁ r a
    obtain pre₁ : CopyPre T B m s₂' := by
      refine ⟨fun i hi => ?_, fun i hi => scrIn i (by omega_arith), dataSep, by omega_arith⟩
      obtain ⟨r, hr, hc⟩ := dataW i hi
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    obtain inv₁ : CopyInv T B m s₂' 0 s₂' := by
      refine ⟨by omega_arith, ?_, ?_, ?_, fun j hj => by omega_arith, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₂', s₂, gpr_write, State.read]; exact hx1
      · rw [wAt_zero]; simp [s₂', s₂, gpr_write, State.read]; exact (g₁ _ (by decide)).trans hx3
      · simp [s₂', s₂, gpr_write, State.read]; rw [g₁ _ (by decide), h.x2]
    apply WP.seq
    apply WP.mono (copy_ok pre₁ s₂' 0 inv₁)
    intro s₃ c₃
    obtain g₃ : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₃.gpr r = s.gpr r :=
      fun r a b c e => (c₃.regs r ⟨a, b, c, e⟩).trans (g₂ r a b c e)
    -- x4 := x3
    let s₄ := s₃.write .x .x4 (s₃.read .x .x3 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₄, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    obtain g₄ : ∀ r, r ≠ .x4 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₄.gpr r = s.gpr r := by
      intro r a b c e f; simp only [s₄, State.write, a, ite_false]; exact g₃ r b c e f
    obtain x4₄ : s₄.gpr .x4 = B := by
      simp [s₄, gpr_write, State.read]
      exact (g₃ _ (by decide) (by decide) (by decide) (by decide)).trans hx3
    have wr₄ : s₄.wr = s.wr := c₃.wr
    obtain room₄ : Room s₄ := Ok.of_off (off := 0) (by rw [wr₄]; exact scrR)
      (by show s₄.gpr .x4 = _; rw [x4₄]; simp [B]) (by show 0 + 16 * 64 ≤ 1024; decide)
      (by show 1024 < 2 ^ 64; decide)
    obtain st₄ : stateR s₄ = ⟨B, 1024⟩ := by simp only [stateR, x4₄]
    obtain x0₄ : s₄.gpr .x0 = S :=
      (g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx0
    obtain S₄ : Sched s₄ := by
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [x0₄]
        show InRegions (s₃.rd ++ s₃.wr) _ 8
        rw [c₃.rd, c₃.wr]
        show InRegions (s.rd ++ s.wr) _ 8
        rw [h.rd, h.wr]; exact E.keyIn i hi
      · rw [x0₄, st₄]; exact keyB
    apply WP.seq
    apply WP.mono (batch_ok d room₄ S₄)
    intro s₅ q₅
    obtain g₅ : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
        r ≠ .x13 → s₅.gpr r = s.gpr r :=
      fun r a b c e f i j l => (q₅.gpr r b c e f).trans (g₄ r a f i j l)
    apply WP.seq
    let s₆ := s₅.write .x .x10 (s₅.read .x .x2 >>> 7)
    refine WP.of_runBlock ⟨s₆, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    obtain x2₅ : s₅.gpr .x2 = BitVec.ofNat 64 m :=
      (g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans h.x2
    obtain x10₆ : s₆.gpr .x10 = BitVec.ofNat 64 (m / 128) := by
      simp only [s₆, State.write, State.read, BitVec.setWidth_eq, ite_true]
      rw [x2₅, lsr7 _ (by omega_arith)]
    obtain g₆ : ∀ r, r ≠ .x10 → s₆.gpr r = s₅.gpr r := fun r hr => by simp [s₆, State.write, hr]
    apply WP.ite _ (eval_zero s₆ .x10 x10₆ (by omega_arith))
    swap
    · intro hnz; simp at hnz; omega_arith
    intro _
    unfold tailOut
    apply WP.seq
    -- x11 := x3, x12 := x1, x13 := x2
    let s₇ := ((s₆.write .x .x11 (s₆.read .x .x3 + BitVec.ofNat _ 0)).write .x .x12
      ((s₆.write .x .x11 (s₆.read .x .x3 + BitVec.ofNat _ 0)).read .x .x1 + BitVec.ofNat _ 0))
    let s₇' := s₇.write .x .x13 (s₇.read .x .x2 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₇', by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    obtain r₆ : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
        r ≠ .x13 → s₆.gpr r = s.gpr r :=
      fun r a b c e f i j l => (g₆ r f).trans (g₅ r a b c e f i j l)
    obtain wr₇ : s₇'.wr = s.wr := q₅.wr.trans wr₄
    obtain rd₇ : s₇'.rd = s.rd := q₅.rd.trans (c₃.rd)
    obtain pre₂ : CopyPre B T m s₇' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, dataSep.symm, by omega_arith⟩
      · obtain ⟨r, hr, hc⟩ := scrIn i (by omega_arith)
        rw [wr₇]; exact ⟨r, List.mem_append_right _ hr, hc⟩
      · rw [wr₇]; exact dataW i hi
    obtain inv₂ : CopyInv B T m s₇' 0 s₇' := by
      refine ⟨by omega_arith, ?_, ?_, ?_, fun j hj => by omega_arith, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
        rfl, rfl⟩
      · rw [wAt_zero]; simp [s₇', s₇, gpr_write, State.read]
        exact (r₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans hx3
      · rw [wAt_zero]; simp [s₇', s₇, gpr_write, State.read]
        exact (r₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans ((g₁ _ (by decide)).symm.trans hx1)
      · simp [s₇', s₇, gpr_write, State.read]
        rw [r₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h.x2]
    apply WP.seq
    apply WP.mono (copy_ok pre₂ s₇' 0 inv₂)
    intro s₈ c₈
    -- x2 := 0
    let s₉ := s₈.write .x .x2 ((0 : BitVec 16).setWidth 64)
    refine WP.of_runBlock ⟨s₉, by rw [runBlock_cons, exec_movz_x, runStep_some, runBlock_nil], ?_⟩
    left
    refine ⟨eval_nonzero s₉ .x2 (m := 0) (by simp [s₉, State.write]) (by decide), fun b hb => ?_⟩
    have m₉ : s₉.mem = s₈.mem := rfl
    have m₄ : s₄.mem = s₃.mem := rfl
    have m₇ : s₇'.mem = s₆.mem := rfl
    have m₆ : s₆.mem = s₅.mem := rfl
    have m₂ : s₂'.mem = s₁.mem := rfl
    have m₁ : s₁.mem = s.mem := rfl
    show blockAt s₉.mem (wAt D b) = blockOut (scheduleAt s₀.mem S) d (blockAt s₀.mem (wAt D b))
    rw [m₉]
    by_cases hb' : b < n - m
    · -- a block done before: untouched since
      rw [← h.done b hb']
      obtain f₃ : Frame [⟨B, 8 * m⟩] s.mem s₃.mem := by rw [← m₁, ← m₂]; exact c₃.frame
      obtain f₅ : Frame [⟨B, 1024⟩] s₃.mem s₅.mem := by rw [← m₄, ← st₄]; exact q₅.frame
      obtain f₈ : Frame [⟨T, 8 * m⟩] s₅.mem s₈.mem := by rw [← m₆, ← m₇]; exact c₈.frame
      obtain hT : (⟨wAt D b, 8⟩ : Region).Disjoint ⟨T, 8 * m⟩ :=
        Offset.disjoint D (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      obtain hS : (⟨wAt D b, 8⟩ : Region).Disjoint ⟨B, 1024⟩ :=
        dataB.sub_left (Offset.sub_base _ (by omega_arith))
      rw [blockAt_frame f₈ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hT),
        blockAt_frame f₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hS),
        blockAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hS.sub_right (Region.sub_prefix (by omega_arith)))]
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega_arith⟩
      obtain hj : j < m := by omega_arith
      -- the block in the data, from the scratch buffer after the batch
      obtain e₈ : blockAt s₈.mem (wAt D (n - m + j)) = blockAt s₅.mem (wAt B j) := by
        rw [← wAt_wAt, ← m₆, ← m₇]; exact blockAt_eq_of_readW (c₈.copied j hj)
      -- the block in the scratch buffer before the batch, from the data
      obtain e₃ : blockAt s₃.mem (wAt B j) = blockAt s.mem (wAt D (n - m + j)) := by
        rw [← wAt_wAt, ← m₁, ← m₂]; exact blockAt_eq_of_readW (c₃.copied j hj)
      obtain K₃ : scheduleAt s₃.mem S = scheduleAt s.mem S := by
        rw [← m₁, ← m₂]
        exact VG.Proof.TripleDes.scheduleAt_eq_of_frame S c₃.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact keyB.sub_right (Region.sub_prefix (by omega_arith))
      obtain o := q₅.out j (by omega_arith)
      rw [x4₄, x0₄, m₄, e₃, K₃, hK, hB j hj] at o
      rw [e₈, o]
  · -- the next 128 blocks, in place
    intro hnz
    obtain hm : 128 ≤ m := by simp at hnz; omega_arith
    let s₂ := s₁.write .x .x4 (s₁.read .x .x1 + BitVec.ofNat _ 0)
    refine WP.of_runBlock ⟨s₂, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    obtain g₂ : ∀ r, r ≠ .x4 → r ≠ .x10 → s₂.gpr r = s.gpr r := fun r a b => by
      simp only [s₂, State.write, a, ite_false]; exact g₁ r b
    obtain x4₂ : s₂.gpr .x4 = wAt D (n - m) := by
      simp [s₂, State.write, State.read]; exact (g₁ _ (by decide)).trans h.x1
    obtain room₂ : Room s₂ := Ok.of_off (off := 8 * (n - m)) (show _ ∈ s.wr from dataR)
      (by show s₂.gpr .x4 = _; rw [x4₂]) (by show 8 * (n - m) + 16 * 64 ≤ 8 * n; omega_arith) (by omega_arith)
    obtain st₂ : stateR s₂ = ⟨wAt D (n - m), 1024⟩ := by simp only [stateR, x4₂]
    obtain stSub : Region.Sub (stateR s₂) ⟨D, 8 * n⟩ := by
      rw [st₂]; exact Offset.sub_base _ (by omega_arith)
    obtain x0₂ : s₂.gpr .x0 = S := (g₂ _ (by decide) (by decide)).trans hx0
    obtain S₂ : Sched s₂ := by
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [x0₂]
        show InRegions (s.rd ++ s.wr) _ 8
        rw [h.rd, h.wr]; exact E.keyIn i hi
      · rw [x0₂]; exact keyData.sub_right stSub
    apply WP.seq
    apply WP.mono (batch_ok d room₂ S₂)
    intro s₃ q₃
    obtain g₃ : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s₃.gpr r = s.gpr r :=
      fun r a b c e f => (q₃.gpr r b c e f).trans (g₂ r a f)
    obtain x2₃ : s₃.gpr .x2 = BitVec.ofNat 64 m :=
      (g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x2
    apply WP.seq
    let s₄ := s₃.write .x .x10 (s₃.read .x .x2 >>> 7)
    refine WP.of_runBlock ⟨s₄, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    obtain x10₄ : s₄.gpr .x10 = BitVec.ofNat 64 (m / 128) := by
      simp only [s₄, State.write, State.read, BitVec.setWidth_eq, ite_true]
      rw [x2₃, lsr7 _ (by omega_arith)]
    obtain g₄ : ∀ r, r ≠ .x10 → s₄.gpr r = s₃.gpr r := fun r hr => by simp [s₄, State.write, hr]
    apply WP.ite _ (eval_zero s₄ .x10 x10₄ (by omega_arith))
    · intro hz; simp at hz; omega_arith
    intro _
    let s₅ := s₄.write .x .x1 (s₄.read .x .x1 + BitVec.ofNat _ 1024)
    let s₆ := s₅.write .x .x2 (s₅.read .x .x2 - BitVec.ofNat _ 128)
    refine WP.of_runBlock ⟨s₆, by
      rw [wideOut, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
    obtain r₄ : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → s₄.gpr r = s.gpr r :=
      fun r a b c e f => (g₄ r f).trans (g₃ r a b c e f)
    obtain x2₆ : s₆.gpr .x2 = BitVec.ofNat 64 (m - 128) := by
      simp only [s₆, s₅, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
        ite_true]
      rw [r₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x2,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hm]
    obtain x1₆ : s₆.gpr .x1 = wAt D (n - (m - 128)) := by
      simp only [s₆, s₅, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
        ite_true]
      rw [r₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x1, wAt,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega_arith)
    obtain g₆ : ∀ r, EcbRegs r → s₆.gpr r = s₀.gpr r := by
      intro r hr
      have ⟨a, b, c, e, f, i, j, _, _, _⟩ := hr
      simp only [s₆, s₅, State.write, b, a, ite_false]
      rw [r₄ r c e f i j, g r hr]
    have mem₆ : s₆.mem = s₃.mem := rfl
    obtain frame' : Frame [⟨D, 8 * (n - (m - 128))⟩, ⟨B, 1024⟩] s₀.mem s₆.mem := by
      obtain f₁ : Frame [⟨D, 8 * (n - (m - 128))⟩, ⟨B, 1024⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      obtain f₂ : Frame [⟨D, 8 * (n - (m - 128))⟩, ⟨B, 1024⟩] s.mem s₃.mem := q₃.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, by rw [st₂]; exact Offset.sub_base _ (by omega_arith)⟩
      rw [mem₆]; exact f₁.trans f₂
    obtain done' : ∀ b < n - (m - 128), blockAt s₆.mem (wAt D b) =
        blockOut (scheduleAt s₀.mem S) d (blockAt s₀.mem (wAt D b)) := by
      intro b hb
      rw [mem₆]
      by_cases hb' : b < n - m
      · rw [← h.done b hb']
        refine blockAt_frame q₃.frame fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        rw [st₂]
        exact Offset.disjoint D (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega_arith⟩
        obtain e := q₃.out j (by omega_arith)
        rw [x4₂, wAt_wAt, x0₂] at e
        rw [e]
        show blockOut (scheduleAt s.mem S) d (blockAt s.mem _) = _
        rw [hK, hB j (by omega_arith)]
    obtain wr₆ : s₆.wr = s₀.wr := q₃.wr.trans h.wr
    obtain rd₆ : s₆.rd = s₀.rd := q₃.rd.trans h.rd
    obtain sp₆ : s₆.sp = s₀.sp := q₃.sp.trans h.sp
    obtain flag := eval_nonzero s₆ .x2 x2₆ (by omega_arith)
    by_cases hend : m - 128 = 0
    · left
      refine ⟨by rw [flag]; simp [hend], fun b hb => done' b (by omega_arith)⟩
    · right
      refine ⟨by rw [flag]; simp [hend], m - 128, by omega_arith,
        ⟨by omega_arith, by omega_arith, by have := h.mod; omega_arith, x2₆, x1₆, g₆, rd₆, wr₆, sp₆, done', frame'⟩⟩

/-- Every block becomes its encryption or decryption. -/
theorem ecb_correct (d : Direction) {s : State} (E : Env s) :
    WP isa (ecb d) s (fun s' => ∀ b < (s.gpr .x2).toNat, blockAt s'.mem (wAt (s.gpr .x1) b) =
      blockOut (scheduleAt s.mem (s.gpr .x0)) d (blockAt s.mem (wAt (s.gpr .x1) b))) := by
  let n := (s.gpr .x2).toNat
  have hl := E.len
  obtain hx2 : s.gpr .x2 = BitVec.ofNat 64 n := by simp [n]
  rw [Impl.TripleDes.AArch64.BitsliceNeon.ecb]
  apply WP.ite _ (eval_zero s .x2 hx2 (by omega_using []))
  · intro hz
    apply WP.block_nil
    intro b hb
    simp at hz
    omega
  · intro hnz
    obtain hn0 : 0 < n := by simp at hnz; omega_using [hnz]
    refine WP.loop (M := isa) (EcbInv d s n) (fun m s' h => step_ok d E rfl m s' h) n s ?_
    exact ⟨hn0, Nat.le_refl _, rfl, hx2, by simp [wAt], fun _ _ => rfl, rfl, rfl, rfl,
      fun b hb => by omega, by rw [Nat.sub_self]; exact Frame.refl _ _⟩

end VG.Proof.TripleDes.AArch64.BitslicedNeon

end

end

/-! ### `TripleDes.AArch64.Ecb.Contract`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 384⟩
    let data : Region := ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3]

end VG.Proof.TripleDes.AArch64.Ecb

end

end


/-! # The AdvSIMD bitsliced ECB functions meet their contracts -/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.Impl.TripleDes.AArch64.BitsliceNeon VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame ecb_blocks)
open VG.Proof.TripleDes.AArch64.Ecb (contract)

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem publicRegs_four (s₁ s₂ : State) :
    VG.Proof.TripleDes.AArch64.PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
      s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
        s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [VG.Proof.TripleDes.AArch64.PublicRegs]

theorem ecb_contract (d : Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (ecb d) s (fun s' => (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩ := hs
  exact WP.mono (ecb_correct d ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit⟩) fun s' h =>
    ecb_blocks _ _ _ _ _ _ h

end VG.Proof.TripleDes.AArch64.BitslicedNeon
