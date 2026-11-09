module

public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The machine state of the bitsliced ECB code on RISC-V

The code keeps its 64 state words in the frame at `s0` (`sl s j`, the word
at `s0 + 8j`; `words`). `Room` says that the frame is writable, aligned and
does not wrap around. Blocks that only move and XOR words between registers
and the state words are checked by evaluation over the variable domain
(`Bitslice.vars`): `varsRun` runs one, its variables being the state words
(variable `k < 64`) and some registers (variable `64 + i`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64.Bitslice

/-- The word at slot `j` of the frame. -/
def sl (s : State) (j : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .s0) j) 64

/-- The 64 state words. -/
def words (s : State) : Nat → BitVec 64 := sl s

/-- The frame. -/
def frameR (s : State) : Region := ⟨s.gpr .s0, frameBytes⟩

/-- The frame is writable and 8-byte aligned, and does not wrap around. -/
structure Room (s : State) : Prop where
  frame : frameR s ∈ s.wr
  al : (s.gpr .s0).toNat % 8 = 0
  fit : (s.gpr .s0).toNat + frameBytes ≤ 2 ^ 64

theorem Room.congr {s s' : State} (h : Room s) (hb : s'.gpr .s0 = s.gpr .s0) (hw : s'.wr = s.wr) :
    Room s' where
  frame := by simp only [frameR, hb, hw]; exact h.frame
  al := by rw [hb]; exact h.al
  fit := by rw [hb]; exact h.fit

/-- A word of the frame, at slot `k < 132`. -/
theorem slot_in {s : State} (h : Room s) {k : Nat} (hk : k < 132) :
    InRegions s.wr (wordAddr (s.gpr .s0) k) 8 := by
  refine ⟨frameR s, h.frame, ?_⟩
  have := slot_contains (s.gpr .s0) (n := 132) hk (by decide)
  exact this

/-! ## Blocks over the variable domain -/

/-- The state words, `[s0 + 8k]`, `k < 64`. -/
def varsCfg : Cfg := { base := .s0, slots := 64, ext := .s0, exts := 0 }

theorem Room.ok {s : State} (h : Room s) : Ok varsCfg s where
  slotIn k hk := slot_in h (by simp only [varsCfg] at hk; omega)
  extIn k hk := by simp [varsCfg] at hk
  baseAl _ := h.al
  extAl h0 := by simp [varsCfg] at h0
  slots := by decide
  sep k _ j hj := by simp [varsCfg] at hj

/-- State word `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List Reg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => .v (2 ^ (64 + i)),
    slot := fun k => if k < 64 then some (2 ^ k) else none }

/-- The values of the variables. -/
def varVals (s : State) (regs : List Reg) (v : Nat) : BitVec 64 :=
  if v < 64 then sl s v else s.gpr (regs.getD (v - 64) .ra)

def varN (regs : List Reg) : Nat := 64 + regs.length

theorem varEnv_rel {s : State} (regs : List Reg) :
    Rel (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) (varEnv regs) s where
  reg r a h := by
    simp only [varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [ValRel, VarRel, varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [varVals, show ¬ 64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, heq]
  slot k a hk h := by
    have hk' : k < 64 := hk
    simp only [varEnv, hk', ite_true, Option.some.injEq] at h
    subst h
    simp only [VarRel, varN]
    rw [xorSet_two_pow _ (by omega)]
    simp only [varVals, hk', ite_true, sl, varsCfg]
  ext _ _ hk := by simp [varsCfg] at hk

theorem varRel_fun {V : Nat → BitVec 64} {N : Nat} (a : Nat) (x y : BitVec 64) (hx : VarRel V N a x)
    (hy : VarRel V N a y) : x = y := by
  simp only [VarRel] at hx hy
  rw [hx, hy]

/-- Run a block that the variable domain accepts. -/
theorem varsRun {is : List Instr} (regs : List Reg) {post : Env Nat → Bool}
    (hchk : check (vars 64) varsCfg (fun _ => none) is (varEnv regs) post = true)
    {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) e' s s'
        (fun r => (is.all fun i => dst i != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨s', hs', p⟩ := run (vars_sound _ _) varRel_fun h.ok (varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem varRel_slot {V : Nat → BitVec 64} {N : Nat} {e : Env Nat} {s : State}
    (hrel : Rel (VarRel V N) varsCfg (fun _ => none) e s) {k a : Nat} (hk : k < 64)
    (ha : e.slot k = some a) : sl s k = xorSet V a N :=
  hrel.slot k a hk ha

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

/-- The state words' region. -/
def stR (s : State) : Region := ⟨s.gpr .s0, 512⟩

end VG.Proof.TripleDes.RISCV64.Bitsliced
