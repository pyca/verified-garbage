module

public import VerifiedGarbage.Proof.Framework.Bitslice.Vars
public import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced

/-!
# The machine state of the bitsliced ECB code on PPC64LE

The code keeps its 64 state words in the scratch buffer at `r10` (`sl s j`,
the word at `r10 + 8j`; `words`). `Room` says that the buffer is writable.
Blocks that only move and XOR words between registers and the state words
are checked by evaluation over the variable domain (`Bitslice.vars`):
`varsRun` runs one, its variables being the state words (variable `k < 64`)
and some registers (variable `64 + i`). As on RISC-V
(`Proof/TripleDes/RISCV64/Bitsliced/Machine.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

open VG VG.PPC64LE VG.PPC64LE.Straight VG.Bitslice VG.Impl.TripleDes.PPC64LE.Bitslice

/-- The word at slot `j` of the scratch buffer. -/
def sl (s : State) (j : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .r10) j) 64

/-- The 64 state words. -/
def words (s : State) : Nat → BitVec 64 := sl s

/-- The scratch buffer. -/
def frameR (s : State) : Region := ⟨s.gpr .r10, 1024⟩

/-- The scratch buffer is writable. -/
structure Room (s : State) : Prop where
  frame : frameR s ∈ s.wr

theorem Room.congr {s s' : State} (h : Room s) (hb : s'.gpr .r10 = s.gpr .r10) (hw : s'.wr = s.wr) :
    Room s' where
  frame := by simp only [frameR, hb, hw]; exact h.frame

/-- A word of the buffer, at slot `k < 128`. -/
theorem slot_in {s : State} (h : Room s) {k : Nat} (hk : k < 128) :
    InRegions s.wr (wordAddr (s.gpr .r10) k) 8 :=
  ⟨frameR s, h.frame, slot_contains (s.gpr .r10) (n := 128) hk (by decide)⟩

/-! ## Blocks over the variable domain -/

/-- The state words, `[r10 + 8k]`, `k < 64`. -/
def varsCfg : Cfg := { base := .r10, slots := 64, ext := .r10, exts := 0 }

theorem Room.ok {s : State} (h : Room s) : Ok varsCfg s where
  slotIn k hk := slot_in h (by simp only [varsCfg] at hk; omega)
  extIn k hk := by simp [varsCfg] at hk
  slots := by decide
  sep k _ j hj := by simp [varsCfg] at hj

/-- State word `k` is variable `k`; register `regs[i]` is variable `64 + i`. -/
def varEnv (regs : List Reg) : Env Nat :=
  { reg := fun r => (regs.idxOf? r).map fun i => 2 ^ (64 + i),
    slot := fun k => if k < 64 then some (2 ^ k) else none }

/-- The values of the variables. -/
def varVals (s : State) (regs : List Reg) (v : Nat) : BitVec 64 :=
  if v < 64 then sl s v else s.gpr (regs.getD (v - 64) .r0)

def varN (regs : List Reg) : Nat := 64 + regs.length

theorem varEnv_rel {s : State} (regs : List Reg) :
    Rel (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) (varEnv regs) s where
  reg r a h := by
    simp only [varEnv, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp hi
    simp only [VarRel, varN]
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

/-- Run a block that the variable domain accepts. -/
theorem varsRun {is : List Instr} (regs : List Reg) {post : Env Nat → Bool}
    (hchk : check (vars 64) varsCfg (fun _ => none) is (varEnv regs) post = true)
    {s : State} (h : Room s) :
    ∃ e' s', post e' = true ∧ runBlock isa is s = some s' ∧
      Post (VarRel (varVals s regs) (varN regs)) varsCfg (fun _ => none) e' s s'
        (fun r => (is.all fun i => dst i != some r) = false) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨s', hs', p⟩ := run (vars_sound _ _) h.ok (varEnv_rel regs) he
  exact ⟨e', s', hpost, hs', p⟩

theorem varRel_slot {V : Nat → BitVec 64} {N : Nat} {e : Env Nat} {s : State}
    (hrel : Rel (VarRel V N) varsCfg (fun _ => none) e s) {k a : Nat} (hk : k < 64)
    (ha : e.slot k = some a) : sl s k = xorSet V a N :=
  hrel.slot k a hk ha

theorem xorSet_two_pow_xor {V : Nat → BitVec 64} {a b N : Nat} (ha : a < N) (hb : b < N) :
    xorSet V (2 ^ a ^^^ 2 ^ b) N = V a ^^^ V b := by
  rw [xorSet_xor, xorSet_two_pow _ ha, xorSet_two_pow _ hb]

/-- The state words' region. -/
def stR (s : State) : Region := ⟨s.gpr .r10, 512⟩

end VG.Proof.TripleDes.PPC64LE.Bitsliced
