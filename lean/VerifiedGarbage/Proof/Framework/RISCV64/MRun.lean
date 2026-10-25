module

public import VerifiedGarbage.Proof.Framework.Block
public meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Exec -- shake: keep (`mrun` expands to its lemmas)
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# Running short RISC-V blocks that access memory a word at a time

Untrusted: everything here is checked by Lean. `mrun [h, …]` runs a short
block as `crun` (`Run.lean`) does, but keeps the memory read by a load as
`Mem.readW` (a word or doubleword) or as the byte, and written by a store as
`Mem.writeW` (a word or doubleword) or `Mem.write` of a byte, rather than
unfolding `Mem.read`, whose recursion on the width is deep for a
doubleword. `li` and `addi` of a numeral (`exec_li_nat`, `exec_addi_nat`,
`exec_addi_neg_nat`) need only its bound.
-/

@[expose] public section

namespace VG.RISCV64

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp

theorem read_four (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem read_eight (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_four (m : Mem) (a : Addr) (v : BitVec 32) : m.write a 4 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem write_eight (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

/-- `li` of a numeral below 2048. -/
theorem exec_li_nat {s : State} {d : Reg} {n : Nat} (h : n < 2048) :
    exec (.li d (n : Int)) s = some (s.write d (BitVec.ofNat 64 n)) := by
  rw [exec_li (by unfold imm12; omega), BitVec.ofInt_natCast]

/-- `addi` of a numeral below 2048. -/
theorem exec_addi_nat {s : State} {d n : Reg} {m : Nat} (h : m < 2048) :
    exec (.addi d n (m : Int)) s = some (s.write d (s.gpr n + BitVec.ofNat 64 m)) := by
  rw [exec_addi (by unfold imm12; omega), BitVec.ofInt_natCast]

/-- `addi` of a negated numeral up to 2048. -/
theorem exec_addi_neg_nat {s : State} {d n : Reg} {m : Nat} (h : m ≤ 2048) :
    exec (.addi d n (-(m : Int))) s = some (s.write d (s.gpr n - BitVec.ofNat 64 m)) := by
  rw [exec_addi (by unfold imm12; omega), BitVec.ofInt_neg, BitVec.ofInt_natCast,
    ← BitVec.sub_eq_add_neg]

end VG.RISCV64

public meta section

namespace VG.RISCV64

syntax "mrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| mrun) => `(tactic| mrun [])
  | `(tactic| mrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil, ↓exec_li_nat, ↓exec_addi_nat,
        ↓exec_addi_neg_nat, exec, State.write, addr, State.load, State.store, Width.bytes, imm12,
        BitVec.setWidth_eq, BitVec.add_zero, read_one, read_four, read_eight, write_four,
        write_eight, Option.bind_some, Option.map_some, List.cons_append, List.nil_append,
        false_implies, Option.some.injEq, exists_eq_left', ite_true, ite_false, reduceCtorEq, ne_eq,
        not_false_eq_true, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reduceAdd, Nat.reducePow,
        Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceDiv, Nat.mod_one, implies_true,
        true_implies, ↓reduceIte, and_self, true_and, and_true, Int.reduceLE, Int.reduceLT,
        Int.reduceNeg, BitVec.ofInt_neg, BitVec.ofInt_ofNat, ← BitVec.sub_eq_add_neg, $ls,*]))

end VG.RISCV64
