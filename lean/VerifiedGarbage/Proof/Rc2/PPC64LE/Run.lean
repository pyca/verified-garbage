module

import VerifiedGarbage.Impl.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# RC2 on PPC64LE: running blocks

`rrun [facts]` runs a block of the RC2 code symbolically (`crun`), keeping
32- and 64-bit loads and stores as `Mem.readW` and `Mem.writeW` and byte
loads as the byte, as IDEA's `irun` (`Proof/Idea/PPC64LE/Round.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp

theorem read_four (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem read_eight (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_eight (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem write_one (m : Mem) (a : Addr) (v : BitVec 8) : m.write a 1 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

/-- Steps a block of the RC2 code. -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic|
      crun [List.cons_append, List.nil_append, ↓read_one, ↓read_four, ↓read_eight, write_eight, write_one,
        false_implies, $ls,*])

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0#64) := by
  simp only [eval, State.read, BitVec.setWidth_eq]; rfl

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0#64) := by
  simp only [eval, State.read, BitVec.setWidth_eq]; rfl

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0#64) = !decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega
    simp [this, h]

theorem ofNat_beq_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a == 0#64) = decide (a = 0) := by
  have := ofNat_bne_zero ha
  cases h : (BitVec.ofNat 64 a == 0#64) <;> cases e : decide (a = 0) <;> simp_all [bne]

/-- A loop counting to `stop`, exiting when `r` is zero. -/
theorem countLoop (body : Prog isa) (r : Reg) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ (s'.gpr r != 0#64) = !decide (i + 1 = stop)))
    (i : Nat) (hi : i < stop) (s : State) (hs : I i s) :
    WP isa (.loop body (.nonzero .d r)) s (I stop) := by
  refine WP.loop (M := isa) (fun n s => ∃ i, i < stop ∧ stop - i = n ∧ I i s) ?_ (stop - i) s ⟨i, hi, rfl, hs⟩
  intro n s ⟨j, hj, hn, hI⟩
  refine WP.mono (step j hj s hI) fun s' ⟨h', hc⟩ => ?_
  by_cases he : j + 1 = stop
  · left
    rw [eval_nonzero, hc, he]
    exact ⟨by simp, he ▸ h'⟩
  · right
    rw [eval_nonzero, hc]
    exact ⟨by simp [he], stop - (j + 1), by omega, j + 1, by omega, rfl, h'⟩

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem sub_bne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y != 0#64) = !decide (x = y) := by
  rw [bne, ← Offset.ofNat_sub_ofNat_beq hx hy]; rfl

end VG.Proof.Rc2.PPC64LE
