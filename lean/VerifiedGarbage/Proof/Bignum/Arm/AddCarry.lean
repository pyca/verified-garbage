module

public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-! # Additions with a carry kept in a register, one instruction at a time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Upd)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_adds {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → s'.c = decide (2 ^ 32 ≤ (s.gpr n).toNat + y.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.adds d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := (addFlags s (s.gpr n) y).setReg d (s.gpr n + y))
    (by simp only [reduceExec, ho, Option.map_some])
    (k _ ⟨by simp only [State.setReg, ↓reduceIte],
      fun r h => by simp only [State.setReg, addFlags, h, ↓reduceIte], rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → s'.c = s.c →
      WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0)))
    (by simp only [reduceExec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _) rfl)

/-- `mov` keeps the flags. -/
theorem wp_mov_c {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → s'.c = s.c → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d v) (by simp only [reduceExec, ho, Option.map_some])
    (k _ (Upd.setReg _ _ _) rfl)

end

/-- A sum's low word and its carry. -/
theorem add_carry (x y : BitVec 32) :
    (x + y).toNat + 2 ^ 32 * (if 2 ^ 32 ≤ x.toNat + y.toNat then 1 else 0) = x.toNat + y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_add]
  split <;> omega

/-- `adc` of zero and the carry into a small register. -/
theorem adc_zero (r : BitVec 32) (c : Bool) (hr : r.toNat < 2 ^ 31) :
    (r + 0 + (if c then 1 else 0) : BitVec 32).toNat = r.toNat + (if c then 1 else 0) := by
  have z : (0 : BitVec 32).toNat = 0 := rfl
  have o : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_add]
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, z, o] <;> omega

end VG.Proof.Bignum.Arm
