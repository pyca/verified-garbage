module

public import VerifiedGarbage.Proof.X25519.Arm.Instr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the carry flag

`subs` sets the carry flag to "no borrow", which `mov` keeps and `adc`
adds: `subs t, x, y; mov t, #0; adc t, t, #0` makes `t` 1 iff `y ≤ x`
(`carry_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.X25519.Arm

theorem ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp only [exec, ho, Option.map_some])
    (k _ (Upd.subs _ _ _ _ _) (by simp [State.setReg, subFlags]))

theorem wp_movC {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → s'.c = s.c → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _) rfl)

theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0))) (by simp only [exec, ho, Option.map_some])
    (k _ (Upd.setReg _ _ _))

/-- `subs t, x, y; mov t, #0; adc t, t, #0`: `t := 1` if `y ≤ x`, else 0. -/
theorem carry_ok {t x y : Reg}
    (k : ∀ s', Rest [t] s s' → s'.mem = s.mem → s'.gpr t = (if (s.gpr y).toNat ≤ (s.gpr x).toNat then 1 else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subs t x (.reg y) :: .mov t (.imm 0) :: .adc t t (.imm 0) :: is)) s Q := by
  refine wp_subsC (op2_reg _ _) fun s1 u1 c1 => ?_
  refine wp_movC (op2_imm (by decide)) fun s2 u2 c2 => ?_
  refine wp_adc (op2_imm (by decide)) fun s3 u3 => k s3 ((u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    (u3.rest (by simp)))) (by rw [u3.mem, u2.mem, u1.mem]) ?_
  rw [u3.gpr, u2.gpr, c2, c1]
  by_cases h : (s.gpr y).toNat ≤ (s.gpr x).toNat <;> simp [h]

end

end VG.Proof.RsaKeyGen.Arm.Cand
