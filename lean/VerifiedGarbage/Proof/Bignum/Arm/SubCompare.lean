module

public import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The final subtraction borrow is the exact unsigned multiword comparison -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem subCompare_ok (s : State) {base : BitVec 32} {size o a b n : Nat}
    (ctx : SubCtx s base size o a b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (count : s.gpr .lr = BitVec.ofNat 32 n) (borrow : s.gpr .r11 = 0) :
    WP isa subRow s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) b n then 1 else 0) ∧
      Outside (State.addr base) o (4 * n) s.mem t.mem ∧ Rest subLoopClobbers s t := by
  refine WP.mono (subRow_ok s ctx hn hp0 hp10 hp12 count (by rw [borrow]; decide)) ?_
  intro t inv
  have equation := inv.value
  rw [borrow] at equation
  change val32 t.mem (State.addr base) o n + val32 s.mem (State.addr base) b n + 0 =
    val32 s.mem (State.addr base) a n + 2 ^ (32 * n) * (t.gpr .r11).toNat at equation
  have diff := val32_lt t.mem (State.addr base) o n
  have bit : (t.gpr .r11).toNat = 0 ∨ (t.gpr .r11).toNat = 1 := by have := inv.borrow; omega
  refine ⟨?_, inv.outside, inv.rest⟩
  apply BitVec.eq_of_toNat_eq
  rcases bit with zero | one
  · rw [zero] at equation ⊢
    have ge : ¬ val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) b n := by omega
    rw [ite_eq_right ge]; rfl
  · rw [one] at equation ⊢
    have lt : val32 s.mem (State.addr base) a n < val32 s.mem (State.addr base) b n := by omega
    rw [ite_eq_left lt]; rfl

end VG.Proof.Bignum.Arm
