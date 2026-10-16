module

public import VerifiedGarbage.Impl.Bignum.Arm.Csub
public import VerifiedGarbage.Proof.Bignum.Arm.Sub
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Include the high accumulator word in the reduction decision -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_reg)

theorem reduceChoice_ok (s : State) (a : Addr)
    (ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 0) = a)
    (ra : InRegions (s.rd ++ s.wr) a 4) :
    WP isa reduceChoice s fun t =>
      t.gpr .r11 = (if (s.gpr .r11).toNat ≤ (s.mem.readW a 32).toNat then 0 else 1) ∧
      (t.gpr .r11).toNat ≤ 1 ∧ t.mem = s.mem ∧ Rest [.r1, .r2, .r3, .r11] s t := by
  rw [reduceChoice, WP.seq_iff]
  refine wp_ldr (a := a) (by decide) ha ra fun s1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => WP.block_nil ?_
  refine WP.mono (subWord_ok s2 .r3 .r11 .r1 .r2 (by decide)) ?_
  rintro t ⟨_, value, keep⟩
  have aa : s2.gpr .r1 = s.mem.readW a 32 := (u2.other .r1 (by decide)).trans u1.gpr
  have cc : s2.gpr .r2 = s.gpr .r11 := by rw [u2.gpr, u1.other .r11 (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [value, aa, cc]
  · rw [value]; split <;> decide
  · rw [keep.mem, u2.mem, u1.mem]
  · have k3 : Rest [.r3, .r11] s2 t := ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩
    exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (k3.mono (by simp_all)))

end VG.Proof.Bignum.Arm
