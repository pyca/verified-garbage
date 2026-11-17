module

public import VerifiedGarbage.Impl.Bignum.Arm.Minv64
import VerifiedGarbage.Proof.Bignum.Arm.Newton64Math
import VerifiedGarbage.Proof.Bignum.Arm.Newton64Steps
import VerifiedGarbage.Proof.Bignum.Arm.Sub64
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.Arm.Newton64
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.Mul64

/-! ### `Bignum.Arm.Newton64`, which this module and modules that import it used -/

section

/-! # A complete machine-level Newton step on 64-bit values -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

abbrev newtonClobbers : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem newton64_ok (s : State) (a b : Addr)
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = b)
    (ra : InRegions (s.rd ++ s.wr) a 4) (rb : InRegions (s.rd ++ s.wr) b 4) :
    WP isa (.block newton64) s fun t =>
      (t.gpr .r10 ++ t.gpr .r1) = (s.gpr .r10 ++ s.gpr .r1) *
        ((2 : BitVec 64) - (s.mem.readW b 32 ++ s.mem.readW a 32) * (s.gpr .r10 ++ s.gpr .r1)) ∧
      t.mem = s.mem ∧ Rest newtonClobbers s t := by
  simp only [newton64, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (newton64Load_ok s a b pa pb ra rb) ?_
  rintro s1 ⟨m1, mem1, r1⟩
  rw [WP.block_append_iff]
  refine WP.mono (mul64_ok s1) ?_
  rintro s2 ⟨v2, mem2, r2⟩
  rw [WP.block_append_iff]
  refine WP.mono (newton64Subtract_ok s2) ?_
  rintro s3 ⟨v3, mem3, r3⟩
  rw [WP.block_append_iff]
  refine WP.mono (mul64_ok s3) ?_
  rintro s4 ⟨v4, mem4, r4⟩
  refine WP.mono (newton64Finish_ok s4) ?_
  rintro t ⟨value, mem5, r5⟩
  refine ⟨?_, mem5.trans (mem4.trans (mem3.trans (mem2.trans mem1))), ?_⟩
  · rw [value, v4, v3, v2, m1,
      r3.gpr .r10 (by decide), r3.gpr .r1 (by decide),
      r2.gpr .r10 (by decide), r2.gpr .r1 (by decide),
      r1.gpr .r10 (by decide), r1.gpr .r1 (by decide),
      BitVec.mul_comm (s.mem.readW b 32 ++ s.mem.readW a 32)]
  · exact (r1.mono (by decide)).trans
      ((r2.mono (by decide)).trans
        ((r3.mono (by decide)).trans
          ((r4.mono (by decide)).trans (r5.mono (by decide)))))

end VG.Proof.Bignum.Arm

end

end

/-! # The initial approximation, lifting step, and final negation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg op2_imm)

theorem minv64Start_ok (s : State) (a b : Addr)
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = b)
    (ra : InRegions (s.rd ++ s.wr) a 4) (rb : InRegions (s.rd ++ s.wr) b 4) :
    WP isa (.block minv64Start) s fun t =>
      (t.gpr .r10 ++ t.gpr .r1) = (s.mem.readW b 32 ++ s.mem.readW a 32) ∧
      t.mem = s.mem ∧ Rest newtonClobbers s t := by
  rw [minv64Start, WP.block_append_iff]
  refine WP.mono (newton64Load_ok s a b pa pb ra rb) ?_
  rintro u ⟨val, mem, rest⟩
  refine wp_mov (op2_reg _ _) fun v h => ?_
  refine wp_mov (op2_reg _ _) fun t j => WP.block_nil ?_
  refine ⟨?_, j.mem.trans (h.mem.trans mem), ?_⟩
  · rw [j.gpr, j.other .r1 (by decide), h.gpr, h.other .r11 (by decide), val]
  · exact (rest.mono (by decide)).trans
      ((h.rest (by decide)).trans (j.rest (by decide)))

theorem minv64End_ok (s : State) :
    WP isa (.block minv64End) s fun t =>
      (t.gpr .r11 ++ t.gpr .r2) = (0 : BitVec 64) - (s.gpr .r10 ++ s.gpr .r1) ∧
      t.mem = s.mem ∧ Rest newtonClobbers s t := by
  rw [minv64End, WP.block_append_iff]
  refine wp_mov (op2_reg _ _) fun s1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => WP.block_nil ?_
  refine WP.mono (sub64_ok s3) ?_
  rintro t ⟨val, mem, rest⟩
  refine ⟨?_, mem.trans (u3.mem.trans (u2.mem.trans u1.mem)), ?_⟩
  · rw [val, u3.gpr, u3.other .r4 (by decide), u3.other .r3 (by decide),
      u2.gpr, u2.other .r3 (by decide), u1.gpr, u1.other .r10 (by decide)]
    rfl
  · exact (u1.rest (by decide)).trans
      ((u2.rest (by decide)).trans
        ((u3.rest (by decide)).trans (rest.mono (by decide))))

/-- The machine iteration doubles the number of correct inverse bits. -/
theorem newton64_step_ok (s : State) (a b : Addr) {j : Nat}
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = b)
    (ra : InRegions (s.rd ++ s.wr) a 4) (rb : InRegions (s.rd ++ s.wr) b 4)
    (hj : 2 * j ≤ 64)
    (h : (((s.mem.readW b 32 ++ s.mem.readW a 32).toNat : Int) *
      (s.gpr .r10 ++ s.gpr .r1).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton64) s fun t =>
      (((s.mem.readW b 32 ++ s.mem.readW a 32).toNat : Int) *
        (t.gpr .r10 ++ t.gpr .r1).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
      t.mem = s.mem ∧ Rest newtonClobbers s t := by
  refine WP.mono (newton64_ok s a b pa pb ra rb) ?_
  rintro t ⟨val, mem, rest⟩
  refine ⟨?_, mem, rest⟩
  apply VG.Proof.Bignum.newton_step hj h
  rw [val]
  exact newton64_val _ _

end VG.Proof.Bignum.Arm
