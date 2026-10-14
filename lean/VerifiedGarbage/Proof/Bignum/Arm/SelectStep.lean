module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A selection step writes exactly the chosen input word -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

abbrev selectClobbers : List Reg := [.r1, .r2, .r3, .r4]

theorem selectStep_ok (s : State) (o a b : Addr)
    (ho : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = o)
    (ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 0) = a)
    (hb : State.addr (s.gpr .r12 + BitVec.ofNat 32 0) = b)
    (wo : InRegions s.wr o 4) (ra : InRegions (s.rd ++ s.wr) a 4)
    (rb : InRegions (s.rd ++ s.wr) b 4) (hc : (s.gpr .r11).toNat ≤ 1) :
    WP isa selectStep s fun t =>
      t.mem = s.mem.writeW o (if (s.gpr .r11).toNat = 0 then s.mem.readW a 32 else s.mem.readW b 32) ∧
      Rest selectClobbers s t := by
  rw [selectStep, WP.seq_iff]
  refine wp_ldr (a := a) (by decide) ha ra fun s1 u1 => ?_
  refine wp_ldr (a := b) (by decide) (by rw [u1.other .r12 (by decide)]; exact hb)
    (by rw [u1.rd, u1.wr]; exact rb) fun s2 u2 => WP.block_nil ?_
  have aa : s2.gpr .r1 = s.mem.readW a 32 := (u2.other .r1 (by decide)).trans u1.gpr
  have bb : s2.gpr .r2 = s.mem.readW b 32 := by rw [u2.gpr, u1.mem]
  have cc : s2.gpr .r11 = s.gpr .r11 :=
    (u2.other .r11 (by decide)).trans (u1.other .r11 (by decide))
  rw [WP.seq_iff]
  refine WP.mono (selectWord_ok s2 (by rw [cc]; exact hc)) ?_
  rintro s3 ⟨value, keep⟩
  have ptr : s3.gpr .r0 = s.gpr .r0 := (keep.regs .r0 (by simp)).trans
    ((u2.other .r0 (by decide)).trans (u1.other .r0 (by decide)))
  refine wp_str (a := o) (by decide) (by rw [ptr]; exact ho)
    (by rw [keep.wr, u2.wr, u1.wr]; exact wo) fun t ut => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · rw [ut.mem, keep.mem, u2.mem, u1.mem, value, aa, bb, cc]
  · have k3 : Rest [.r3, .r4] s2 s3 := ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩
    exact (u1.rest (by simp [selectClobbers])).trans ((u2.rest (by simp [selectClobbers])).trans
      ((k3.mono (by simp [selectClobbers])).trans (ut.rest _)))

end VG.Proof.Bignum.Arm
