module
public import VerifiedGarbage.Impl.Bignum.Arm.Newton64
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.Newton64Steps
import VerifiedGarbage.Proof.Bignum.Arm.Mul64
import VerifiedGarbage.Proof.Framework.Block

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
      r3.gpr .r10 (by simp), r3.gpr .r1 (by simp),
      r2.gpr .r10 (by simp [clobbers]), r2.gpr .r1 (by simp [clobbers]),
      r1.gpr .r10 (by simp), r1.gpr .r1 (by simp),
      BitVec.mul_comm (s.mem.readW b 32 ++ s.mem.readW a 32)]
  · exact (r1.mono (by simp [newtonClobbers])).trans
      ((r2.mono (by simp [newtonClobbers, clobbers])).trans
        ((r3.mono (by simp [newtonClobbers])).trans
          ((r4.mono (by simp [newtonClobbers, clobbers])).trans (r5.mono (by simp [newtonClobbers])))))

end VG.Proof.Bignum.Arm
