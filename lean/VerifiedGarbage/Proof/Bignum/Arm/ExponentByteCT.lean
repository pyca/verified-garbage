module
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck

import VerifiedGarbage.Proof.Bignum.Arm.ExponentAccumulate
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
meta import VerifiedGarbage.Proof.Bignum.Arm.ExponentAccumulate
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The exponent scanner's saturation branch uses only the public prefix -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure ExponentByteInput (p : BitVec 32) (x : Nat) (s : State) : Prop where
  ptr : s.gpr .r1 = p
  low : s.gpr .r3 = BitVec.ofNat 32 (x % 2 ^ 32)
  high : s.gpr .r4 = BitVec.ofNat 32 (exponentHigh x)
  read : InRegions (s.rd ++ s.wr) (State.addr p) 1

theorem exponentByte_ct {p : BitVec 32} {x : Nat} :
    RelCT isa (fun s t => ExponentByteInput p x s ∧ ExponentByteInput p x t)
      exponentByte (fun _ _ => True) := by
  let P := ExponentByteInput p x
  let z := (((BitVec.ofNat 32 (exponentHigh x) <<< 8) +
    (BitVec.ofNat 32 (x % 2 ^ 32) >>> 24)) >>> 1) == 0
  have accum : RelCT isa (fun s t => P s ∧ P t) (.block exponentAccumulate) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block exponentAccumulate) s (fun t => t.z = z) := by
    refine WP.mono (exponentAccumulate_ok s (by rw [h.ptr]; simp) h.read) ?_
    rintro t ⟨_, _, zero, _, _⟩
    simpa only [h.low, h.high] using zero
  have branch : RelCT isa (fun s t => s.z = z ∧ t.z = z)
      (.ite .eq (.block []) (.block [.mov .r4 (.imm 2)])) (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      change some s.z = some t.z
      rw [h.1, h.2]
    · exact RelCT.block_nil (fun _ _ _ => trivial)
    · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro s t _
      exact Taint.agree_ofRegs (by simp)
  have advance : RelCT isa (fun _ _ => True) (.block exponentAdvance) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact ((pair_posts accum wp).seq branch).seq advance

end VG.Proof.Bignum.Arm
