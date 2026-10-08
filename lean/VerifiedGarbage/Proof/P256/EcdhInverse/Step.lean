import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.P256.EcdhInverse.Shift

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- Update before halving the second packed row. The incoming zero flag is its parity. -/
def updateStep : List Instr :=
  [.cselc .x .x6 .x4 .x27 .ne,.ccmp .x .x1 0 8 .ne,
   .csneg .x .x1 .x1 .x1 .lt,.csneg .x .x6 .x6 .x6 .lt,
   .cselc .x .x4 .x5 .x4 .ge,.add .x .x5 .x5 .x6,.addImm .x .x1 .x1 2]

def halfStep : List Instr :=
  [.lsr .x .x26 .x5 63,.sub .x .x26 .x27 .x26,.extr .x .x5 .x26 .x5 1]

def roundStep : List Instr := updateStep ++ [.movz .x .x28 2 0,.tst .x .x5 .x28] ++ halfStep

theorem updateStep_run (s : State) (h27 : s.gpr .x27=0) {odd neg : Bool}
    (hz : s.zf = !odd) (hn : (s.gpr .x1).msb=neg) :
    WP isa (.block updateStep) s fun t =>
      t.gpr .x1=(if odd && !neg then -s.gpr .x1+2 else s.gpr .x1+2) ∧
      t.gpr .x4=(if odd && !neg then s.gpr .x5 else s.gpr .x4) ∧
      t.gpr .x5=s.gpr .x5+(if odd then (if neg then s.gpr .x4 else -s.gpr .x4) else 0) ∧
      Keeps [.x1,.x4,.x5,.x6] s t := by
  apply WP.of_runBlock
  have hadd (x : BitVec 64) : x + 18446744073709551615#64 + 1#64 = x := by
    rw [BitVec.add_assoc,show 18446744073709551615#64 + 1#64 = 0 by decide]
    exact BitVec.add_zero x
  have hflag : (s.gpr .x1 + BitVec.allOnes Size.x.bits + 1#Size.x.bits).msb = neg := by
    change (s.gpr .x1 + 18446744073709551615#64 + 1#64).msb=neg
    rw [hadd]
    exact hn
  cases odd <;> cases neg <;>
  · simp only [updateStep,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
      RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,exists_eq_left',and_self,
      h27,hz,CondCode.holds,State.flagsAdd,toInt_not0,int_m1p1,
      RegUpd.nf_write,RegUpd.zf_write,RegUpd.vf_write,Bool.not_true,Bool.not_false,
      Bool.bne_false,Bool.and_true,Bool.and_false,
      Bool.toNat_true,Int.natCast_one,show (2:Nat)<4096 by decide,
      show (0:Nat)<32 ∧ (8:Nat)<16 by decide,
      show Nat.testBit 8 3=true by decide,show Nat.testBit 8 0=false by decide,
      Bool.false_eq_true]
    refine ⟨?_,?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
    · simp [hflag]
    · simp [hflag]
    · simp [hflag]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      obtain ⟨h1,h4,h5,h6⟩ := hr
      simp only [RegUpd.gpr_write,h1,h4,h5,h6,↓reduceIte]


theorem halfStep_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block halfStep) s fun t =>
      t.gpr .x5=(s.gpr .x5).sshiftRight 1 ∧ t.zf=s.zf ∧
      Keeps [.x5,.x26] s t := by
  apply WP.of_runBlock
  simp only [halfStep,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,show 63<Size.x.bits by decide,show 1<Size.x.bits by decide]
  refine ⟨?_,rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [show (0 : BitVec 64)-(s.gpr .x5 >>> 63)= -(s.gpr .x5 >>> 63) by ring]
    exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h5,h26⟩ := hr
    simp only [RegUpd.gpr_write,h5,h26,↓reduceIte]


def testHalf : List Instr := [.movz .x .x28 2 0,.tst .x .x5 .x28] ++ halfStep

theorem testHalf_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block testHalf) s fun t =>
      t.gpr .x5=(s.gpr .x5).sshiftRight 1 ∧
      t.zf=decide (t.gpr .x5 &&& 1 = 0) ∧ Keeps [.x5,.x26,.x28] s t := by
  apply WP.of_runBlock
  simp only [testHalf,halfStep,List.cons_append,List.nil_append,
    runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,show (16*0:Nat)<Size.x.bits by decide,
    Nat.mul_zero,BitVec.shiftLeft_zero,
    RegUpd.zf_write,show 63<Size.x.bits by decide,show 1<Size.x.bits by decide]
  have he : ((s.gpr .x27-(s.gpr .x5 >>> 63)) ++ s.gpr .x5).extractLsb' 1 64 =
      (s.gpr .x5).sshiftRight 1 := by
    rw [h27,show (0 : BitVec 64)-(s.gpr .x5 >>> 63)= -(s.gpr .x5 >>> 63) by ring]
    exact signed_extract _ (by decide)
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · simpa only [h27] using he
  · rw [show (((0 : BitVec 64)-(s.gpr .x5 >>> 63)) ++ s.gpr .x5).extractLsb' 1 64 =
      (s.gpr .x5).sshiftRight 1 by simpa only [h27] using he]
    simp only [half_parity]
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h5,h26,h28⟩ := hr
    simp only [RegUpd.gpr_write,h5,h26,h28,↓reduceIte]

end VG.Proof.P256.EcdhInverse
