module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowZeroMask
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Omega

/-! Both nine-limb zero tests in the measured nonfinal-window tail. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def windowZeroCode (z : Nat) : List Instr :=
  [.movz .x .x7 0 0,.ldr .x .x1 .x0 z]++windowOrCode (z+8) 8++windowMaskCode

theorem window_zero_digit_source : outerBlock143.take 20=windowZeroCode 1648 := by decide

theorem window_zero_accumulator_source : (outerBlock143.drop 182).take 20=windowZeroCode 1216 := by decide

theorem window_zero7 (s : State) :
    WP isa (.block [.movz .x .x7 0 0]) s fun t => t.gpr .x7=0#64 ∧ Keeps [.x7] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceMul,
    Nat.reduceLT,ite_true,BitVec.shiftLeft_zero,RegUpd.gpr_write_self,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  exact ⟨rfl,⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
    rfl,rfl,rfl,rfl⟩⟩

theorem window_zero_ok {s : State} {base : Addr} {size z : Nat}
    (hs : Scr s base size) (hz : z+72≤size) (hz8 : z%8=0) :
    WP isa (.block (windowZeroCode z)) s fun t =>
      t.gpr .x3=(if wordsVal s.mem base z 9=0 then 0#64 else BitVec.allOnes 64) ∧
      Keeps [.x1,.x2,.x3,.x7,.x16] s t := by
  rw [windowZeroCode,List.append_assoc,WP.block_append_iff]
  change WP isa (.block ([.movz .x .x7 0 0]++[.ldr .x .x1 .x0 z])) s _
  rw [WP.block_append_iff]
  refine WP.mono (window_zero7 s) fun u ⟨zu,ku⟩ => ?_
  refine WP.mono (ldR_ok (hs.of_keeps ku (by decide)).ptr (d:=z) (by omega_arith) hz8 .x1)
    fun v ⟨ev,kv,_⟩ => ?_
  rw [WP.block_append_iff]
  have hv := (hs.of_keeps ku (by decide)).of_keeps kv (by decide)
  refine WP.mono (window_or_ok hv (z:=z+8) (n:=8) (by omega_arith) (by omega_arith) 8 (by decide))
    fun w ⟨ew,kw⟩ => ?_
  have zw : w.gpr .x7=0#64 := by rw [kw.gpr .x7 (by decide),kv.gpr .x7 (by decide),zu]
  refine WP.mono (window_mask_ok w zw) fun t ⟨et,kt⟩ => ?_
  have value : w.gpr .x1=0#64 ↔ wordsVal s.mem base z 9=0 := by
    rw [ew,window_or_zero,ev,kv.mem,ku.mem]
    change VG.Proof.Mont.word s.mem base z=0#64 ∧ wordsVal s.mem base (z+8) 8=0 ↔
      (VG.Proof.Mont.word s.mem base z).toNat+2^64*wordsVal s.mem base (z+8) 8=0
    have wordZero (x : BitVec 64) : x=0#64 ↔ x.toNat=0 := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact BitVec.eq_of_toNat_eq h
    rw [wordZero]
    simp only [Nat.add_eq_zero_iff,Nat.mul_eq_zero,show 2^64≠0 from by decide,false_or]
  refine ⟨?_,?_⟩
  · rw [et]
    by_cases h : w.gpr .x1=0#64
    · simp only [h,value.mp h,ite_true]
    · have hn : wordsVal s.mem base z 9≠0 := fun e => h (value.mpr e)
      simp only [h,hn,ite_false]
  · exact (ku.mono (by simp)).trans ((kv.mono (by simp)).trans ((kw.mono (by simp)).trans (kt.mono (by simp))))

end VG.Proof.Weierstrass.AArch64.P521Native
