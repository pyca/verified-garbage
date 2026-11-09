module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishYWords
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishZMask
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-! Canonical homogeneous infinity without assuming the accumulator is finite. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.Weierstrass.AArch64.P521Native

def finishFixYCode : List Instr := finishZMaskCode 1216++finishYWords 9 1144 true

theorem finish_fix_y_source : (outerBlock152.drop 107).take 102=finishFixYCode := by lit_decide

private theorem words_same {base : Addr} {m m' : Mem} : ∀n o,
    (∀j<n,word m' base (o+8*j)=word m base (o+8*j)) → wordsVal m' base o n=wordsVal m base o n
  | 0,_,_ => rfl
  | n+1,o,h => by
    rw [wordsVal,wordsVal,show word m' base o=word m base o from by simpa only [Nat.mul_zero,Nat.add_zero] using h 0 (by omega_arith)]
    have tail := words_same (base:=base) (m:=m) (m':=m') n (o+8) (fun j hj => by
      rw [show o+8+8*j=o+8*(j+1) by omega_arith]
      exact h (j+1) (by omega_arith))
    rw [tail]

theorem finish_fix_y_ok {base : Addr} {s : State} (hs : Scr s base 8192) :
    WP isa (.block finishFixYCode) s fun t =>
      wordsVal t.mem base 1144 9=(if wordsVal s.mem base 1216 9=0 then 1 else wordsVal s.mem base 1144 9) ∧
      KeepRegs [.x1,.x2,.x4,.x5,.x7,.x9,.x16] s t ∧ Outside base 1144 72 s.mem t.mem := by
  rw [finishFixYCode,WP.block_append_iff]
  refine WP.mono (finish_z_mask_ok hs (z:=1216) (by decide) (by decide)) fun u ⟨mask,ku⟩ => ?_
  have hu := hs.of_keeps ku (by decide)
  let chooseOne := decide (wordsVal s.mem base 1216 9=0)
  have mu : u.gpr .x2=(if chooseOne then BitVec.allOnes 64 else 0#64) := by
    rw [mask]
    simp only [chooseOne,decide_eq_true_eq]
  refine WP.mono (finish_y_words_ok chooseOne 9 true hu (by decide) (by decide) mu)
    fun t ⟨values,kt,ot⟩ => ?_
  refine ⟨?_,((VG.Proof.Mont.AArch64.Keeps.regs ku).mono (by decide)).trans (kt.mono (by decide)),?_⟩
  · by_cases hz : wordsVal s.mem base 1216 9=0
    · simp only [hz,ite_true]
      have oneBound := Nat.one_lt_two_pow (n:=64*9) (by decide)
      have fromWords := wordsVal_of_shifts t.mem base 1144 9 1 oneBound
      apply fromWords
      intro j hj
      rw [values j hj]
      simp only [chooseOne,hz,decide_true,ite_true,Bool.true_and]
      by_cases h0 : j=0
      · subst j; rfl
      · have zeroShift := Nat.shiftRight_eq_zero 1 (64*j) (Nat.one_lt_two_pow (by omega_arith))
        simp only [h0,decide_false,zeroShift]
        rfl
    · simp only [hz,ite_false]
      apply words_same 9 1144
      intro j hj
      rw [values j hj,ku.mem]
      simp only [chooseOne,hz,decide_false,Bool.false_eq_true,ite_false]
  · rw [ku.mem] at ot
    exact ot

end VG.Proof.Weierstrass.AArch64.P521Native
