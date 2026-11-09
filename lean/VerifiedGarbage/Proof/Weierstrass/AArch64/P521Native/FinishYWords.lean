module

-- separate module: the word-array induction is independent of the scalar mux and the final zero-test composition

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishYWord
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete branchless ordinate correction, with each word and frame. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def finishYWords : Nat → Nat → Bool → List Instr
  | 0,_,_ => []
  | n+1,o,first => finishYWord o first++finishYWords n (o+8) false

theorem finish_y_words_ok (chooseOne : Bool) : ∀n {s : State} {base : Addr} {W o : Nat} (first : Bool),
    Scr s base W → o+8*n≤W → o%8=0 →
    s.gpr .x2=(if chooseOne then BitVec.allOnes 64 else 0#64) →
    WP isa (.block (finishYWords n o first)) s fun t =>
      (∀j<n,word t.mem base (o+8*j)=
        if chooseOne then (if first && decide (j=0) then 1#64 else 0#64) else word s.mem base (o+8*j)) ∧
      KeepRegs [.x9,.x4] s t ∧ Outside base o (8*n) s.mem t.mem
  | 0,s,base,W,o,first,_,_,_,_ => WP.block_nil
    ⟨fun _ h => False.elim (Nat.not_lt_zero _ h),⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1,s,base,W,o,first,hs,ho,ho8,mask => by
    rw [finishYWords,WP.block_append_iff]
    refine WP.mono (finish_y_word_ok hs (by omega_arith) ho8 first chooseOne mask) fun u ⟨eu,ku⟩ => ?_
    have hu := hs.of_keepRegs ku (by decide)
    have mu : u.gpr .x2=(if chooseOne then BitVec.allOnes 64 else 0#64) := by
      rw [ku.gpr .x2 (by decide),mask]
    have ou : Outside base o 8 s.mem u.mem := by
      rw [eu]
      exact writeW_outside _ _ _ (by have h:=hs.enc; omega_arith)
    refine WP.mono (finish_y_words_ok chooseOne n false hu (by omega_arith) (by omega_arith) mu)
      fun t ⟨tail,kt,ot⟩ => ?_
    refine ⟨?_,ku.trans kt,?_⟩
    · intro j hj
      cases j with
      | zero =>
        rw [Nat.mul_zero,Nat.add_zero,ot.word (by omega_arith) (by have h:=hs.enc; omega_arith),eu,word_writeW_self]
        simp only [decide_true,Bool.and_true]
      | succ j =>
        have e : o+8*(j+1)=(o+8)+8*j := by omega_arith
        rw [e,tail j (by omega_arith)]
        have saved : word u.mem base ((o+8)+8*j)=word s.mem base ((o+8)+8*j) :=
          ou.word (by omega_arith) (by have h:=hs.enc; omega_arith)
        rw [saved]
        simp only [Bool.false_and,Nat.succ_ne_zero,decide_false,Bool.and_false]
    · exact (ou.mono (by omega_arith) (by omega_arith)).trans (ot.mono (by omega_arith) (by omega_arith))

end VG.Proof.Weierstrass.AArch64.P521Native
