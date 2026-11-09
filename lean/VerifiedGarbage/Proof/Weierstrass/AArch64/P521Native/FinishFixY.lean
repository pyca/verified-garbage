module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishZeroMask
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowZero
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Lit

/-! Adjacent stages of the final P-521 window, sharing their machine-state interface. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ed25519.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def finishYArith (first : Bool) : List Instr := [
  .bicRor .x .x9 .x9 .x2 0,
  .movz .x .x4 (if first then 1 else 0) 0,
  .movk .x .x4 0 1,.movk .x .x4 0 2,.movk .x .x4 0 3,
  .logic .and .x .x4 .x4 .x2,.logic .orr .x .x4 .x4 .x9]

theorem finish_y_arith_ok (s : State) (first chooseOne : Bool)
    (mask : s.gpr .x2=if chooseOne then BitVec.allOnes 64 else 0#64) :
    WP isa (.block (finishYArith first)) s fun t =>
      t.gpr .x4=(if chooseOne then (if first then 1#64 else 0#64) else s.gpr .x9) ∧
      Keeps [.x9,.x4] s t := by
  cases first <;> cases chooseOne <;>
    apply WP.of_runBlock <;>
    simp only [finishYArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
      Nat.reduceLT,Nat.reduceMul,BitVec.shiftLeft_zero,RegUpd.gpr_write,BitVec.setWidth_eq,
      mask,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  all_goals refine ⟨?_,⟨?_,?_,?_,?_,?_⟩⟩
  all_goals try rfl
  all_goals try reg_keeps
  all_goals try simp
  all_goals first | exact BitVec.and_allOnes | decide

def finishYWord (o : Nat) (first : Bool) : List Instr :=
  [.ldr .x .x9 .x0 o]++finishYArith first++[.str .x .x4 .x0 o]

theorem finish_y_word_ok {s : State} {base : Addr} {W o : Nat} (hs : Scr s base W)
    (ho : o+8≤W) (ho8 : o%8=0) (first chooseOne : Bool)
    (mask : s.gpr .x2=if chooseOne then BitVec.allOnes 64 else 0#64) :
    WP isa (.block (finishYWord o first)) s fun t =>
      t.mem=s.mem.writeW (off base o)
        (if chooseOne then (if first then 1#64 else 0#64) else word s.mem base o) ∧
      KeepRegs [.x9,.x4] s t := by
  rw [finishYWord,List.append_assoc,WP.block_append_iff]
  refine WP.mono (ldR_ok hs.ptr ho ho8 .x9) fun u ⟨eu,ku,_⟩ => ?_
  rw [WP.block_append_iff]
  have mu : u.gpr .x2=if chooseOne then BitVec.allOnes 64 else 0#64 := by
    rw [ku.gpr .x2 (by decide),mask]
  refine WP.mono (finish_y_arith_ok u first chooseOne mu) fun v ⟨ev,kv⟩ => ?_
  have hv : Scr v base W := (hs.of_keeps ku (by decide)).of_keeps kv (by decide)
  refine WP.mono (stR_ok hv.ptrW ho ho8 .x4) fun t et => ?_
  have k : Keeps [.x9,.x4] s v := (ku.mono (by simp)).trans kv
  refine ⟨?_,?_⟩
  · rw [et,ev,eu,kv.mem,ku.mem]
  · rw [et]
    exact ⟨k.gpr,k.rd,k.wr,k.sp⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

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

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ed25519.AArch64

def finishZMaskCode (z : Nat) : List Instr :=
  [.movz .x .x7 0 0,.ldr .x .x1 .x0 z]++windowOrCode (z+8) 8++finishZeroMaskCode

theorem finish_z_mask_ok {s : State} {base : Addr} {size z : Nat}
    (hs : Scr s base size) (hz : z+72≤size) (hz8 : z%8=0) :
    WP isa (.block (finishZMaskCode z)) s fun t =>
      t.gpr .x2=(if wordsVal s.mem base z 9=0 then BitVec.allOnes 64 else 0#64) ∧
      Keeps [.x1,.x2,.x5,.x7,.x16] s t := by
  rw [finishZMaskCode,List.append_assoc,WP.block_append_iff]
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
  refine WP.mono (finish_zero_mask_ok w zw) fun t ⟨et,kt⟩ => ?_
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

end

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

end
