module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyStep
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Scan the vetted records in order and stop exactly at the first complete match. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)

theorem policyLoop_ok {s : State} {B src table : Addr} {Z k N : Nat} {dom : List Byte} {gs : List Policy.Group}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (source : Source src dom s) (records : PolicyTableAt B table gs s)
 (shape : dom.length=2*k ∨ dom.length=3*k) (positive : 0<k) (size : k<2^28)
 (domain : word s.mem B (8*sDom)=src) (length : word s.mem B (8*sDL)=BitVec.ofNat 64 dom.length)
 (keyLength : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (width : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (fit : N<2^64)
 (pointer : s.gpr .x4=table) (count : s.gpr .x7=BitVec.ofNat 64 gs.length)
 (nonempty : gs≠[]) (small : gs.length<2^64) :
 WP isa (.loop Policy.record (.nonzero .x .x7)) s fun t =>
 word t.mem B (8*sBits)=BitVec.ofNat 64 (policyWidth N k dom gs) ∧
 Outside B (8*sBits) 8 s.mem t.mem ∧ Keep recordClobbers s t := by
 let I := fun n t => ∃ rest cursor,
  n=rest.length ∧ rest≠[] ∧ rest.length≤gs.length ∧ PolicyTableAt B cursor rest t ∧
  t.gpr .x4=cursor ∧ t.gpr .x7=BitVec.ofNat 64 rest.length ∧
  policyWidth N k dom rest=policyWidth N k dom gs ∧ t.mem=s.mem ∧ Keep recordClobbers s t
 refine WP.loop (M:=isa) I ?_ gs.length s ?_
 · intro n t h
   obtain ⟨rest,cursor,remaining,notNil,atMost,tableT,ptrT,countT,rule,memT,keepT⟩ := h
   cases rest with
   | nil => exact False.elim (notNil rfl)
   | cons g tail =>
     have head := tableT.1
     have nextTable := tableT.2
     refine WP.mono (policyStep_ok (scratch.congr keepT.wr) room
      ((keepT.gpr .x0 (by simp [recordClobbers])).trans base) (source.of_mem memT keepT) head
      shape positive size (memT ▸ domain) (memT ▸ length) (memT ▸ keyLength) (memT ▸ width) fit
      ptrT countT (by simp)) ?_
     rintro u ⟨memU,countU,ptrU,keepU⟩
     have totalKeep : Keep recordClobbers s u := (keepT.trans keepU).mono (by simp)
     by_cases matched : k=g.len ∧ dom=g.domain.take dom.length
     · left
       have result : min N g.bits=policyWidth N k dom gs := by
        rw [←rule,policyWidth,ite_eq_left matched]
       refine ⟨?_,?_,?_,totalKeep⟩
       · rw [eval_nonzero,countU,ite_eq_left matched]
         decide
       · rw [memU,ite_eq_left matched,word_writeW_self,result]
       · rw [memU,ite_eq_left matched,memT]
         exact writeW_outside _ _ _ (by decide)
     · have mem : u.mem=s.mem := by rw [memU,ite_eq_right matched,memT]
       have nextRule : policyWidth N k dom tail=policyWidth N k dom gs := by
        rw [←rule,policyWidth,ite_eq_right matched]
       cases tail with
       | nil =>
         left
         refine ⟨?_,?_,?_,totalKeep⟩
         · rw [eval_nonzero,countU,ite_eq_right matched]
           change some (0#64 != 0#64)=some false
           decide
         · rw [mem,width,←nextRule]
           rfl
         · rw [mem]
           exact Outside.refl _ _ _ _
       | cons a tail =>
         right
         refine ⟨?_,(a::tail).length,by simp only [List.length_cons] at remaining ⊢;omega,
          a::tail,off cursor (8+3*g.len),rfl,by simp,by simp only [List.length_cons] at atMost ⊢;omega,
          nextTable.after_mem (by rw [memU,ite_eq_right matched]) keepU,ptrU,?_,nextRule,mem,totalKeep⟩
         · rw [eval_nonzero,countU,ite_eq_right matched]
           simp only [List.length_cons,Nat.add_sub_cancel]
           change some (BitVec.ofNat 64 (tail.length+1) != 0#64)=some true
           rw [ofNat_nonzero (by simp only [List.length_cons] at atMost;omega),decide_eq_true (by omega : 0<tail.length+1)]
         · simpa only [ite_eq_right matched,List.length_cons,Nat.add_sub_cancel] using countU
 · exact ⟨gs,table,rfl,nonempty,Nat.le_refl _,records,pointer,count,rfl,rfl,Keep.refl _ _⟩

end VG.Proof.Ffdh.AArch64.Cached
