import VerifiedGarbage.Proof.P256.Linear.FortyOneCore

namespace VG.Proof.P256.Linear.FortyOne
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open Weak (W4 value)

def reference (o a b : Nat) : List Instr :=
  loads [.x1,.x2,.x3,.x4] a ++ loads [.x9,.x10,.x11,.x12] b ++ prefixCode ++ reduce ++ back ++ stores [.x14,.x1,.x2,.x3] o

theorem input_value (s : State) : regsVal s [.x1,.x2,.x3,.x4]=value (input s) := by
  simp only [regsVal,value,input,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
theorem other_value (s : State) : regsVal s [.x9,.x10,.x11,.x12]=value (other s) := by
  simp only [regsVal,value,other,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
theorem output_value (s : State) : regsVal s [.x14,.x1,.x2,.x3]=value (output s) := by
  simp only [regsVal,value,output,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]

theorem reference_ok {s : State} {base : Addr} {size o a b : Nat}
    (hs : Scr s base size) (ho : o+32≤size) (ha : a+32≤size) (hb : b+32≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (haP : wordsVal s.mem base a 4<p) (hbP : wordsVal s.mem base b 4<p) :
    WP isa (.block (reference o a b)) s fun t =>
      KeepRegs (clob 4) s t ∧ VG.Proof.Mont.Outside base o 32 s.mem t.mem ∧
      wordsVal t.mem base o 4=(4*wordsVal s.mem base a 4+p-wordsVal s.mem base b 4)%p := by
  unfold reference
  simp only [List.append_assoc]
  rw [WP.block_append_iff,loads_eq]
  refine WP.mono (loadsR_ok [.x1,.x2,.x3,.x4] hs.ptr ha ha8 (by decide) (by decide)) fun s1 ⟨e1,k1,_⟩ => ?_
  rw [WP.block_append_iff,loads_eq]
  refine WP.mono (loadsR_ok [.x9,.x10,.x11,.x12] (hs.of_keeps k1 (by decide)).ptr hb hb8 (by decide) (by decide)) fun s2 ⟨e2,k2,_⟩ => ?_
  have v1 : value (input s2)=wordsVal s.mem base a 4 := by
    rw [←input_value]
    calc
      regsVal s2 [.x1,.x2,.x3,.x4]=regsVal s1 [.x1,.x2,.x3,.x4] := by
        apply regsVal_congr
        intro r hr
        apply k2.gpr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide
      _ = _ := e1
  have v2 : value (other s2)=wordsVal s.mem base b 4 := by
    rw [←other_value]
    change regsVal s2 [.x9,.x10,.x11,.x12]=wordsVal s1.mem base b 4 at e2
    simpa only [k1.mem] using e2
  rw [WP.block_append_iff]
  refine WP.mono (prefix_ok s2) fun s3 ⟨e3,h3,z3,k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s3 z3) fun s4 ⟨e4,c4,k4⟩ => ?_
  rw [WP.block_append_iff]
  have z4 : s4.gpr .x17=0 := (k4.gpr .x17 (by decide)).trans z3
  refine WP.mono (back_ok s4 z4) fun s5 ⟨e5,k5⟩ => ?_
  have kk : Keeps (clob 4) s s5 := (k1.mono (by decide)).trans ((k2.mono (by decide)).trans
    ((k3.mono (by decide)).trans ((k4.mono (by decide)).trans (k5.mono (by decide)))))
  refine WP.mono (stores_ok [.x14,.x1,.x2,.x3] (hs.of_keeps kk (by decide)) ho ho8 (by decide)) fun t ⟨et,kt,ot⟩ => ?_
  change wordsVal t.mem base o 4=regsVal s5 [.x14,.x1,.x2,.x3] at et
  change VG.Proof.Mont.Outside base o 32 s5.mem t.mem at ot
  refine ⟨(Keeps.regs kk).trans (kt.mono (by simp)),by simpa only [kk.mem] using ot,?_⟩
  rw [et,output_value,e5,e4,c4,e3,h3]
  change value (result (input s2) (other s2))=_
  rw [result_value _ _ (by rw [v1]; exact haP) (by rw [v2]; exact hbP),v1,v2]
end VG.Proof.P256.Linear.FortyOne
