import VerifiedGarbage.Proof.P256.Linear.WeakCore

namespace VG.Proof.P256.Linear.Weak
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def reference (o a b : Nat) : List Instr :=
  loads [.x5,.x6,.x7,.x8] a ++ loads [.x9,.x10,.x11,.x12] b ++ addCode ++ reduceCode ++ stores [.x5,.x6,.x7,.x8] o

theorem regs_value (s : State) : regsVal s [.x5,.x6,.x7,.x8]=value (regs s) := by
  simp only [regsVal,value,regs,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]

theorem reference_ok {s : State} {base : Addr} {size o a b : Nat}
    (hs : Scr s base size) (ho : o+32≤size) (ha : a+32≤size) (hb : b+32≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (haP : wordsVal s.mem base a 4<p) (hbP : wordsVal s.mem base b 4<p) :
    WP isa (.block (reference o a b)) s fun t =>
      KeepRegs (clob 4) s t ∧ VG.Proof.Mont.Outside base o 32 s.mem t.mem ∧
      wordsVal t.mem base o 4%p=(wordsVal s.mem base a 4+wordsVal s.mem base b 4)%p := by
  unfold reference
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  rw [loads_eq]
  refine WP.mono (loadsR_ok [.x5,.x6,.x7,.x8] hs.ptr ha ha8 (by decide) (by decide)) fun s1 ⟨e1,k1,_⟩ => ?_
  rw [WP.block_append_iff]
  rw [loads_eq]
  refine WP.mono (loadsR_ok [.x9,.x10,.x11,.x12] (hs.of_keeps k1 (by decide)).ptr hb hb8 (by decide) (by decide)) fun s2 ⟨e2,k2,_⟩ => ?_
  have v1 : value (regs s2)=wordsVal s.mem base a 4 := by
    rw [←regs_value]
    calc
      regsVal s2 [.x5,.x6,.x7,.x8]=regsVal s1 [.x5,.x6,.x7,.x8] := by
        apply regsVal_congr
        intro r hr
        apply k2.gpr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide
      _ = _ := e1
  have v2 : value (s2.gpr .x9,s2.gpr .x10,s2.gpr .x11,s2.gpr .x12)=wordsVal s.mem base b 4 := by
    rw [k1.mem] at e2
    have hh : value (s2.gpr .x9,s2.gpr .x10,s2.gpr .x11,s2.gpr .x12)=regsVal s2 [.x9,.x10,.x11,.x12] := by
      simp only [regsVal,value,val4,Nat.mul_zero,Nat.add_zero,Nat.mul_add,←Nat.mul_assoc,Nat.add_assoc]
    exact hh.trans e2
  rw [WP.block_append_iff]
  refine WP.mono (addCode_ok s2) fun s3 ⟨e3,c3,k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceCode_ok s3) fun s4 ⟨e4,k4⟩ => ?_
  have kk : Keeps (clob 4) s s4 := (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans (k4.mono (by decide))))
  refine WP.mono (stores_ok [.x5,.x6,.x7,.x8] (hs.of_keeps kk (by decide)) ho ho8 (by decide)) fun t ⟨et,kt,ot⟩ => ?_
  change wordsVal t.mem base o 4=regsVal s4 [.x5,.x6,.x7,.x8] at et
  change VG.Proof.Mont.Outside base o 32 s4.mem t.mem at ot
  refine ⟨(Keeps.regs kk).trans (kt.mono (by simp)),?_,?_⟩
  · simpa only [kk.mem] using ot
  · rw [et,regs_value,e4,e3,c3]
    have he := weakWords_mod (regs s2) (s2.gpr .x9,s2.gpr .x10,s2.gpr .x11,s2.gpr .x12)
      (by rw [v1]; exact haP) (by rw [v2]; exact hbP)
    simpa only [v1,v2] using he
end VG.Proof.P256.Linear.Weak
