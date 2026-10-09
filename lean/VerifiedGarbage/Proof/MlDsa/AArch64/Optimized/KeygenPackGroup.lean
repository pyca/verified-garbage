import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackInput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackTail

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def groupCode (signed : Bool) (_b d c : Nat) : List Instr :=
  loadVec signed c ++ (List.range c).flatMap (field d) ++ tail (d*c/8)

def groupResult (signed : Bool) (b d c : Nat) (m : Mem) (input out : Addr) : Mem × BitVec 64 :=
  let f := fieldsRun d out (inputValue signed b m input) ⟨m,0⟩ c
  tailResult (d*c/8) f.mem out f.acc

theorem group_ok (signed : Bool) (b d c : Nat) (hd : d≤20) (hc : 0<c) (hc8 : c≤8) (hc4 : c%4=0)
    (hn : TailWidth (d*c/8)) (s : State) (hconst : signed=true → Constants b s)
    (hin : ∀off,off+16≤4*c → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hout : ∀off sz,off+sz≤d*c/8 → InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 off) sz) :
    WP isa (.block (groupCode signed b d c)) s fun t =>
      Keep [.x9,.x10,.x11] s t ∧ (signed=true → Constants b t) ∧
      t.mem=(groupResult signed b d c s.mem (s.gpr .x0) (s.gpr .x2)).1 ∧
      t.gpr .x9=(groupResult signed b d c s.mem (s.gpr .x0) (s.gpr .x2)).2 := by
  simp only [groupCode,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadVec_ok signed b c hc8 hc4 s hconst hin) fun a ⟨ha,ca,hvalues⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fields_ok d c hd hc8 a ?_) fun f ⟨hf,hfv,hfm,hfa⟩ => ?_
  · intro off ho
    simpa only [ha.wr,ha.gpr] using hout off 8 ho
  · have he : fieldsRun d (a.gpr .x2) (fieldValue a.v) ⟨a.mem,a.gpr .x9⟩ c=
        fieldsRun d (s.gpr .x2) (inputValue signed b s.mem (s.gpr .x0)) ⟨s.mem,0⟩ c := by
      rw [ha.gpr,ha.mem,fieldsRun_values d (s.gpr .x2) _ _ _ hvalues]
      exact fieldsRun_acc_irrel d hd _ _ _ _ _ hc
    rw [he] at hfm hfa
    refine WP.mono (tail_ok (d*c/8) hn f ?_) fun t ⟨⟨⟨htm,hta⟩,ht⟩,htv⟩ => ?_
    · intro off sz ho
      simpa only [hf.wr,ha.wr,hf.get .x2,ha.gpr] using hout off sz ho
    · refine ⟨((ha.keep.trans hf).trans ht).mono,?_,?_,?_⟩
      · intro h
        have hh := ca h
        exact ⟨by rw [htv,hfv]; exact hh.bias,by rw [htv,hfv]; exact hh.modulus⟩
      · rw [htm,hfm,hfa,hf.get .x2,ha.gpr]
        rfl
      · rw [hta,hfm,hfa,hf.get .x2,ha.gpr]
        rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
