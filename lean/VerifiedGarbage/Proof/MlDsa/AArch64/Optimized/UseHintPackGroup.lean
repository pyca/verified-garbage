import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackFields

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep VChg)
open HighPack (packWidth)

def groupCode (g : Nat) : List Instr :=
  loadFour g++Impl.MlDsa.AArch64.Optimized.HighPack.packTail (packWidth g)

structure GroupPost (g block : Nat) (h a : Addr) (s t : State) : Prop where
  keep : Keep [.x9] s t
  vec : ∀r,r∉temps→t.v r=s.v r
  ready : Ready g t
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀i<2*packWidth g,t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    (packed g s.mem h a)[2*packWidth g*block+i]!

 theorem group_ok {g : Nat} (hg : IsG g) {block : Nat} (hb : block<16)
    {h a : Addr} {s : State} (hr : Reduced s.mem a) (hc : Ready g s)
    (hp : s.gpr .x5=a+BitVec.ofNat 64 (64*block))
    (hhp : s.gpr .x4=h+BitVec.ofNat 64 (64*block))
    (ha : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16)
    (hh : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6→InRegions s.wr (s.gpr .x1+8) 4)
    {rest : List Instr} {Q : State→Prop}
    (k : ∀t,GroupPost g block h a s t→WP isa (.block rest) t Q) :
    WP isa (.block (groupCode g++rest)) s Q := by
  unfold groupCode
  rw [List.append_assoc]
  refine loadFour_ok hg hc ha hh fun u hu cu hv=>?_
  refine HighPack.packTail_ok hg cu.toPackReady (by rw [hu.wr,hu.gpr];exact hw8)
    (fun h=>by rw [hu.wr,hu.gpr];exact hw4 h) fun t ht=>?_
  refine k t ⟨(hu.keep.trans ht.keep).mono (by decide),?_,?_,?_,?_⟩
  · intro r hr
    rw [ht.vec r (by intro h;exact hr (by simp only [temps,List.mem_cons,List.not_mem_nil,or_false] at *;grind only)),hu.get r hr]
  · refine ⟨ht.ready,?_,?_,?_⟩
    · intro e he;rw [ht.vec .v21 (by decide)];exact cu.factor e he
    · intro e he;rw [ht.vec .v22 (by decide)];exact cu.one e he
    · intro e he;rw [ht.vec .v23 (by decide)];exact cu.z e he
  · simpa only [hu.gpr,hu.mem] using ht.frame
  · intro i hi
    have hx:=ht.bytes i hi
    rw [hu.gpr] at hx
    rw [hx]
    exact packed_fields_byte hg hr cu.toPackConstants hb hi (by simpa only [hp,hhp] using hv)

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
