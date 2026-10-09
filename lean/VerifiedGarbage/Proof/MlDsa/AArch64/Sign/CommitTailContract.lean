import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailTiming
import VerifiedGarbage.Spec.MlDsa.CommitTail
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Spec.MlDsa

def kernel (wlen olen : Nat) : Contract isa where
  pre := Pre wlen olen
  post s t := Spec.Sha3.bytesAt t.mem (s.gpr .x2) olen=H
    (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 64++Spec.Sha3.bytesAt s.mem (s.gpr .x1) wlen) olen ∧
    PolyIs t.mem (s.gpr .x6) (toRq (bitUnpack (H (seedBytes s.mem (s.gpr .x4) (s.gpr .x5)) 640) 524287 524288))
  pub := VG.AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x6])

theorem correct (s : State) {wlen olen : Nat} (hp : (kernel wlen olen).pre s) :
    ∃tr t,Exec isa (Impl.MlDsa.AArch64.Sign.CommitTail.code wlen olen) s tr t ∧
      abiPreserved s t ∧ (kernel wlen olen).post s t := by
  obtain ⟨tr,t,he,habi,_,hhash,hmask⟩ := raw_ok s hp
  exact ⟨tr,t,he,habi,hhash,hmask⟩

theorem shared_pre {s : State} {wlen olen : Nat} (hw : wlen=768 ∨ wlen=1024)
    (ho : olen=48 ∨ olen=64) (h : (commitTailContract AArch64.abi wlen olen).pre s) :
    Pre wlen olen s := by
  sig_pre [commitTailContract,commitTailSig,AArch64.abi,AArch64.argRegs] at h
  sig_split h
  have hrd : s.rd=[⟨s.gpr .x0,64⟩,⟨s.gpr .x1,wlen⟩,⟨s.gpr .x4,64⟩] := by with_reducible assumption
  have hwr : s.wr=[⟨s.gpr .x2,olen⟩,⟨s.gpr .x3,2048⟩,⟨s.gpr .x6,1024⟩] := by with_reducible assumption
  refine ⟨⟨hw,?_,?_,?_,?_,?_,?_,?_⟩,ho,?_,?_,?_,?_,?_,?_⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x0,64⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by omega)⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x1,wlen⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by rcases hw with rfl|rfl <;> omega)⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x4,64⟩,by rw [hrd]; simp,Offset.contains_base _ hn (by omega)⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x3,2048⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by omega)⟩
  · with_reducible assumption
  · with_reducible assumption
  · exact Region.Disjoint.symm (by with_reducible assumption)
  · intro d n hn
    exact ⟨⟨s.gpr .x2,olen⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by rcases ho with rfl|rfl <;> omega)⟩
  · exact ⟨⟨s.gpr .x6,1024⟩,by rw [hwr]; simp,by simp [Region.Contains]⟩
  · intro d n hn
    exact ⟨⟨s.gpr .x3,2048⟩,by rw [hwr]; simp,Offset.contains_base _ hn (by omega)⟩
  · with_reducible assumption
  · exact Region.Disjoint.symm (by with_reducible assumption)
  · with_reducible assumption

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
