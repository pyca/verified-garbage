import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackProg
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! ## From `UseHintPackContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)
open HighPack (packWidth)

def packK (g : Nat) : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x1),polyRegion (s.gpr .x2)] ∧
    s.wr=[⟨s.gpr .x0,32*packWidth g⟩] ∧
    (polyRegion (s.gpr .x1)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩ ∧
    (polyRegion (s.gpr .x2)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩ ∧
    arg32 s .x3=g ∧ Reduced s.mem (s.gpr .x2)
  post s t := Spec.Sha3.bytesAt t.mem (s.gpr .x0) (32*packWidth g)=
    packed g s.mem (s.gpr .x1) (s.gpr .x2)
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧
    s.gpr .x2=t.gpr .x2 ∧ (s.gpr .x3).setWidth 32=(t.gpr .x3).setWidth 32 ∧ s.sp=t.sp

theorem pack_pre {g : Nat} {s : State} (hp : (packK g).pre s) : Pre g s := by
  obtain ⟨rd,wr,hs,ws,hg,hr⟩ := hp
  refine ⟨hg,hr,?_,?_,?_,ws,hs⟩
  · rw [rd];exact ⟨polyRegion (s.gpr .x2),by simp,Region.contains_self _ _⟩
  · rw [rd];exact ⟨polyRegion (s.gpr .x1),by simp,Region.contains_self _ _⟩
  · rw [wr];exact ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩

/-- Full selected program satisfies the AArch64 calling convention. -/
theorem pack_correct {g : Nat} (hg : IsG g) (s : State) (hp : (packK g).pre s) :
    ∃ tr t, Exec isa Impl.MlDsa.AArch64.Optimized.UseHintPack.prog s tr t ∧
      abiPreserved s t ∧ (packK g).post s t := by
  obtain ⟨tr,t,he,ht⟩ := prog_ok hg (pack_pre hp)
  exact ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he,ht.bytes⟩

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Round

private def shuffled (s : State) : State :=
  ((s.write .x .x4 (s.gpr .x1)).write .x .x5 (s.gpr .x2)).write .x .x1 (s.gpr .x0)

private theorem shuffled_exec (s : State) :
    Exec isa (.block [.addImm .x .x4 .x1 0,.addImm .x .x5 .x2 0,.addImm .x .x1 .x0 0])
      s [] (shuffled s) := by
  apply Exec.block
  simp [shuffled,execBlock,isa,exec,addrs,State.read,State.write]

private theorem body_ct :
    ConstantTime isa (fun _=>True)
      (fun s t=>s.sp=t.sp ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x4=t.gpr .x4 ∧
        s.gpr .x5=t.gpr .x5 ∧ (s.gpr .x3).setWidth 32=(t.gpr .x3).setWidth 32)
      (zext .x3 (onGamma .x3 .x6 Impl.MlDsa.AArch64.Optimized.UseHintPack.code)) := by
  apply zext_ct (τ:=Taint.ofRegs [.x3,.x1,.x4,.x5])
  · intro s t h
    apply agree_zext h.1 h.2.2.2.2
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
  · taint_decide

/-- Data and hint values stay secret; only pointers and the low32 public gamma are related. -/
theorem pack_ct {g : Nat} : ConstantTime isa (packK g).pre (packK g).pub
    Impl.MlDsa.AArch64.Optimized.UseHintPack.prog := by
  intro s t l r s' t' _ _ hp hs ht
  cases hs with | seq a b =>
    cases ht with | seq c d =>
      obtain ⟨rfl,rfl⟩ := Exec.det a (shuffled_exec s)
      obtain ⟨rfl,rfl⟩ := Exec.det c (shuffled_exec t)
      apply body_ct _ _ _ _ _ _ trivial trivial ?_ b d
      rcases hp with ⟨h0,h1,h2,h3,hsp⟩
      simpa [shuffled,State.write] using And.intro hsp (And.intro h0 (And.intro h1 (And.intro h2 h3)))

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end
