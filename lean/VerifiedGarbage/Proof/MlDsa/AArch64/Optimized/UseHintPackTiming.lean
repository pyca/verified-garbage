import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackContract
import VerifiedGarbage.Proof.Framework.AArch64.Taint

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
