module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyInverse
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
import VerifiedGarbage.Proof.Rsa.X86.InverseTiming
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # The inverse wrapper's complete schedule is independent of its inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key

theorem copyWords_public (n src dst : Nat) : KeyPublic (VG.Impl.Rsa.X86.Div.copyWords n src dst) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0))),
      ({ regs := .ofList [.edi, .esi, .ebp, .edx, .ecx], flags := true } : VG.X86.Taint.T), ?_, by decide +kernel⟩
  exact (check_of_erase_eq (VG.Impl.Rsa.X86.Div.copyWords n src dst) (VG.Impl.Rsa.X86.Div.copyWords 1 0 0)
    (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem setOne_public (n j : Nat) : KeyPublic (.block (setOne n j)) := by
  refine ⟨(VG.Taint.hintOf taint (workspaceTaint true) (.block [.mov .eax (.imm 0),
      .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)), ({ regs := .ofList [.edi, .esi, .eax], flags := false } : VG.X86.Taint.T), ?_, by decide +kernel⟩
  exact (check_of_erase_eq (.block (setOne n j)) (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)
    (workspaceTaint true) (VG.Taint.hintOf taint (workspaceTaint true) (.block [.mov .eax (.imm 0),
        .store (VG.Impl.Mont.X86.sc 0) .eax] : Prog isa)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)

theorem inverseBank_public (n : Nat) : KeyPublic (inverseBank n) := by
  unfold inverseBank
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact copy_public ..
  · exact setOne_public ..
  · exact sub3_public ..

theorem inverseLoad_public (n src mo : Nat) : KeyPublic (inverseLoad n src mo) := by
  unfold inverseLoad
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨zerosHint true, zerosTaint true, zeros_check true _ _, rfl⟩
  · exact copyWords_public ..
  · exact copyWords_public ..

theorem inverseFrom_public (n src mo : Nat) : KeyPublic (inverseFrom n src mo) := by
  exact ((inverseLoad_public n src mo).seq (inverseBank_public n)).seq (inverse_public n)

theorem inverseFrom_constantTime (n src mo : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree (workspaceTaint true)) (inverseFrom n src mo) := by
  obtain ⟨hint, out, checked, _⟩ := inverseFrom_public n src mo
  exact VG.Taint.constantTime (A := taint) (workspaceTaint true) (fun _ _ _ _ H => H)
    (hc := hint) (by rw [checked]; rfl)

end VG.Proof.RsaKeyGen.X86.Key
