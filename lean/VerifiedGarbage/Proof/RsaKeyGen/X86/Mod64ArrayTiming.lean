module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Two runs of the reduction agree on its public pointers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86

theorem ArrayContext.agree {g : ArrayGeometry} {candidate exponent other otherExponent : Nat} {s t : State}
    (S : ArrayContext g candidate exponent s) (T : ArrayContext g other otherExponent t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.stack.sp.trans T.stack.sp.symm
  · exact S.workspace.trans T.workspace.symm

end VG.Proof.RsaKeyGen.X86.Mod64
