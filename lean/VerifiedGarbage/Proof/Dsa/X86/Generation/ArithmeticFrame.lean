module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! Allocate and initialize the reusable arithmetic argument frame. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86

structure ArithmeticSetup (s t : State) : Prop where
  keeps : Keeps [.eax] (allocFrame 16 s) t
  frame : Frame [below (s.gpr .esp) 16] s.mem t.mem
  zero : t.mem.readW ((t.gpr .esp).setWidth 64 + 4#64) 32 = (0 : BitVec 32)
  workspace : t.mem.readW ((t.gpr .esp).setWidth 64 + 8#64) 32 = s.gpr .edi
  length : t.mem.readW ((t.gpr .esp).setWidth 64 + 12#64) 32 = s.gpr .esi

theorem with_arithmetic {s : State} {body : Prog isa} {Q : State → Prop}
    (low : 16 ≤ (s.gpr .esp).toNat) (noSp : NoSp body)
    (run : ∀ t, ArithmeticSetup s t → WP isa body t fun u => Q (freed 16 u)) :
    WP isa (withArithmetic body) s Q := by
  have argsNoSp : NoSp (.block arithmeticArgs : Prog isa) := NoSp.of_all (by decide)
  have seqNoSp : NoSp (.seq (.block arithmeticArgs) body : Prog isa) := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact argsNoSp i hi
    · exact noSp i hi
  apply WP.frameAlloc (by decide) (by decide) (by decide) low seqNoSp
  have fit : ((allocFrame 16 s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [allocFrame_esp, VG.X86.sub_toNat low]
    have := (s.gpr .esp).isLt
    omega
  refine WP.seq (WP.mono (arithmetic_arguments fit
    (by rw [allocFrame_wr]; exact List.mem_cons_self ..)) fun t ⟨K, F, zero, ws, len⟩ => ?_)
  apply run t
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · exact F
  · rw [K.1 .esp (by decide)]; exact zero
  · rw [K.1 .esp (by decide)]
    simpa only [allocFrame_gpr _ _ (show Reg.edi ≠ .esp by decide)] using ws
  · rw [K.1 .esp (by decide)]
    simpa only [allocFrame_gpr _ _ (show Reg.esi ≠ .esp by decide)] using len

end VG.Proof.Dsa.X86.Generation
