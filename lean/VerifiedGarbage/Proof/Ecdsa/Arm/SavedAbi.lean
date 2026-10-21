module

public import VerifiedGarbage.Impl.Ecdsa.Arm
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The shared elliptic-curve save area restores the AAPCS callee-saved registers. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm
open VG VG.Arm

theorem abi_of_saved {s t : State}
    (saved : ∀ p∈VG.Impl.Ecdsa.Arm.Cfg.saved,t.gpr p.1=s.gpr p.1) (sp : t.sp=s.sp) :
    abiPreserved s t := by
  refine ⟨fun r hr => ?_,sp⟩
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact saved (.r4,0) (by decide)
  · exact saved (.r5,4) (by decide)
  · exact saved (.r6,8) (by decide)
  · exact saved (.r7,12) (by decide)
  · exact saved (.r8,16) (by decide)
  · exact saved (.r9,20) (by decide)
  · exact saved (.r10,24) (by decide)
  · exact saved (.r11,28) (by decide)
  · exact saved (.lr,32) (by decide)

end VG.Proof.Ecdsa.Arm
