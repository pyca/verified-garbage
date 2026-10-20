module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Copying and shaping the public-width candidate has a fixed schedule -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem pShape_ct (len : Nat) : RelCT isa (RegistersAgree [.edi, .esi]) (pShape len) (fun _ _ => True) := by
  have h : RelCT isa (VG.X86.Taint.Agree (τr [.edi, .esi])) (pShape len) (VG.X86.Taint.Agree (τr [.edi])) :=
    erased_relCT _ (pShape 1) (VG.Taint.hintOf taint (τr [.edi, .esi]) (Code.erase (pShape 1))) rfl rfl rfl rfl
  exact h.mono (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)
end VG.Proof.Dsa.X86.Generation
