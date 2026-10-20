module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrepareExponent
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Copying fixed-width exponents has public addresses and bounds -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem copyWords_relCT (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (VG.Impl.Rsa.X86.Div.copyWords n src dst)
      (VG.X86.Taint.Agree (τr [.edi])) :=
  erased_relCT _ (VG.Impl.Rsa.X86.Div.copyWords 1 0 0)
    (VG.Taint.hintOf taint (τr [.edi]) (Code.erase (VG.Impl.Rsa.X86.Div.copyWords 1 0 0))) rfl rfl rfl rfl

theorem copyWords_ct (n src dst : Nat) :
    RelCT isa (RegistersAgree [.edi]) (VG.Impl.Rsa.X86.Div.copyWords n src dst) (fun _ _ => True) :=
  (copyWords_relCT n src dst).mono (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)

theorem restoreExponent_ct (n : Nat) :
    RelCT isa (RegistersAgree [.edi]) (restoreExponent n) (fun _ _ => True) := by
  unfold restoreExponent
  have tail : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block restoreExponentCount)
      (VG.X86.Taint.Agree (τr [.edi])) := checkedBlockInvariant rfl rfl
  exact (RelCT.seq (copyWords_relCT _ _ _) tail).mono (fun _ _ h => agree_regs h) (fun _ _ _ => trivial)
end VG.Proof.Dsa.X86.Generation
