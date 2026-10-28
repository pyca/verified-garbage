module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.WriteOutputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Frame
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome

/-! # Small verified I/O adapters surround the shared arithmetic core -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment Input CoreOutcome WrittenCore)

theorem loadInputs_front {E : Environment} {p : BitVec 32} {s : State} (h : Input E s)
    (H : Ws s E.base E.size E.n 32) (C : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size p E.argument s) :
    WP isa loadInputs s fun t => Loaded E s.mem t ∧ Ws t E.base E.size E.n 32 ∧
      Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  loadInputs_ok h H C

theorem writeCore_front {E : Environment} {sp : BitVec 32} {s : State} {e p q : Nat} (h : Input E s)
    (C : VG.Proof.RsaKeyGen.X86.KeyArgs.Context E.base E.size sp E.argument s)
    (apart : ∀ i < 7, (VG.Proof.RsaKeyGen.X86.KeyArgs.argsRegion sp).Disjoint (E.outputRegion i))
    (result : CoreOutcome E.base E.n e p q s.mem) :
    WP isa writeOutputs s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ WrittenCore E.outputs e p q t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  writeCore_ok h.outputs ⟨h.valid, C, fun i hi => by rw [h.valid.outputRegion hi]; exact apart i hi⟩ result

end VG.Proof.RsaKeyGen.X86.KeyRuntime
