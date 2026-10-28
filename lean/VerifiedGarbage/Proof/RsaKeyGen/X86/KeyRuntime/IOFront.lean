module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SelectIO
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Frame

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

theorem writeCore_front {E : Environment} {s : State} {e p q : Nat} (h : Input E s)
    (result : CoreOutcome E.base E.n e p q s.mem) :
    WP isa (selectIO VG.Impl.RsaKeyGen.X86.Key.writeOutputs) s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ WrittenCore E.outputs e p q t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  refine selectIO_ok h fun u Ku memory => ?_
  have hu := h.keep (h.ws.rest Ku) Ku (by intro d hd; rw [memory])
  have Ru : CoreOutcome E.base E.n e p q u.mem := by rw [memory]; exact result
  refine WP.mono (VG.Proof.RsaKeyGen.X86.Key.writeCore_ok (g := E.outputs) (s := u)
    (e := e) (p := p) (q := q) hu.outputs Ru)
    fun t ⟨ht, written, F, K⟩ => ?_
  rw [memory] at F
  exact ⟨ht, written, F, (Ku.mono (by decide)).trans K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
