module

public import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation
import VerifiedGarbage.Proof.Ffdh.X86.Shape

/-! Ordinary instructions preserve ESP; the existing balanced symbol frame is explicit. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86
open VG.Impl.Ffdh.X86.VettedValidation

theorem spSafe : code.all (fun i => !isa.writesSp i) = true := by
  have before : recognize.all (fun i => !isa.writesSp i) = true := by decide +kernel
  change (recognize.all (fun i => !isa.writesSp i) &&
    (true && (true && VG.Impl.Ffdh.X86.CheckDomain.code.all (fun i => !isa.writesSp i)))) = true
  rw [before, VG.Proof.Ffdh.X86.Shape.checkDomain_spSafe]
  rfl

end VG.Proof.Ffdh.X86.VettedValidation
