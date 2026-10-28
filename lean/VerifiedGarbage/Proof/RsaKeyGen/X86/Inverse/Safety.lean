module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Inverse
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Framed
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # `vg_rsa_keygen_inverse` moves `esp` only by its frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86

theorem code_sp : (VG.Impl.RsaKeyGen.X86.Inverse.code).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  rw [equal]
  have frame : ∀ (p q : Instr) (b : Prog isa) (f : Instr → Bool),
      (Code.frame p b q).allInstrs f = (f p && b.allInstrs f && f q) := fun _ _ _ _ => rfl
  unfold VG.Impl.RsaKeyGen.X86.Inverse.code
  rw [frame, VG.Proof.RsaKeyGen.X86.KeyNoSp.checked inner_noSp]
  rfl

end VG.Proof.RsaKeyGen.X86.Inverse
