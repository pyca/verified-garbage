module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.Verified
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.P521

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.P521

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.compress p521

materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem ct : ConstantTime isa (compressContract Spec.P521.curve).pre
    (compressContract Spec.P521.curve).pub code := by
  apply VG.Taint.constantTime (A := taint) (codecT (Spec.P521.curve.len + 1))
  · exact fun _ _ hs ht hp => codec_agree hs ht hp
  · taint_decide

theorem sat : ∃ s, (Spec.EcKey.P521.inst.compressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 133 67) 0 = 0x1000 := by decide
  have a1 : arg (satState 133 67) 1 = 0x2000 := by decide
  have a2 : arg (satState 133 67) 2 = 0x8000 := by decide
  have ea : argAddr (satState 133 67) 0 = 0x20004 := by decide
  have esp : (satState 133 67).gpr .esp = 0x20000 := rfl
  have hlen : Spec.P521.curve.len = 66 := rfl
  sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 133 67)

theorem verified :
    Verified target code (Spec.EcKey.P521.inst.compressPublicKeyContract abi 28) :=
  compress_verified (p521_ok) Spec.EcKey.P521.inst rfl sp ct sat

end VG.Proof.EcKey.Compressed.X86.P521
