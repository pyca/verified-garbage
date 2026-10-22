module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressVerified
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.P224.Sqrt
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Tonelli
import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressCT
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressCT
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.RootCT
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.P224Decompress

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.P224

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.decompress p224

materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem ct : ConstantTime isa (decompressContract Spec.P224.curve (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11))).pre
    (decompressContract Spec.P224.curve (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11))).pub code := by
  apply decompress_tonelli_ct p224_ok (by decide +kernel)
    (candidateTonelli_correct p224_ok (by decide +kernel) (by decide +kernel)) sp
  · apply VG.Taint.constantTime (A := taint) (codecT (2 * Spec.P224.curve.len + 1))
    · exact fun _ _ hs ht hp => codec_agree hs ht hp
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (rootT p224)
    · exact fun _ _ _ _ hp => root_agree hp
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (rootT p224)
    · exact fun _ _ _ _ hp => root_agree hp
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (powerT p224)
    · exact fun _ _ _ _ hp => power_agree hp
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (rootT p224)
    · exact fun _ _ _ _ hp => root_agree hp
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (rootT p224)
    · exact fun _ _ _ _ hp => root_agree hp
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (finishT p224)
    · exact fun _ _ hs ht hp => finish_agree hs ht hp.1 hp.2
    · taint_decide

theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 29 57) 0 = 0x1000 := by decide
  have a1 : arg (satState 29 57) 1 = 0x2000 := by decide
  have a2 : arg (satState 29 57) 2 = 0x8000 := by decide
  have ea : argAddr (satState 29 57) 0 = 0x20004 := by decide
  have esp : (satState 29 57).gpr .esp = 0x20000 := rfl
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 29 57)

theorem verified (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target code (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 28) :=
  decompress_verified (p224_ok) Spec.EcKey.P224.inst rfl (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)) (candidateTonelli_correct (p224_ok) (by decide +kernel) (by decide +kernel)) (Proof.P224.rootFacts hL) sp ct sat

end VG.Proof.EcKey.Compressed.X86.P224Decompress
