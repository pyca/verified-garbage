module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressMain
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
import VerifiedGarbage.Proof.P224.Sqrt
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Tonelli
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.RootCT
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.RootCT
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P224.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P224Decompress

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P224

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.decompress p224

materialize_shared baseline := code

abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)

theorem ct : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub code := by
  apply decompress_tonelli_ct p224_ok (by decide +kernel)
  · apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2])
    · intro s t _ _ ⟨_, h0, h1, h2⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r12, .lr, .r11])
    · intro s t _ _ ⟨⟨hb, ho⟩, hc⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hb
      · exact ho
      · exact hc
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide

theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, decompressSatState] [decompressSatState] using (decompressSatState 28)

theorem verified (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target code (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct p224 p224_ok _ (candidateTonelli_correct p224_ok (by decide +kernel) (by decide +kernel))) ct
    (decompress_implies Spec.EcKey.P224.inst _
      (Proof.P224.rootFacts hL) sat)

end VG.Proof.EcKey.Compressed.Arm.P224Decompress
