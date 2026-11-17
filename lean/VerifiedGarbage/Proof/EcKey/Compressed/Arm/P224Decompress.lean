module

import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Umaal
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressMain
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
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
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P224.Arm
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressContract
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Tonelli
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P224Decompress

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P224

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.decompress p224

materialize_shared baseline := code

/-- The function with `umaal`. -/
abbrev codeU : Prog isa := Impl.EcKey.Compressed.Arm.decompress (p224With true)

materialize_shared umaal := codeU

abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)

/-! The functions modulo `p` as literals, for their summaries (the kernel would otherwise build
their instructions once for the analysis and once for the frame). -/
materialize_code mulModP := Impl.Weierstrass.Arm.Mont.mulFnWith false p224.SP.k p224.SP.m
materialize_code addModP := Impl.Weierstrass.Arm.Mont.addFnWith false p224.SP.k p224.SP.m
materialize_code subModP := Impl.Weierstrass.Arm.Mont.subFnWith false p224.SP.k p224.SP.m

/-! The constant-time analyses of the calls of the functions modulo `p`, from their arguments,
each done once for the six checks of `ct` (`taint_decide_sum`), which would each analyse the
functions' code again. They keep what is public of `r10` (which the callers keep `lr` in) and of
the loops' counter `r11`: the functions write neither. The analysis is `taintS`'s, which has
summaries (`Proof/Framework/Arm/TaintMono.lean`); `ctU`'s is `taintU`'s, which has none. -/
taint_summary mulPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (Impl.Weierstrass.Arm.Mont.mulName false p224.SP)
    (Impl.Weierstrass.Arm.Mont.mulFnWith false p224.SP.k p224.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])
taint_summary addPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (Impl.Weierstrass.Arm.Mont.addName false p224.SP)
    (Impl.Weierstrass.Arm.Mont.addFnWith false p224.SP.k p224.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])
taint_summary subPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (Impl.Weierstrass.Arm.Mont.subName false p224.SP)
    (Impl.Weierstrass.Arm.Mont.subFnWith false p224.SP.k p224.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])

theorem ct : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub code := by
  apply decompress_tonelli_ct p224_ok (by decide +kernel)
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r0, .r1, .r2])
    · intro s t _ _ ⟨_, h0, h1, h2⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr, .r11])
    · intro s t _ _ ⟨⟨hb, ho⟩, hc⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hb
      · exact ho
      · exact hc
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide_sum [mulPSum, addPSum, subPSum]

theorem ctU : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub codeU := by
  apply decompress_tonelli_ct p224u_ok (by decide +kernel)
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2])
    · intro s t _ _ ⟨_, h0, h1, h2⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr, .r11])
    · intro s t _ _ ⟨⟨hb, ho⟩, hc⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hb
      · exact ho
      · exact hc
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr])
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

theorem verifiedU (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target codeU (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct (p224With true) p224u_ok _
      (candidateTonelli_correct p224u_ok (by decide +kernel) (by decide +kernel))) ctU
    (decompress_implies Spec.EcKey.P224.inst _
      (Proof.P224.rootFacts hL) sat)

end VG.Proof.EcKey.Compressed.Arm.P224Decompress
