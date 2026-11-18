module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressMain
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P192.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P192.Arm
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressFront
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.Arm.Target

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P192Decompress

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P192

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.decompress p192

materialize_shared baseline := code

/-- The function with `umaal`. -/
abbrev codeU : Prog isa := Impl.EcKey.Compressed.Arm.decompress (p192With true)

materialize_shared umaal := codeU

def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (h : (decompressContract Spec.P192.curve Impl.EcKey.Compressed.rootThreeModFour).pub s t) : VG.Arm.Taint.Agree τ₀ s t := by
  obtain ⟨_, h0, h1, h2⟩ := h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩,
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem ct : ConstantTime isa (decompressContract Spec.P192.curve Impl.EcKey.Compressed.rootThreeModFour).pre (decompressContract Spec.P192.curve Impl.EcKey.Compressed.rootThreeModFour).pub code :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ _ _ h => agree_τ₀ h) (by taint_decide)

theorem ctU : ConstantTime isa (decompressContract Spec.P192.curve Impl.EcKey.Compressed.rootThreeModFour).pre (decompressContract Spec.P192.curve Impl.EcKey.Compressed.rootThreeModFour).pub codeU :=
  VG.Taint.constantTime (A := taintU) τ₀ (fun _ _ _ _ h => agree_τ₀ h) (by taint_decide)

theorem sat : ∃ s, (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P192.curve.len = 24 := rfl
  sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, decompressSatState] [decompressSatState] using (decompressSatState 24)

theorem verified (hL : Proof.Weierstrass.Law Spec.P192.curve) :
    Verified target code (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct p192 p192_ok _ (candidateThree_correct p192_ok (by decide +kernel))) ct
    (decompress_implies Spec.EcKey.P192.inst _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sat)

theorem verifiedU (hL : Proof.Weierstrass.Law Spec.P192.curve) :
    Verified target codeU (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct (p192With true) p192u_ok _ (candidateThree_correct p192u_ok (by decide +kernel))) ctU
    (decompress_implies Spec.EcKey.P192.inst _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sat)

end VG.Proof.EcKey.Compressed.Arm.P192Decompress
