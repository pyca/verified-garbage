module

import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Main
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Umaal
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.Ecdsa.P521.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.Ecdsa.P521.Arm
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.TCB.Arm.Target

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P521

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P521

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.compress p521

materialize_shared baseline := code

/-- The function with `umaal`. -/
abbrev codeU : Prog isa := Impl.EcKey.Compressed.Arm.compress (p521With true)

materialize_shared umaal := codeU

def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (h : (compressContract Spec.P521.curve).pub s t) : VG.Arm.Taint.Agree τ₀ s t := by
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

theorem ct : ConstantTime isa (compressContract Spec.P521.curve).pre (compressContract Spec.P521.curve).pub code :=
  VG.Taint.constantTime_of_exists (A := taintS) τ₀ (fun _ _ _ _ h => agree_τ₀ h)
    (by taint_decide_sum [mulPSum, addPSum, subPSum])

theorem ctU : ConstantTime isa (compressContract Spec.P521.curve).pre (compressContract Spec.P521.curve).pub codeU :=
  VG.Taint.constantTime (A := taintU) τ₀ (fun _ _ _ _ h => agree_τ₀ h) (by taint_decide)

theorem sat : ∃ s, (Spec.EcKey.P521.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P521.curve.len = 66 := rfl
  sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, satState] [satState] using (satState 66)

theorem verified : Verified target code (Spec.EcKey.P521.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct p521 p521_ok) ct (compress_implies Spec.EcKey.P521.inst sat)

theorem verifiedU : Verified target codeU (Spec.EcKey.P521.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct (p521With true) p521u_ok) ctU (compress_implies Spec.EcKey.P521.inst sat)

end VG.Proof.EcKey.Compressed.Arm.P521
