module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Main
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.Ecdsa.P192.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P192

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P192

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.compress p192

materialize_shared baseline := code

def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

theorem ct : ConstantTime isa (compressContract Spec.P192.curve).pre (compressContract Spec.P192.curve).pub code := by
  refine VG.Taint.constantTime (A := taint) τ₀ ?_ (by taint_decide)
  intro s t _ _ ⟨_, h0, h1, h2⟩
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

theorem sat : ∃ s, (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P192.curve.len = 24 := rfl
  sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, satState] [satState] using (satState 24)

theorem verified : Verified target code (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct p192 p192_ok) ct (compress_implies _ sat)

end VG.Proof.EcKey.Compressed.Arm.P192
