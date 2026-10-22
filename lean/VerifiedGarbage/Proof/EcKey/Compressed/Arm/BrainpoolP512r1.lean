module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Main
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.BrainpoolP512r1

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP512r1

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.compress brainpoolp512r1

materialize_shared baseline := code

def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

theorem ct : ConstantTime isa (compressContract Spec.BrainpoolP512r1.curve).pre (compressContract Spec.BrainpoolP512r1.curve).pub code := by
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

theorem sat : ∃ s, (Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.BrainpoolP512r1.curve.len = 64 := rfl
  sig_implies_sat [Spec.EcKey.BrainpoolP512r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, satState] [satState] using (satState 64)

theorem verified : Verified target code (Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct brainpoolp512r1 brainpoolp512r1_ok) ct (compress_implies _ sat)

end VG.Proof.EcKey.Compressed.Arm.BrainpoolP512r1
