module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressMain
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P521.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P521Decompress

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P521

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.decompress p521

materialize_shared baseline := code

def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

theorem ct : ConstantTime isa (decompressContract Spec.P521.curve Impl.EcKey.Compressed.rootThreeModFour).pre (decompressContract Spec.P521.curve Impl.EcKey.Compressed.rootThreeModFour).pub code := by
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

theorem sat : ∃ s, (Spec.EcKey.P521.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P521.curve.len = 66 := rfl
  sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, decompressSatState] [decompressSatState] using (decompressSatState 66)

theorem verified (hL : Proof.Weierstrass.Law Spec.P521.curve) :
    Verified target code (Spec.EcKey.P521.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct p521 p521_ok _ (candidateThree_correct p521_ok (by decide +kernel))) ct
    (decompress_implies Spec.EcKey.P521.inst _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sat)

end VG.Proof.EcKey.Compressed.Arm.P521Decompress
