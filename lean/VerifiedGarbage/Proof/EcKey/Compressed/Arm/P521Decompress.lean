module

import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressMain
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Umaal
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P521.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P521.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.Arm.Target

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P521Decompress

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P521

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.decompress p521

materialize_shared baseline := code

/-- The function with `umaal`. -/
abbrev codeU : Prog isa := Impl.EcKey.Compressed.Arm.decompress (p521With true)

materialize_shared umaal := codeU

def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (h : (decompressContract Spec.P521.curve Impl.EcKey.Compressed.rootThreeModFour).pub s t) : VG.Arm.Taint.Agree τ₀ s t := by
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

/-- The contract with the table of constants (`Cfg.constsK`), as the proof states it. -/
abbrev AC (u : Bool) : Contract isa := (decompressContract Spec.P521.curve Impl.EcKey.Compressed.rootThreeModFour).withTablesArm (p521With u).constsK

theorem ct : ConstantTime isa (AC false).pre (AC false).pub code :=
  VG.Taint.constantTime_of_exists (A := taintC) τ₀ (fun _ _ _ _ h => ⟨agree_τ₀ h.1, withTablesArm_syms h⟩)
    (by taint_decide_sum [mulPSum, addPSum, subPSum])

theorem ctU : ConstantTime isa (AC true).pre (AC true).pub codeU :=
  VG.Taint.constantTime (A := taintSymU [(p521With true).constSym]) τ₀
    (fun _ _ _ _ h => ⟨agree_τ₀ h.1, withTablesArm_syms h⟩) (by taint_decide)

theorem sat : ∃ s, (Spec.EcKey.P521.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P521.curve.len = 66 := rfl
  sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, decompressSatState] [decompressSatState] using (decompressSatState 66)

/-- `decompressSatState`, holding the table at `0x100000`. -/
def satStateC (u : Bool) : State := { decompressSatState 66 with
  mem := constMem ((0x100000 : BitVec 32).setWidth 64) (p521With u).constTbl
  syms := fun _ => 0x100000 }

theorem satC (u : Bool) :
    ∃ s, (Spec.EcKey.P521.inst.decompressPublicKeyContract (abi.withConsts (p521With u).constsK) 0).pre s :=
  sat_consts (s := satStateC u)
    (by
      have hlen : Spec.P521.curve.len = 66 := rfl
      cases u <;>
      (sig_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
        Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
        abi, argRegs, reduceClassify, Loc.val, State.addr, decompressSatState, satStateC]
       sig_and_intros
       all_goals first
         | rfl
         | decide
         | exact Region.disjoint_of_sep (by decide)))
    (constsOk_tbl _ (T := 0x100000) rfl rfl (by cases u <;> decide) (by decide) (by cases u <;> decide)
      (by cases u <;> decide))

theorem verified (hL : Proof.Weierstrass.Law Spec.P521.curve) :
    Verified target code
      (Spec.EcKey.P521.inst.decompressPublicKeyContract (abi.withConsts (p521With false).constsK) 0) :=
  Verified.of_correct (decompress_correctT p521 p521_ok _ (candidateThree_correct p521_ok (by decide +kernel))
      (List.mem_singleton_self _)) ct
    (withTables_implies (decompress_implies Spec.EcKey.P521.inst _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sat) (satC false))

theorem verifiedU (hL : Proof.Weierstrass.Law Spec.P521.curve) :
    Verified target codeU
      (Spec.EcKey.P521.inst.decompressPublicKeyContract (abi.withConsts (p521With true).constsK) 0) :=
  Verified.of_correct (decompress_correctT (p521With true) p521u_ok _
      (candidateThree_correct p521u_ok (by decide +kernel)) (List.mem_singleton_self _)) ctU
    (withTables_implies (decompress_implies Spec.EcKey.P521.inst _
      (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sat) (satC true))

end VG.Proof.EcKey.Compressed.Arm.P521Decompress
