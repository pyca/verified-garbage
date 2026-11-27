module

import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Umaal
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Main
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.Ecdsa.P384.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.Ecdsa.P384.Arm
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.TCB.Arm.Target

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P384

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P384

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.compress p384

materialize_shared baseline := code

/-- The function with `umaal`. -/
abbrev codeU : Prog isa := Impl.EcKey.Compressed.Arm.compress (p384With true)

materialize_shared umaal := codeU

def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

theorem agree_τ₀ {s t : State} (h : (compressContract Spec.P384.curve).pub s t) : VG.Arm.Taint.Agree τ₀ s t := by
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
abbrev AC (u : Bool) : Contract isa := (compressContract Spec.P384.curve).withTablesArm (p384With u).constsK

theorem ct : ConstantTime isa (AC false).pre (AC false).pub code :=
  VG.Taint.constantTime (A := taintSym [(p384With false).constSym]) τ₀
    (fun _ _ _ _ h => ⟨agree_τ₀ h.1, withTablesArm_syms h⟩) (by taint_decide)

theorem ctU : ConstantTime isa (AC true).pre (AC true).pub codeU :=
  VG.Taint.constantTime (A := taintSymU [(p384With true).constSym]) τ₀
    (fun _ _ _ _ h => ⟨agree_τ₀ h.1, withTablesArm_syms h⟩) (by taint_decide)

theorem sat : ∃ s, (Spec.EcKey.P384.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P384.curve.len = 48 := rfl
  sig_implies_sat [Spec.EcKey.P384.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, satState] [satState] using (satState 48)

/-- `satState`, holding the table at `0x100000`. -/
def satStateC (u : Bool) : State := { satState 48 with
  mem := constMem ((0x100000 : BitVec 32).setWidth 64) (p384With u).constTbl
  syms := fun _ => 0x100000 }

theorem satC (u : Bool) :
    ∃ s, (Spec.EcKey.P384.inst.compressPublicKeyContract (abi.withConsts (p384With u).constsK) 0).pre s :=
  sat_consts (s := satStateC u)
    (by
      have hlen : Spec.P384.curve.len = 48 := rfl
      cases u <;>
      (sig_pre [Spec.EcKey.P384.inst, Spec.EcKey.Instance.compressPublicKeyContract,
        Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
        abi, argRegs, reduceClassify, Loc.val, State.addr, satState, satStateC]
       sig_and_intros
       all_goals first
         | rfl
         | decide
         | exact Region.disjoint_of_sep (by decide)))
    (constsOk_tbl _ (T := 0x100000) rfl rfl (by cases u <;> decide) (by decide) (by cases u <;> decide)
      (by cases u <;> decide))

theorem verified :
    Verified target code (Spec.EcKey.P384.inst.compressPublicKeyContract (abi.withConsts (p384With false).constsK) 0) :=
  Verified.of_correct (compress_correct p384 p384_ok (List.mem_singleton_self _)) ct
    (withTables_implies (compress_implies _ sat) (satC false))

theorem verifiedU :
    Verified target codeU (Spec.EcKey.P384.inst.compressPublicKeyContract (abi.withConsts (p384With true).constsK) 0) :=
  Verified.of_correct (compress_correct (p384With true) p384u_ok (List.mem_singleton_self _)) ctU
    (withTables_implies (compress_implies _ sat) (satC true))

end VG.Proof.EcKey.Compressed.Arm.P384
