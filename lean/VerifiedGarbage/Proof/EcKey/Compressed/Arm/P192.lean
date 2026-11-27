module

import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Main
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.Ecdsa.P192.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Impl.Ecdsa.P192.Arm
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.TCB.Arm.Target

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P192

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P192

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.compress p192

materialize_shared baseline := code

/-- The function with `umaal`. -/
abbrev codeU : Prog isa := Impl.EcKey.Compressed.Arm.compress (p192With true)

materialize_shared umaal := codeU

def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (h : (compressContract Spec.P192.curve).pub s t) : VG.Arm.Taint.Agree τ₀ s t := by
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
abbrev compressAC (u : Bool) : Contract isa :=
  (compressContract Spec.P192.curve).withTablesArm (p192With u).constsK

/-- The taint analysis's start, and the table's address, agree in the two states. -/
theorem agreeC {u : Bool} {s t : State} (h : (compressAC u).pub s t) :
    VG.Arm.Taint.Agree τ₀ s t ∧ ∀ n ∈ [(p192With u).constSym], s.syms n = t.syms n :=
  ⟨agree_τ₀ h.1, fun n hn => by
    obtain rfl := List.mem_singleton.mp hn; exact h.2 _ (List.mem_singleton_self _)⟩

theorem ct : ConstantTime isa (compressAC false).pre (compressAC false).pub code :=
  VG.Taint.constantTime (A := taintSym [(p192With false).constSym]) τ₀ (fun _ _ _ _ h => agreeC h)
    (by taint_decide)

theorem ctU : ConstantTime isa (compressAC true).pre (compressAC true).pub codeU :=
  VG.Taint.constantTime (A := taintSymU [(p192With true).constSym]) τ₀ (fun _ _ _ _ h => agreeC h)
    (by taint_decide)

theorem sat : ∃ s, (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P192.curve.len = 24 := rfl
  sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, satState] [satState] using (satState 24)

/-- A state satisfying the precondition with the table, at `0x100000`. -/
def satStateC (u : Bool) : State := { satState 24 with
  mem := constMem 0x100000 (p192With u).constTbl
  rd := (satState 24).rd ++ [⟨0x100000, 8 * (17 * 3)⟩]
  syms := fun _ => 0x100000 }

theorem satC (u : Bool) :
    ∃ s, (Spec.EcKey.P192.inst.compressPublicKeyContract (abi.withConsts (p192With u).constsK) 0).pre s := by
  refine ⟨satStateC u, ?_⟩
  have hlen : Spec.P192.curve.len = 24 := rfl
  have hl := constTbl_length (p192With u)
  have held := constMem_held 0x100000 (p192With u).constTbl (by rw [hl]; cases u <;> decide)
  obtain ⟨W, eW⟩ : ∃ W, (p192With u).constTbl = W := ⟨_, rfl⟩
  have hk : (p192With u).constsK = [((p192With u).constSym, W)] := by rw [← eW]; rfl
  rw [hk]
  rw [eW] at hl held
  generalize e : satStateC u = s
  sig_pre [Spec.EcKey.P192.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords, abi, argRegs, reduceClassify,
    Loc.val, State.addr, Abi.withConsts, Abi.constRegions_cons, Abi.constRegions_nil, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨by cases u <;> decide, by cases u <;> decide, fun i hi => ?_, by cases u <;> decide, ?_, by cases u <;> decide, by cases u <;> decide, ?_⟩
  · show (constMem 0x100000 (p192With u).constTbl).readW _ 64 = _
    rw [eW]; exact held i (by rw [hl]; exact hi)
  · intro r hr
    change r ∈ [⟨0x1000, 24 + 1⟩, ⟨0x8000, 8192⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by cases u <;> decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by cases u <;> decide) | (cases u <;> decide)

theorem verified :
    Verified target code (Spec.EcKey.P192.inst.compressPublicKeyContract (abi.withConsts (p192With false).constsK) 0) :=
  Verified.of_correct (compress_correct p192 p192_ok (List.mem_singleton_self _)) ct
    (withTables_implies (compress_implies _ sat) (satC false))

theorem verifiedU :
    Verified target codeU (Spec.EcKey.P192.inst.compressPublicKeyContract (abi.withConsts (p192With true).constsK) 0) :=
  Verified.of_correct (compress_correct (p192With true) p192u_ok (List.mem_singleton_self _)) ctU
    (withTables_implies (compress_implies _ sat) (satC true))

end VG.Proof.EcKey.Compressed.Arm.P192
