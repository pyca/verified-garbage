module

public import VerifiedGarbage.Proof.Ecdh.Arm.Main
public import VerifiedGarbage.Proof.Ecdh.Arm.P224.Contract
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Umaal
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
public import VerifiedGarbage.Impl.Ecdh.P224.Arm
public import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdh.Arm.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Ecdh.Arm.Main
meta import VerifiedGarbage.Proof.Ecdh.Arm.P224.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
meta import VerifiedGarbage.Impl.Ecdh.P224.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdh.Arm.P224.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDH over P-224 on 32-bit ARM: `Verified`

`exchange_ok` for P-224 (`p224_ok`, and `Law` for its group law, which the
registration file supplies: `Proof.P224.law`) gives the contract's
postcondition; `r4`–`r11` and `lr` are restored and `sp` kept. Constant time
by taint tracking from the arguments' registers, as for the public key
(`Proof/EcKey/Arm/Verified.lean`): the only branches are on loop counters,
and every address is `r12` (`scratch`), `lr` (`out`) or `r2` (`peer`) plus a
constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.P224

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Ecdh.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P224 Spec.Weierstrass

theorem pre_of {u : Bool} {s : State} (h : ecdhArm.pre s) : EPre (p224With u) s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem post_of {u : Bool} {s s' : State} (h : EPost (p224With u) s s') : ecdhArm.post s s' := by
  unfold EPost at h
  show match ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) with
    | some z => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 28 = z
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 28 = List.replicate 28 0
  rw [BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) = q
  rw [show Spec.Ecdh.exchange (p224With u).C (dk (p224With u) s)
      (Spec.Ecdsa.bytesAt s.mem (ptr s .r2) (1 + 2 * (p224With u).C.len)) =
        ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_arm (hL : Weierstrass.Law Spec.P224.curve) (u : Bool) (s : State) (hs : ecdhArm.pre s) :
    ∃ t s', Exec isa (exchangeP224With u) s t s' ∧ abiPreserved s s' ∧ ecdhArm.post s s' := by
  have hp := pre_of (u := u) hs
  obtain ⟨t, s', he, K, hpost⟩ := exchange_ok (p224With_ok u) hL hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, K.sp⟩, post_of hpost⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.saved (.r4, 0) (by decide)
  · exact K.saved (.r5, 4) (by decide)
  · exact K.saved (.r6, 8) (by decide)
  · exact K.saved (.r7, 12) (by decide)
  · exact K.saved (.r8, 16) (by decide)
  · exact K.saved (.r9, 20) (by decide)
  · exact K.saved (.r10, 24) (by decide)
  · exact K.saved (.r11, 28) (by decide)
  · exact K.saved (.lr, 32) (by decide)

/-- The taint analysis starts with the arguments' registers public. -/
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (h : ecdhArm.pub s t) : VG.Arm.Taint.Agree τ₀ s t := by
  obtain ⟨_, h0, h1, h2, h3⟩ := h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩,
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
      fun _ h => (List.not_mem_nil h).elim⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem ecdh_ct : ConstantTime isa ecdhArm.pre ecdhArm.pub exchangeP224 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ _ _ h => agree_τ₀ h) (by native_taint_decide)

theorem ecdhU_ct : ConstantTime isa ecdhArm.pre ecdhArm.pub exchangeP224U :=
  VG.Taint.constantTime (A := taintU) τ₀ (fun _ _ _ _ h => agree_τ₀ h) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 28⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x1000, 28⟩, ⟨0x8000, 8192⟩]

theorem ecdhWith_verified (hL : Weierstrass.Law Spec.P224.curve) (u : Bool)
    (hct : ConstantTime isa ecdhArm.pre ecdhArm.pub (exchangeP224With u)) :
    Verified Arm.target (exchangeP224With u) (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst Arm.abi) :=
  Verified.of_correct (ecdh_arm hL u) hct
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [ecdhArm, ex, Spec.P224.curve, Arm.State.addr] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState }

theorem ecdh_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target exchangeP224 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst Arm.abi) :=
  ecdhWith_verified hL false ecdh_ct

theorem ecdhU_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target exchangeP224U (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst Arm.abi) :=
  ecdhWith_verified hL true ecdhU_ct

end VG.Proof.Ecdh.Arm.P224
