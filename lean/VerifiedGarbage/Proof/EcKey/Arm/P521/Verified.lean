module

public import VerifiedGarbage.Proof.EcKey.Arm.Main
public import VerifiedGarbage.Proof.EcKey.Arm.P521.Contract
import VerifiedGarbage.Proof.EcKey.Arm.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Umaal
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Impl.EcKey.P521.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.EcKey.Arm.Main
meta import VerifiedGarbage.Proof.EcKey.Arm.P521.Contract
meta import VerifiedGarbage.Proof.EcKey.Arm.P521.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Impl.EcKey.P521.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.EcKey.P521
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono

/-!
# P-521 public keys on 32-bit ARM: `Verified`

`publicKey_ok` for P-521 (`p521_ok`, and `Law` for its group law, which the
registration file supplies) gives the contract's postcondition; `r4`–`r11`
and `lr` are restored and `sp` kept. Constant time by taint tracking from
the arguments' registers: the only branches are on loop counters, and every
address is `r12` (`scratch`) or `lr` (`out`) plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P521

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P521 Spec.Weierstrass

theorem pre_of {u : Bool} {s : State} (h : pkArm.pre s) : PkPre (p521With u) s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem post_of {u : Bool} {s s' : State} (h : PkPost (p521With u) s s') : pkArm.post s s' := by
  unfold PkPost at h
  show match pk s.mem (State.addr (s.gpr .r1)) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 133 = Spec.EcKey.encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 133 = List.replicate 133 0
  rw [BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : pk s.mem (State.addr (s.gpr .r1)) = q
  rw [show Spec.EcKey.publicKey (p521With u).C (dk (p521With u) s) = pk s.mem (State.addr (s.gpr .r1)) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_arm (hL : Weierstrass.Law Spec.P521.curve) (u : Bool) (s : State) (hs : pkArm.pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Arm.publicKeyP521With u) s t s' ∧ abiPreserved s s' ∧ pkArm.post s s' := by
  have hp := pre_of (u := u) hs
  obtain ⟨t, s', he, K, hpost⟩ := publicKey_ok (p521With_ok u) hL hp
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
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false }

/-- The taint analysis's start agrees in the two states. -/
theorem agree_τ₀ {s t : State} (h : pkArm.pub s t) : VG.Arm.Taint.Agree τ₀ s t := by
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

theorem pk_ct : ConstantTime isa pkArm.pre pkArm.pub Impl.EcKey.Arm.publicKeyP521 :=
  VG.Taint.constantTime_of_exists (A := taintS) τ₀ (fun _ _ _ _ h => agree_τ₀ h)
    (by taint_decide_sum [mulPSum, mulSum])

theorem pkU_ct : ConstantTime isa pkArm.pre pkArm.pub Impl.EcKey.Arm.publicKeyP521U :=
  VG.Taint.constantTime (A := taintU) τ₀ (fun _ _ _ _ h => agree_τ₀ h) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 66⟩]
  wr := [⟨0x1000, 133⟩, ⟨0x8000, 8192⟩]

theorem pkWith_verified (hL : Weierstrass.Law Spec.P521.curve) (u : Bool)
    (hct : ConstantTime isa pkArm.pre pkArm.pub (Impl.EcKey.Arm.publicKeyP521With u)) :
    Verified Arm.target (Impl.EcKey.Arm.publicKeyP521With u) (Spec.EcKey.P521.inst.publicKeyContract Arm.abi) :=
  Verified.of_correct (pk_arm hL u) hct
    { pre := by
        sig_implies_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, pkArm, pk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, pkArm, pk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [pkArm, pk, Spec.P521.curve, Arm.State.addr] at h
        revert h
        generalize Spec.EcKey.publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, pkArm, pk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, pkArm, pk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState }

theorem pk_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target Impl.EcKey.Arm.publicKeyP521 (Spec.EcKey.P521.inst.publicKeyContract Arm.abi) :=
  pkWith_verified hL false pk_ct

theorem pkU_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target Impl.EcKey.Arm.publicKeyP521U (Spec.EcKey.P521.inst.publicKeyContract Arm.abi) :=
  pkWith_verified hL true pkU_ct

end VG.Proof.EcKey.Arm.P521
