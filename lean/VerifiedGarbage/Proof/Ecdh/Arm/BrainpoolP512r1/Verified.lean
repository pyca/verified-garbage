module

public import VerifiedGarbage.Proof.Ecdh.Arm.Main
public import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP512r1.Contract
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ecdh.Arm.Main
meta import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDH over brainpoolP512r1 on 32-bit ARM: `Verified`

`exchange_ok` for brainpoolP512r1 (`brainpoolp512r1_ok`, and `Law` for its group law, which the
registration file supplies: `Proof.BrainpoolP512r1.law`) gives the contract's
postcondition; `r4`–`r11` and `lr` are restored and `sp` kept. Constant time
by taint tracking from the arguments' registers, as for the public key
(`Proof/EcKey/Arm/Verified.lean`): the only branches are on loop counters,
and every address is `r12` (`scratch`), `lr` (`out`) or `r2` (`peer`) plus a
constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.BrainpoolP512r1

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Ecdh.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP512r1 Spec.Weierstrass

theorem pre_of {s : State} (h : ecdhArm.pre s) : EPre brainpoolp512r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost brainpoolp512r1 s s') : ecdhArm.post s s' := by
  unfold EPost at h
  show match ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) with
    | some z => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 64 = z
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 64 = List.replicate 64 0
  rw [BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) = q
  rw [show Spec.Ecdh.exchange brainpoolp512r1.C (dk brainpoolp512r1 s)
      (Spec.Ecdsa.bytesAt s.mem (ptr s .r2) (1 + 2 * brainpoolp512r1.C.len)) =
        ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_arm (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (s : State) (hs : ecdhArm.pre s) :
    ∃ t s', Exec isa exchangeBrainpoolP512r1 s t s' ∧ abiPreserved s s' ∧ ecdhArm.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := exchange_ok brainpoolp512r1_ok hL hp
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

theorem ecdh_ct : ConstantTime isa ecdhArm.pre ecdhArm.pub exchangeBrainpoolP512r1 := by
  refine VG.Taint.constantTime (A := taint) τ₀ ?_ (by native_taint_decide)
  intro s t _ _ ⟨_, h0, h1, h2, h3⟩
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
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 129⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem ecdh_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target exchangeBrainpoolP512r1 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst Arm.abi) :=
  Verified.of_correct (ecdh_arm hL) ecdh_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [ecdhArm, ex, Spec.BrainpoolP512r1.curve, Arm.State.addr] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP512r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords, ecdhArm, ex, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState }

end VG.Proof.Ecdh.Arm.BrainpoolP512r1
