import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P521.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Impl.Ecdsa.Verify.P521.Arm

/-!
# ECDSA verification over P-521 on 32-bit ARM: `Verified`

`verify_ok` for P-521 (`p521_ok`, and `Law` for its group law, which the
registration file supplies: `Proof.P521.law`) gives the contract's
postcondition; `r4`–`r11` and `lr` are restored and `sp` kept. Constant time
by taint tracking from the arguments' registers, as for ECDH
(`Proof/Ecdh/Arm/Verified.lean`): the only branches are on loop counters,
and every address is `r12` (`scratch`) or a pointer argument plus a
constant or a counter.
-/

namespace VG.Proof.Ecdsa.Verify.Arm.P521

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Ecdsa.Verify.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P521 Spec.Weierstrass

theorem pre_of {s : State} (h : verifyArm.pre s) : VPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : VPost p521 s s') : verifyArm.post s s' := by
  show BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = _
  rw [BitVec.setWidth_append_eq_right]
  exact h

theorem verify_arm (hL : Weierstrass.Law Spec.P521.curve) (s : State) (hs : verifyArm.pre s) :
    ∃ t s', Exec isa verifyP521 s t s' ∧ abiPreserved s s' ∧ verifyArm.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := verify_ok p521_ok hL hp
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

theorem verify_ct : ConstantTime isa verifyArm.pre verifyArm.pub verifyP521 := by
  refine VG.Taint.constantTime (A := taint) τ₀ ?_ (by taint_decide)
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
  rd := [⟨0x1000, 133⟩, ⟨0x2000, 66⟩, ⟨0x3000, 132⟩]
  wr := [⟨0x8000, 8192⟩]

theorem verify_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified Arm.target verifyP521 (Spec.Ecdsa.P521.inst.verifyContract Arm.abi) :=
  Verified.of_correct (verify_arm hL) verify_ct
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyArm, vf, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyArm, vf, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        exact h
      pub := by
        sig_implies_pub [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyArm, vf, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract,
          Spec.Ecdsa.Instance.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, verifyArm, vf, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState }

end VG.Proof.Ecdsa.Verify.Arm.P521
