import VerifiedGarbage.Proof.EcKey.Arm.Main
import VerifiedGarbage.Proof.EcKey.Arm.P384.Contract
import VerifiedGarbage.Proof.EcKey.Arm.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
import VerifiedGarbage.Impl.EcKey.P384.Arm

/-!
# P-384 public keys on 32-bit ARM: `Verified`

`publicKey_ok` for P-384 (`p384_ok`, and `Law` for its group law, which the
registration file supplies) gives the contract's postcondition; `r4`–`r11`
and `lr` are restored and `sp` kept. Constant time by taint tracking from
the arguments' registers: the only branches are on loop counters, and every
address is `r12` (`scratch`) or `lr` (`out`) plus a constant or a counter.
-/

namespace VG.Proof.EcKey.Arm.P384

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P384 Spec.Weierstrass

theorem pre_of {s : State} (h : pkArm.pre s) : PkPre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem post_of {s s' : State} (h : PkPost p384 s s') : pkArm.post s s' := by
  unfold PkPost at h
  show match pk s.mem (State.addr (s.gpr .r1)) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 97 = Spec.EcKey.encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) 97 = List.replicate 97 0
  rw [BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : pk s.mem (State.addr (s.gpr .r1)) = q
  rw [show Spec.EcKey.publicKey p384.C (dk p384 s) = pk s.mem (State.addr (s.gpr .r1)) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_arm (hL : Weierstrass.Law Spec.P384.curve) (s : State) (hs : pkArm.pre s) :
    ∃ t s', Exec isa Impl.EcKey.Arm.publicKeyP384 s t s' ∧ abiPreserved s s' ∧ pkArm.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := publicKey_ok p384_ok hL hp
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

theorem pk_ct : ConstantTime isa pkArm.pre pkArm.pub Impl.EcKey.Arm.publicKeyP384 := by
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
  rd := [⟨0x2000, 48⟩]
  wr := [⟨0x1000, 97⟩, ⟨0x8000, 8192⟩]

theorem pk_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target Impl.EcKey.Arm.publicKeyP384 (Spec.EcKey.P384.inst.publicKeyContract Arm.abi) :=
  Verified.of_correct (pk_arm hL) pk_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, pkArm, pk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, pkArm, pk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [pkArm, pk, Spec.P384.curve, Arm.State.addr] at h
        revert h
        generalize Spec.EcKey.publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, pkArm, pk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, pkArm, pk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState }

end VG.Proof.EcKey.Arm.P384
