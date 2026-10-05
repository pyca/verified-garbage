import VerifiedGarbage.Proof.AesOcb.Arm.CTFn
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.AesOcb.Scratch

/-!
# AES-OCB on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`), with 8 bytes of stack: each call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` pushes two words.
`Frame.lean` allocates the working space.
-/

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Impl.AesOcb.Arm

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte
nonce, no associated data, no data, a 4-byte tag at `0x3000` and `work` at
0. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8014 then 4 else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 28⟩], wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesOcb.sealScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, sealArm, sealPre, oneLay, onePub, bel, arg, args, roundsOk, ciph, lstar, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesOcb.openScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, openArm, openPre, oneLay, onePub, openLeak, bel, arg, args, roundsOk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, openRes, ciph, inv, lstar, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, openArm, openPre, oneLay, onePub, openLeak, openRes, ciph, inv, lstar, bel, arg, args,
          roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
        · exact a6
      sat := by
        sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, openArm, openPre, oneLay, onePub, openLeak, bel, arg, args, roundsOk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesOcb.Arm
