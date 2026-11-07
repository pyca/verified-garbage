module

public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.Arm.OpenTo.Fn
public import VerifiedGarbage.Proof.AesGcm.Arm.Frame
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.AesGcm.Arm.OpenTo.CT
import VerifiedGarbage.Proof.AesGcm.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES-GCM decryption out of place, by a copy, ARMv7: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_open_to`, with the 2648 bytes of stack below the stack pointer
that its frame and its call use (`Proof.AesGcm.openToRoundsContract`),
implies the one the proof is written against (`toK`, `to_implies`), and so
the code, calling `vg_aes_gcm_open` by its shared contract (`openFn`), is
`Verified` against it (`openTo_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.OpenTo

open VG VG.Arm VG.Arm.FrameStack VG.Impl.AesGcm.Arm.OpenTo

theorem openTo_correct (F : OpenFn) (s : State) (hs : toK.pre s) :
    ∃ t s', Exec isa (openTo F.name F.code) s t s' ∧ abiPreserved s s' ∧ toK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := openTo_wp F hs
  exact ⟨t, s', he, ha, hp⟩

theorem toPre_of_spec {s : State} (h : (Proof.AesGcm.openToRoundsContract Arm.abi 2648).pre s) : ToPre s := by
  sig_pre [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq] at h
  sig_split h
  rename_i w₁ w₂ rd wr kd nd ad sd dt da bk bn ba bs bd bt barg ok on oa os od ot hR
  rw [h] at wr kd nd ad sd dt da bd od
  exact ⟨w₁, w₂, rd, wr, kd, nd, ad, sd, dt, da, bk, bn, ba, bs, bd, bt, barg, ok, on, oa, os, od, ot, hR⟩

theorem toPost_of {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToRoundsContract Arm.abi 2648).post s s' := by
  sig_post [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Proof.AesGcm.openToRoundsPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  intro _
  have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
  rw [e]
  exact h

theorem toPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.openToRoundsContract Arm.abi 2648).pub s₁ s₂) :
    toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToLeak, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq] at hp
  obtain ⟨qsp, ql, q0, q1, q2, q3, a0, a1, a2, a3, a4, a5, a6, a7⟩ := hp
  refine ⟨qsp, ql, q0, q1, q2, q3, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4, a5, a6, a7]

/-- A state satisfying the precondition of `vg_aes_gcm_open_to`: no nonce,
additional data, text or tag; its eight words of stack arguments at
`0x8000`. -/
def toSat : State :=
  Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 32⟩] [⟨0, 0⟩]

theorem toSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract Arm.abi 2648).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [toSat, Proof.AesGcm.Arm.mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using toSat

theorem to_implies : toK.Implies (Proof.AesGcm.openToRoundsContract Arm.abi 2648) :=
  ⟨fun _ h => toPre_of_spec h, fun _ _ _ h => toPost_of h, fun _ _ _ _ h => toPub_of h, toSat_pre⟩

theorem openTo_verified (F : OpenFn) :
    Verified Arm.target (openTo F.name F.code) (Proof.AesGcm.openToRoundsContract Arm.abi 2648) :=
  Verified.of_correct (k := toK) (openTo_correct F) (openTo_ct F) to_implies

open VG.Impl.AesGcm.Arm in
/-- The frames of `vg_aes_gcm_open`, with its working space, use at most the
2600 bytes of stack its contract gives it. -/
theorem open_stack : armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») ≤ 2600 := by
  decide +kernel

/-- `vg_aes_gcm_open`, by its shared contract. -/
def openFn : OpenFn :=
  ⟨Spec.Gcm.openApi.name, Impl.StackScratch.Arm.withStackScratch 2592 6 Impl.AesGcm.Arm.«open», open_framed,
    open_stack⟩

end VG.Proof.AesGcm.Arm.OpenTo
