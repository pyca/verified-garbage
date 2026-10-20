module

import VerifiedGarbage.Proof.Seed.AArch64.ModeCore
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Seed.AArch64.Lit
public import VerifiedGarbage.Proof.Seed.SboxLit
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# SEED's core for the modes on AArch64: the return address across the call

The core's `crypt` calls the ECB code, which overwrites the return address
(`x30`): `crypt` keeps it in `v28`, which no instruction of the callee
writes, and moves it back (`crypt_keeps_x30`). `keeps_x30` proves that a
mode's code keeps `x30`, `crypt` being the only code with a call.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.Impl.Seed.AArch64
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Modes.AArch64 (KeepsReg addImm_ok movz_ok runBlock_app dup_ok umov_ok extract_ofVDwords
  keepsV_of_vSafe)
open VG.Spec.Seed (Direction)

/-- The block's state from `s`, as a function. -/
theorem block_det {is : List Instr} {s s₁ s' : State} {t : List Leak} (h : Exec isa (.block is) s t s')
    (e : runBlock isa is s = some s₁) : s' = s₁ := by
  have w : WP isa (.block is) s fun x => x = s₁ := WP.of_runBlock ⟨s₁, e, rfl⟩
  obtain ⟨t', s'', he, rfl⟩ := w
  exact (Exec.det h he).2

theorem crypt_keeps_x30_aux (d : Direction) {s s₁ s₂ s' : State} {t₁ t₂ t₃ : List Leak}
    (hA : Exec isa (.block cryptHead) s t₁ s₁) (hC : Exec isa (blockCall d) s₁ t₂ s₂)
    (hB : Exec isa (.block cryptTail) s₂ t₃ s') : s'.gpr .x30 = s.gpr .x30 := by
  -- `v28` after the head.
  have v28₁ : s₁.v .v28 = ofVDwords (s.gpr .x30) (s.gpr .x30) := by
    have w : WP isa (.block ([.vop (.dup .d2 .v28 .x30)] ++ cryptHead.tail)) s fun x => x = s₁ := ⟨t₁, s₁, hA, rfl⟩
    obtain ⟨_, u, hu, w⟩ := WP.block_append_iff.mp w
    obtain ⟨t', u', hu', hq⟩ := w
    rw [block_det hu (dup_ok s .v28 .x30)] at hu'
    rw [← hq, Exec.vec (c := .block cryptHead.tail) (by decide) hu', RegUpd.v_setV_self]
  have v28₂ : s₂.v .v28 = s₁.v .v28 := keepsV_of_vSafe (blockCall_vsafe d).1 _ _ _ hC
  have hs' := block_det hB (by
    rw [show cryptTail = [.umov .x sb .v27 0] ++ ([.umov .x .x30 .v28 0] ++ ([.umov .x .x23 .v29 0] ++
      [.umov .x .x24 .v30 0])) from rfl, runBlock_app, umov_ok, Option.bind_some, runBlock_app, umov_ok,
      Option.bind_some, runBlock_app, umov_ok, Option.bind_some, umov_ok])
  subst hs'
  rw [(Modes.AArch64.write_ok _ .x24 _).2.1 .x30 (by decide), (Modes.AArch64.write_ok _ .x23 _).2.1 .x30 (by decide),
    (Modes.AArch64.write_ok _ .x30 _).1]
  show (s₂.v .v28).extractLsb' 0 64 = _
  rw [v28₂, v28₁, extract_ofVDwords]

theorem crypt_keeps_x30 (d : Direction) : KeepsReg .x30 (dirCore d).crypt := by
  intro s t s' h
  cases h with
  | seq hA hR =>
    cases hR with
    | seq hC hB => exact crypt_keeps_x30_aux d hA hC hB

/-- `WP.gprs` for `x30`, from `KeepsReg` rather than the absence of calls. -/
theorem WP.gprs' {c : Prog isa} {s : State} {Q : State → Prop} (hk : KeepsReg .x30 c) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hk _ _ _ he⟩

/-- `KeepsReg .x30` of a mode's code: its structure, down to `crypt` and
blocks that do not write `x30`. -/
tactic_template "keeps_x30" : tactic => `(tactic| repeat (first
  | with_reducible exact crypt_keeps_x30 _
  | apply KeepsReg.seq
  | apply KeepsReg.ite
  | apply KeepsReg.loop
  | exact Modes.AArch64.keepsReg_of_regSafe (by decide)))

theorem cbcEncryptChained_keeps_x30 : KeepsReg .x30 cbcEncryptChained := by keeps_x30
theorem cbcDecryptChained_keeps_x30 : KeepsReg .x30 cbcDecryptChained := by keeps_x30
theorem ofb_keeps_x30 : KeepsReg .x30 ofb := by keeps_x30
theorem cfbEncrypt_keeps_x30 : KeepsReg .x30 cfbEncrypt := by keeps_x30
theorem cfbDecrypt_keeps_x30 : KeepsReg .x30 cfbDecrypt := by keeps_x30

end VG.Proof.Seed.AArch64
