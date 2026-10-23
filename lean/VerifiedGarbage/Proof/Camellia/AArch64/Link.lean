module

public import VerifiedGarbage.Proof.Camellia.AArch64.ModeCore
import VerifiedGarbage.Proof.Camellia.AArch64.Serial.ModeCore
meta import VerifiedGarbage.Proof.Camellia.AArch64.Serial.ModeCore
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Modes.AArch64.Steps
public import VerifiedGarbage.Impl.Camellia.AArch64.Cbc
public import VerifiedGarbage.Impl.Camellia.AArch64.Fb

/-!
# Camellia's core for the modes on AArch64: the return address across the calls

The core's `prepare` and `crypt` call `vg_camellia_prepare_keys`
and `vg_camellia_crypt_prepared`, which overwrite the return address (`x30`): each
keeps it in `v28`, which no instruction of the callees writes, and moves it
back (`prepare_keeps_x30`, `crypt_keeps_x30`). `camellia_keeps_x30` proves that
a mode's code keeps `x30`, the core's code being the only code with calls.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Proof.Modes.AArch64 (KeepsReg runBlock_app dup_ok umov_ok extract_ofVDwords vSafe keepsV_of_vSafe)

/-- The block's state from `s`, as a function. -/
theorem block_det {is : List Instr} {s s₁ s' : State} {t : List Leak} (h : Exec isa (.block is) s t s')
    (e : runBlock isa is s = some s₁) : s' = s₁ := by
  have w : WP isa (.block is) s fun x => x = s₁ := WP.of_runBlock ⟨s₁, e, rfl⟩
  obtain ⟨t', s'', he, rfl⟩ := w
  exact (Exec.det h he).2

theorem call_keeps_x30 {r : Reg} {args : List Instr} {name : String} {c : Prog isa}
    (hargs : ∀ i ∈ (keepHeadWith r).tail ++ args, vdstOf i ≠ some .v28) (hc : vSafe .v28 c = true)
    {s s₁ s₂ s' : State} {t₁ t₂ t₃ : List Leak}
    (hA : Exec isa (.block (keepHeadWith r ++ args)) s t₁ s₁) (hC : Exec isa (.call name c) s₁ t₂ s₂)
    (hB : Exec isa (.block keepTail) s₂ t₃ s') : s'.gpr .x30 = s.gpr .x30 := by
  have v28₁ : s₁.v .v28 = ofVDwords (s.gpr .x30) (s.gpr .x30) := by
    have w : WP isa (.block ([.vop (.dup .d2 .v28 .x30)] ++ ((keepHeadWith r).tail ++ args))) s fun x => x = s₁ :=
      ⟨t₁, s₁, hA, rfl⟩
    obtain ⟨_, u, hu, w⟩ := WP.block_append_iff.mp w
    obtain ⟨t', u', hu', hq⟩ := w
    rw [block_det hu (dup_ok s .v28 .x30)] at hu'
    rw [← hq, Exec.vec (c := .block ((keepHeadWith r).tail ++ args)) hargs hu', RegUpd.v_setV_self]
  have v28₂ : s₂.v .v28 = s₁.v .v28 := keepsV_of_vSafe (c := .call name c) hc _ _ _ hC
  obtain ⟨s'', e'', -, r28, -⟩ := keepTail_ok s₂
  rw [block_det hB e'', r28, v28₂, v28₁, extract_ofVDwords]

theorem vsafe28 {c : Prog isa} (h : keepsVs c = true) : vSafe .v28 c = true := by
  simp only [keepsVs, Bool.and_eq_true] at h
  exact h.1.1.2

theorem prepare_keeps_x30 (d : Dir) : KeepsReg .x30 (dirCore d).prepare := by
  intro s t s' h
  cases h with
  | seq hA hR =>
    cases hR with
    | seq hC hB => exact call_keeps_x30 (by cases d <;> decide) (vsafe28 prepareKeys_vsafe) hA hC hB

theorem crypt_keeps_x30 (d : Dir) : KeepsReg .x30 (dirCore d).crypt := by
  intro s t s' h
  cases h with
  | seq hA hR =>
    cases hR with
    | seq hC hB => exact call_keeps_x30 (r := .x4) (by decide) (vsafe28 cryptPrepared_vsafe) hA hC hB

/-- `WP.gprs` for `x30`, from `KeepsReg` rather than the absence of calls. -/
theorem WP.gprs' {c : Prog isa} {s : State} {Q : State → Prop} (hk : KeepsReg .x30 c) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hk _ _ _ he⟩

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem modeAbi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-- `KeepsReg .x30` of a mode's code: its structure, down to the core's code
and blocks that do not write `x30`. -/
tactic_template "camellia_keeps_x30" : tactic => `(tactic| repeat (first
  | with_reducible exact Serial.keeps_x30.1
  | with_reducible exact Serial.keeps_x30.2
  | with_reducible exact crypt_keeps_x30 _
  | with_reducible exact prepare_keeps_x30 _
  | apply KeepsReg.seq
  | apply KeepsReg.ite
  | apply KeepsReg.loop
  | exact Modes.AArch64.keepsReg_of_regSafe (by decide)))

theorem ctr_keeps_x30 : KeepsReg .x30 ctr := by camellia_keeps_x30
theorem cbcEncryptChained_keeps_x30 : KeepsReg .x30 cbcEncryptChained := by camellia_keeps_x30
theorem cbcDecryptChained_keeps_x30 : KeepsReg .x30 cbcDecryptChained := by camellia_keeps_x30
theorem ofb_keeps_x30 : KeepsReg .x30 ofb := by camellia_keeps_x30
theorem cfbEncrypt_keeps_x30 : KeepsReg .x30 cfbEncrypt := by camellia_keeps_x30
theorem cfbDecrypt_keeps_x30 : KeepsReg .x30 cfbDecrypt := by camellia_keeps_x30

end VG.Proof.Camellia.AArch64
