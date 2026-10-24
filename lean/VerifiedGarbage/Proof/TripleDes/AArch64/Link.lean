module

public import VerifiedGarbage.Proof.Framework.TacticTemplate

import VerifiedGarbage.Proof.TripleDes.AArch64.ModeCore
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit

/-!
# Triple DES's core for the modes on AArch64: the registers across the call

The core's `crypt` calls the block function, which overwrites the return
address (`x30`): `crypt` keeps it in `x26`, which the call keeps (it is
callee-saved), and moves it back (`crypt_keeps_x30`). `crypt_keeps_x25`: the
call keeps `x25`, where the feedback modes keep the IV's address. With
`KeepsReg.seq`, `.ite` and `.loop`, `keeps_x30` proves that a mode's code
keeps `x30`, `crypt` being the only code with a call.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Proof.Modes.AArch64 (KeepsReg addImm_ok runBlock_app)
open VG.Spec.TripleDes (Direction)

/-- `crypt` before the call: the arguments, and the return address to `x26`. -/
def cryptHead : List Instr :=
  [.addImm .x .x0 sb (8 * schedSlot), .addImm .x .x1 sb (8 * cbcBuf), .addImm .x .x2 sb 0, .addImm .x .x26 .x30 0]

/-- `crypt` after the call: `sb` and the return address back. -/
def cryptTail : List Instr := [.addImm .x sb .x2 0, .addImm .x .x30 .x26 0]

theorem crypt_eq (d : Direction) :
    (dirCore d).crypt = .seq (.block cryptHead) (.seq (blockCall d) (.block cryptTail)) := by
  cases d <;> rfl

/-- No instruction of the block function writes `r`. -/
theorem dirBlock_keeps {r : Reg} (hr : r = .x25 ∨ r = .x26) (d : Direction) :
    ∀ i ∈ instrs (dirBlock d), clobbers i r = false := by
  have h : ((instrs (dirBlock d)).all fun i => decide (clobbers i .x25 = false) && decide (clobbers i .x26 = false)) =
      true := by
    cases d
    · change ((instrs encryptBlock).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
    · change ((instrs decryptBlock).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rcases hr with rfl | rfl
  · exact this.1
  · exact this.2

theorem blockCall_keeps {r : Reg} (hr : r = .x25 ∨ r = .x26) (d : Direction) : KeepsReg r (blockCall d) := by
  intro s t s' h
  have hl : r ∉ linkRegs := by rcases hr with rfl | rfl <;> decide
  refine Exec.gpr (fun i hi => ?_) h (.inr hl)
  rw [blockCall_eq] at hi
  exact dirBlock_keeps hr d i (by cases d <;> exact hi)

theorem crypt_keeps_x25 (d : Direction) : KeepsReg .x25 (dirCore d).crypt := by
  rw [crypt_eq]
  exact KeepsReg.seq (Modes.AArch64.keepsReg_of_regSafe (by decide))
    (KeepsReg.seq (blockCall_keeps (.inl rfl) d) (Modes.AArch64.keepsReg_of_regSafe (by decide)))

/-- The block's state from `s`, as a function. -/
theorem block_det {is : List Instr} {s s₁ s' : State} {t : List Leak} (h : Exec isa (.block is) s t s')
    (e : runBlock isa is s = some s₁) : s' = s₁ := by
  have w : WP isa (.block is) s fun x => x = s₁ := WP.of_runBlock ⟨s₁, e, rfl⟩
  obtain ⟨t', s'', he, rfl⟩ := w
  exact (Exec.det h he).2

theorem crypt_keeps_x30_aux (d : Direction) {s s₁ s₂ s' : State} {t₁ t₂ t₃ : List Leak}
    (hA : Exec isa (.block cryptHead) s t₁ s₁) (hC : Exec isa (blockCall d) s₁ t₂ s₂)
    (hB : Exec isa (.block cryptTail) s₂ t₃ s') : s'.gpr .x30 = s.gpr .x30 := by
  obtain ⟨a₁, e₁, -, o₁, -⟩ := addImm_ok s .x0 sb (v := 8 * schedSlot) (by decide)
  obtain ⟨a₂, e₂, -, o₂, -⟩ := addImm_ok a₁ .x1 sb (v := 8 * cbcBuf) (by decide)
  obtain ⟨a₃, e₃, -, o₃, -⟩ := addImm_ok a₂ .x2 sb (v := 0) (by decide)
  obtain ⟨a₄, e₄, r₄, -⟩ := addImm_ok a₃ .x26 .x30 (v := 0) (by decide)
  have hs₁ : s₁ = a₄ := block_det hA (by
    rw [show cryptHead = [.addImm .x .x0 sb (8 * schedSlot)] ++ ([.addImm .x .x1 sb (8 * cbcBuf)] ++
      ([.addImm .x .x2 sb 0] ++ [.addImm .x .x26 .x30 0])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, e₄])
  subst hs₁
  obtain ⟨b₁, f₁, -, ob₁, -⟩ := addImm_ok s₂ sb .x2 (v := 0) (by decide)
  obtain ⟨b₂, f₂, q₂, -⟩ := addImm_ok b₁ .x30 .x26 (v := 0) (by decide)
  have hs' : s' = b₂ := block_det hB (by
    rw [show cryptTail = [.addImm .x sb .x2 0] ++ [.addImm .x .x30 .x26 0] from rfl, runBlock_app, f₁, Option.bind_some, f₂])
  subst hs'
  have k₂ : s₂.gpr .x26 = s₁.gpr .x26 := blockCall_keeps (.inr rfl) d _ _ _ hC
  rw [q₂, ob₁ _ (by decide), k₂, r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), BitVec.add_zero,
    BitVec.add_zero]

theorem crypt_keeps_x30 (d : Direction) : KeepsReg .x30 (dirCore d).crypt := by
  intro s t s' h
  rw [crypt_eq] at h
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

theorem cfb8Encrypt_keeps_x30 : KeepsReg .x30 cfb8Encrypt := by keeps_x30

theorem cfb8Decrypt_keeps_x30 : KeepsReg .x30 cfb8Decrypt := by keeps_x30

end VG.Proof.TripleDes.AArch64
