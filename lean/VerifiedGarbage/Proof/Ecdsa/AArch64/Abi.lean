import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore

/-!
# The ABI of the curve functions on AArch64

The functions built on ECDSA's code save and restore `x19`–`x25` and `x30`,
and no instruction of theirs outside the functions they call writes the
other callee-saved registers (`untouched`), which one check of every such
instruction shows (`KeepsUntouched`, by `lit_decide` on the code's literal);
the functions they call (the Montgomery products) restore those they write
from vector lanes, which `CallsKeep` checks of their code (`restores`). So,
with `x19`–`x25` and `x30` restored, they preserve what the ABI asks
(`abiPreserved_of`).
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64

/-- The callee-saved registers but `x19`–`x25` and `x30`. -/
abbrev untouched : List Reg := [.x26, .x27, .x28]

/-- Whether every instruction of `c` outside the functions it calls
satisfies `p`. -/
def topAll (p : Instr → Bool) : Prog isa → Bool
  | .block is => is.all p
  | .seq a b => topAll p a && topAll p b
  | .ite _ t e => topAll p t && topAll p e
  | .loop b _ => topAll p b
  | .call _ _ => true
  | .frame i b j => p i && topAll p b && p j

/-- Whether no instruction outside the functions `c` calls writes a register
of `untouched`. -/
abbrev KeepsUntouched (c : Prog isa) : Prop :=
  topAll (fun i => (dstOf i).all fun r => !untouched.contains r) c = true

/-- Whether every function `c` calls is straight-line code that keeps the
registers of `untouched` (`restores`). -/
abbrev CallsKeep (c : Prog isa) : Prop :=
  (c.calls.all fun nb => (straight nb.2).any fun is => untouched.all fun r => restores r is) = true

theorem keepsReg_of_untouched {i : Instr} {r : Reg} (hr : r ∈ untouched)
    (h : ((dstOf i).all fun r => !untouched.contains r) = true) : keepsReg r i = true := by
  unfold keepsReg
  cases hd : dstOf i with
  | none => rfl
  | some d =>
    rw [hd] at h
    simp only [Option.all_some, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    simp only [Option.all_some, bne_iff_ne, ne_eq]
    rintro rfl
    exact h hr

/-- A register that no instruction outside the functions `c` calls writes,
and that those functions keep, is kept. -/
theorem gpr_top {r : Reg} (hr : r ∉ linkRegs) {c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') (hc : topAll (keepsReg r) c = true)
    (hb : (c.calls.all fun nb => (straight nb.2).any (restores r)) = true) : s'.gpr r = s.gpr r := by
  induction h with
  | block h =>
    exact execBlock_keep (fun s : State => s.gpr r) (ok := fun i => keepsReg r i = true)
      (fun hi he => exec_gpr (fun hd => by simp [keepsReg, hd] at hi) he)
      (List.all_eq_true.mp (by simpa only [topAll] using hc)) h
  | seq _ _ ih₁ ih₂ =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    rw [ih₂ hc.2 hb.2, ih₁ hc.1 hb.1]
  | iteT _ _ ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    exact ih hc.1 hb.1
  | iteF _ _ ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls, List.all_append, Bool.and_eq_true] at hb
    exact ih hc.2 hb.2
  | loopExit _ _ ih => exact ih hc hb
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc hb, ih₁ hc hb]
  | call hc₁ e hr' _ =>
    simp only [Code.calls, List.all_cons, Bool.and_eq_true] at hb
    obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp hb.1
    obtain ⟨_, eb⟩ := straight_exec his e
    rw [ret_eq hr', restores_ok hres eb, (call_eq hc₁).2.2.2.2 r hr]
  | frame hp _ hq ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls] at hb
    obtain ⟨-, -, -, hg, -⟩ := push_eq hp
    rw [(pop_eq hq).2.2.2.1 r (fun hd => by simp [keepsReg, hd] at hc), ih hc.1.2 hb, hg]

/-- A run that restores `x19`–`x25` and `x30`, writes no other callee-saved
register outside the functions it calls, which keep them, and writes no
callee-saved SIMD register, preserves what the ABI asks. -/
theorem abiPreserved_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hn : CallsKeep c) (hu : KeepsUntouched c) (hv : c.allInstrs keepsV = true)
    (hsv : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s.gpr r) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩
  by_cases h : r ∈ untouched
  · refine gpr_top (by revert h; revert r; decide) he ?_ ?_
    · have : ∀ p q : Instr → Bool, (∀ i, p i = true → q i = true) → ∀ c : Prog isa,
          topAll p c = true → topAll q c = true := by
        intro p q hpq c
        induction c with
        | block is => simp only [topAll, List.all_eq_true]; exact fun h i hi => hpq i (h i hi)
        | seq a b iha ihb | ite _ a b iha ihb =>
          simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨iha h.1, ihb h.2⟩
        | loop b _ ih => exact ih
        | call _ _ _ => intro _; rfl
        | frame i b j ih =>
          simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨⟨hpq i h.1.1, ih h.1.2⟩, hpq j h.2⟩
      exact this _ _ (fun i hi => keepsReg_of_untouched h hi) c hu
    · refine List.all_eq_true.mpr fun nb hnb => ?_
      obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp (List.all_eq_true.mp hn nb hnb)
      exact (Option.any_eq_true _ _).mpr ⟨is, his, List.all_eq_true.mp hres r h⟩
  · refine hsv r ?_
    revert h
    revert r
    decide

end VG.Proof.Ecdsa.AArch64
