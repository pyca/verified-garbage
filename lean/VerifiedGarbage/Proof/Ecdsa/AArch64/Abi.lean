module

public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

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

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64

/-- The callee-saved registers but `x19`–`x25` and `x30`. -/
abbrev untouched : List Reg := [.x26, .x27, .x28]

/-- `topAll`, for compiled code. -/
def topAllC (p : Instr → Bool) : Prog isa → Bool
  | .block is => is.all p
  | .seq a b => topAllC p a && topAllC p b
  | .ite _ t e => topAllC p t && topAllC p e
  | .loop b _ => topAllC p b
  | .call _ _ => true
  | .frame i b j => p i && topAllC p b && p j
  | .icall i _ _ n => p i && topAllC p n

/-- Whether every instruction of `c` outside the functions it calls
satisfies `p`. A block is walked with `List.rec`, which the kernel evaluates
faster than `List.all` (as `Code.allInstrs`). Compiled code runs `topAllC`
(Lean's compiler does not compile `List.rec`). -/
@[implemented_by topAllC] noncomputable def topAll (p : Instr → Bool) : Prog isa → Bool
  | .block is => List.rec (motive := fun _ => Bool) true (fun i _ ih => p i && ih) is
  | .seq a b => topAll p a && topAll p b
  | .ite _ t e => topAll p t && topAll p e
  | .loop b _ => topAll p b
  | .call _ _ => true
  | .frame i b j => p i && topAll p b && p j
  | .icall i _ _ n => p i && topAll p n

theorem topAll_block (p : Instr → Bool) (is : List Instr) : topAll p (.block is) = is.all p := by
  induction is with
  | nil => rfl
  | cons i is ih => exact congrArg (p i && ·) ih

/-- Whether no instruction outside the functions `c` calls writes a register
of `untouched`. -/
abbrev KeepsUntouched (c : Prog isa) : Prop :=
  topAll (fun i => (dsts i).all fun r => !untouched.contains r) c = true

/-- Whether every function `c` calls keeps the registers of `untouched`:
code none of whose instructions writes them (checked first, in one pass over
the code), straight-line code that restores them (`restores`), or code that
keeps each of them. -/
abbrev CallsKeep (c : Prog isa) : Prop :=
  (c.calls.all fun nb => nb.2.allInstrs (fun i => (dsts i).all fun r => !untouched.contains r) ||
    (((straight nb.2).any fun is => untouched.all fun r => restores r is) ||
      untouched.all fun r => nb.2.allInstrs (keepsReg r))) = true

theorem keepsReg_of_untouched {i : Instr} {r : Reg} (hr : r ∈ untouched)
    (h : ((dsts i).all fun r => !untouched.contains r) = true) : keepsReg r i = true := by
  simpa [keepsReg] using clobbers_eq_false_of_all h (by simp only [List.contains_iff_mem.mpr hr, Bool.not_true])

/-- A register that no instruction outside the functions `c` calls writes,
and that those functions keep, is kept. -/
theorem gpr_top {r : Reg} (hr : r ∉ linkRegs) {c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') (hc : topAll (keepsReg r) c = true)
    (hb : (c.calls.all fun nb => (straight nb.2).any (restores r) || nb.2.allInstrs (keepsReg r)) = true) :
    s'.gpr r = s.gpr r := by
  induction h with
  | icall hi => nomatch hi
  | icallNext hi => nomatch hi
  | block h =>
    exact execBlock_keep (fun s : State => s.gpr r) (ok := fun i => keepsReg r i = true)
      (fun hi he => exec_gpr (by simpa [keepsReg] using hi) he)
      (List.all_eq_true.mp (by rwa [topAll_block] at hc)) h
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
    simp only [Code.calls, List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at hb
    rcases hb.1 with hb | hb
    · obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp hb
      obtain ⟨_, eb⟩ := straight_exec his e
      rw [ret_eq hr', restores_ok hres eb, (call_eq hc₁).2.2.2.2 r hr]
    · rw [ret_eq hr', Exec.gpr (fun i hi => by
          have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hb) i hi
          simpa [keepsReg] using this) e (.inr hr), (call_eq hc₁).2.2.2.2 r hr]
  | frame hp _ hq ih =>
    simp only [topAll, Bool.and_eq_true] at hc
    simp only [Code.calls] at hb
    obtain ⟨-, -, -, hg, -⟩ := push_eq hp
    rw [(pop_eq hq).2.2.2.1 r (dstOf_ne_of_clobbers (by simpa [keepsReg] using hc.2)), ih hc.1.2 hb, hg]

/-- A run that writes no register of `untouched` outside the functions it
calls, which keep them, keeps them. -/
theorem untouched_keep {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hn : CallsKeep c) (hu : KeepsUntouched c) : ∀ r ∈ untouched, s'.gpr r = s.gpr r := by
  intro r h
  refine gpr_top (by revert h; revert r; decide) he ?_ ?_
  · have : ∀ p q : Instr → Bool, (∀ i, p i = true → q i = true) → ∀ c : Prog isa,
        topAll p c = true → topAll q c = true := by
      intro p q hpq c
      induction c with
      | icall i _ _ n _ ihn =>
        simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨hpq i h.1, ihn h.2⟩
      | block is =>
        rw [topAll_block, topAll_block, List.all_eq_true, List.all_eq_true]
        exact fun h i hi => hpq i (h i hi)
      | seq a b iha ihb | ite _ a b iha ihb =>
        simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨iha h.1, ihb h.2⟩
      | loop b _ ih => exact ih
      | call _ _ _ => intro _; rfl
      | frame i b j ih =>
        simp only [topAll, Bool.and_eq_true]; exact fun h => ⟨⟨hpq i h.1.1, ih h.1.2⟩, hpq j h.2⟩
    exact this _ _ (fun i hi => keepsReg_of_untouched h hi) c hu
  · refine List.all_eq_true.mpr fun nb hnb => ?_
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hn nb hnb) with h' | h'
    · refine Bool.or_eq_true_iff.mpr (.inr ?_)
      rw [Code.allInstrs_eq] at h' ⊢
      exact List.all_eq_true.mpr fun i hi => keepsReg_of_untouched h (List.all_eq_true.mp h' i hi)
    rcases Bool.or_eq_true_iff.mp h' with h' | h'
    · obtain ⟨is, his, hres⟩ := (Option.any_eq_true _ _).mp h'
      exact Bool.or_eq_true_iff.mpr (.inl ((Option.any_eq_true _ _).mpr ⟨is, his, List.all_eq_true.mp hres r h⟩))
    · exact Bool.or_eq_true_iff.mpr (.inr (List.all_eq_true.mp h' r h))

/-- A run that restores `x19`–`x25` and `x30`, writes no other callee-saved
register outside the functions it calls, which keep them, and writes no
callee-saved SIMD register, preserves what the ABI asks. -/
theorem abiPreserved_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hn : CallsKeep c) (hu : KeepsUntouched c) (hv : c.allInstrs keepsV = true)
    (hsv : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s.gpr r) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩
  by_cases h : r ∈ untouched
  · exact untouched_keep he hn hu r h
  · refine hsv r ?_
    revert h
    revert r
    decide

end VG.Proof.Ecdsa.AArch64
