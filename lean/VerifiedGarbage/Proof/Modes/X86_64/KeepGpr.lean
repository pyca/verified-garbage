module
public import VerifiedGarbage.TCB.X86_64.Isa

import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# Code that keeps a general-purpose register

`keepsGpr_of_gprSafe`: code whose every instruction writes no
general-purpose register (an SSE instruction, a 128-bit load, a store) or
one other than `r` keeps `r`, whatever it does to the rest. A core whose
block code needs every `xmm` register, `ivX` among them, keeps the IV's
address in such a register around it (`Proof/Blowfish/X86_64/ModeCore.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd

/-- Whether `i` writes no general-purpose register but, at most, one other
than `r`. -/
def gprSafeI (r : Reg) : Instr → Bool
  | .xop _ | .movdquLoad .. | .movdquStore .. | .store .. | .store32 .. => true
  | .mov d _ | .mov32 d _ | .alu _ d _ | .movImm64 d _ | .bswap32 d | .movqR d _ => d != r
  | _ => false

theorem xop_exec_gpr (op : XOp) (s : State) : (op.exec s).gpr = s.gpr := by
  cases op <;> rfl

theorem execAlu_gpr {op : AluOp} {d : Reg} {src : Src} {s t : State} (h : execAlu op d src s = some t)
    {r : Reg} (hr : r ≠ d) : t.gpr r = s.gpr r := by
  simp only [execAlu, Option.bind_eq_some_iff] at h
  obtain ⟨b, -, h⟩ := h
  cases op <;> simp only [Option.some.injEq, Option.map_eq_some_iff] at h
  all_goals first
    | (subst h; simp only [gpr_setReg_of_ne _ _ hr, gpr_arithFlags])
    | (obtain ⟨c, -, rfl⟩ := h; simp only [gpr_setReg_of_ne _ _ hr, gpr_arithFlags])

theorem exec_gprSafe {r : Reg} {i : Instr} (hi : gprSafeI r i = true) {s t : State} (h : exec i s = some t) :
    t.gpr r = s.gpr r := by
  cases i <;> simp only [gprSafeI, bne_iff_ne, ne_eq, Bool.false_eq_true] at hi
  all_goals simp only [reduceExec, Option.map_eq_some_iff, Option.some.injEq] at h
  all_goals first
    | (subst h; first | rfl | exact congrFun (xop_exec_gpr _ _) _ |
        simp only [State.setReg32, gpr_setReg_of_ne _ _ (Ne.symm hi)])
    | (obtain ⟨v, -, rfl⟩ := h; first | rfl | simp only [State.setReg32, gpr_setReg_of_ne _ _ (Ne.symm hi)])
    | exact execAlu_gpr h (Ne.symm hi)
    | (simp only [State.store64, State.store32, State.store128] at h
       split at h
       · cases h; rfl
       · cases h)

/-- Whether every instruction of `c` keeps `r`, with no calls or frames. -/
def gprSafe (r : Reg) : Prog isa → Bool
  | .block is => is.all (gprSafeI r)
  | .seq a b => gprSafe r a && gprSafe r b
  | .ite _ a b => gprSafe r a && gprSafe r b
  | .loop b _ => gprSafe r b
  | _ => false

theorem execBlock_gprSafe {r : Reg} : ∀ {is : List Instr}, is.all (gprSafeI r) = true → ∀ {s s' : State}
    {t : List Leak}, execBlock isa is s = some (s', t) → s'.gpr r = s.gpr r
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, hs, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, t₂, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      rw [← he'.1]
      exact (execBlock_gprSafe hs.2 h).trans (exec_gprSafe hs.1 he)

theorem keepsGpr_of_gprSafe {r : Reg} {c : Prog isa} (hc : gprSafe r c = true) :
    ∀ s t s', Exec isa c s t s' → s'.gpr r = s.gpr r := by
  intro s t s' h
  revert hc
  induction h with
  | icall | icallNext => intro hc; simp only [gprSafe, Bool.false_eq_true] at hc
  | block e => exact fun hc => execBlock_gprSafe hc e
  | seq _ _ ih₁ ih₂ =>
    intro hc
    simp only [gprSafe, Bool.and_eq_true] at hc
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  | iteT _ _ ih => intro hc; simp only [gprSafe, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [gprSafe, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => intro hc; exact (ih₂ hc).trans (ih₁ hc)
  | call => intro hc; simp only [gprSafe, Bool.false_eq_true] at hc
  | frame => intro hc; simp only [gprSafe, Bool.false_eq_true] at hc

end VG.Proof.Modes.X86_64
