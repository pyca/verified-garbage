module

public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# Code that keeps the IV's address in `ivX`

`keepsIv_of_ivSafe`: code whose every instruction is scalar (`scalarI`),
reads or stores an `xmm` register (`movq r64, xmm`, `movdqu m128, xmm`), or
writes an `xmm` register other than `ivX` (an SSE instruction, `movdqu xmm,
m128`) keeps `ivX` (`KeepsIv`), as the feedback modes need of a core
(`Proof/Modes/X86_64/Fb.lean`): a core whose block code uses some of the
other `xmm` registers, or that keeps values in them when it runs out of
general-purpose ones, or across a call of a function that may write them.
A call counts as the function's code (a call and a return keep `ivX`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.Impl.Modes.X86_64

/-- `movq r64, xmm`, and stores of `xmm` registers, which write no `xmm` register. -/
def isXmmRead : Instr → Bool
  | .movqR .. | .movdquStore .. => true
  | _ => false

/-- The `xmm` register an SSE instruction writes (it writes no other). -/
def xopDst : XOp → XReg
  | .bin _ d _ | .shift _ d _ | .pshufd d _ _ | .palignr d _ _ | .pblendw d _ _ | .sha256rnds2 d _ | .sha1rnds4 d _ _
  | .movq d _ | .aeskeygenassist d _ _ | .pclmulqdq d _ _ => d

/-- The `xmm` register an SSE instruction or a 128-bit load writes. -/
def xmmDst : Instr → Option XReg
  | .xop op => some (xopDst op)
  | .movdquLoad d _ => some d
  | _ => none

/-- The instructions that keep `ivX`: scalar ones, reads and stores of
`xmm` registers, and SSE instructions and loads that write another `xmm`
register. -/
def ivSafeI (i : Instr) : Bool :=
  scalarI i || isXmmRead i || match xmmDst i with | some d => d != Core.ivX | none => false

theorem xop_exec_xmm (op : XOp) (s : State) {r : XReg} (h : r ≠ xopDst op) : (op.exec s).xmm r = s.xmm r := by
  cases op <;> exact RegUpd.xmm_setXmm_of_ne _ _ h

theorem exec_ivSafe {i : Instr} (hi : ivSafeI i = true) {s t : State} (h : exec i s = some t) :
    t.xmm Core.ivX = s.xmm Core.ivX := by
  unfold ivSafeI at hi
  simp only [Bool.or_eq_true] at hi
  rcases hi with (hs | hm) | hq
  · exact congrFun (exec_vec hs h).1 _
  · cases i <;> first | exact absurd hm Bool.false_ne_true | skip
    all_goals first
      | (simp only [exec, Option.some.injEq] at h; subst h; rfl)
      | (simp only [exec, State.store128] at h
         split at h
         · cases h; rfl
         · cases h)
  · cases i <;> first | exact absurd hq Bool.false_ne_true | skip
    all_goals simp only [xmmDst, bne_iff_ne, ne_eq] at hq
    all_goals first
      | (simp only [exec, Option.some.injEq] at h; subst h
         exact xop_exec_xmm _ s (Ne.symm hq))
      | (simp only [exec, Option.map_eq_some_iff] at h
         obtain ⟨v, -, rfl⟩ := h
         exact RegUpd.xmm_setXmm_of_ne _ _ (Ne.symm hq))

/-- Whether every instruction of `c`, and of the functions it calls, keeps
`ivX`, with no frames: a call and its return change only `rsp` and memory. -/
def ivSafe : Prog isa → Bool
  | .block is => is.all ivSafeI
  | .seq a b => ivSafe a && ivSafe b
  | .ite _ a b => ivSafe a && ivSafe b
  | .loop b _ => ivSafe b
  | .call _ b => ivSafe b
  | _ => false

theorem execBlock_ivSafe : ∀ {is : List Instr}, is.all ivSafeI = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.xmm Core.ivX = s.xmm Core.ivX
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
      exact (execBlock_ivSafe hs.2 h).trans (exec_ivSafe hs.1 he)

theorem keepsIv_of_ivSafe {c : Prog isa} (hc : ivSafe c = true) : KeepsIv c := by
  intro s t s' h hz
  clear hz
  revert hc
  induction h with
  | icall | icallNext => intro hc; simp only [ivSafe, Bool.false_eq_true] at hc
  | block e => exact fun hc => execBlock_ivSafe hc e
  | seq _ _ ih₁ ih₂ =>
    intro hc
    simp only [ivSafe, Bool.and_eq_true] at hc
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  | iteT _ _ ih => intro hc; simp only [ivSafe, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [ivSafe, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => intro hc; exact (ih₂ hc).trans (ih₁ hc)
  | call hc₁ _ hr ih =>
    intro hc
    have a := ih hc
    simp only [isa, call, Option.some.injEq] at hc₁
    subst hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    exact a
  | frame => intro hc; simp only [ivSafe, Bool.false_eq_true] at hc

end VG.Proof.Modes.X86_64
