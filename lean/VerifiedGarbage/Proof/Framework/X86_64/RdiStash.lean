module

public import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.XmmFrame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # x86-64: code that gives `rdi` back

Code that writes `rdi` only to count a loop of scalar code, keeping its value
in `xmm0` meanwhile (`movq xmm0, rdi; mov rdi, imm`, the loop, `movq rdi, xmm0`),
leaves `rdi` as it found it (`keepsRdi_exec`). -/

@[expose] public section

namespace VG.X86_64

/-- Code whose only writes of `rdi` are such stashes. -/
def keepsRdi : Prog isa → Bool
  | .seq (.block [.xop (.movq .xmm0 .rdi), .mov .rdi (.imm _)]) (.seq (.loop b _) (.block [.movqR .rdi .xmm0])) =>
    scalCode b
  | .block is => is.all fun i => !Taint.clobbers i .rdi
  | .seq a b => keepsRdi a && keepsRdi b
  | .ite _ a b => keepsRdi a && keepsRdi b
  | .loop b _ => keepsRdi b
  | _ => false

theorem keepsRdi_exec {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hk : keepsRdi c = true) : s'.gpr .rdi = s.gpr .rdi := by
  induction h with
  | block e =>
    simp only [keepsRdi, List.all_eq_true, Bool.not_eq_true'] at hk
    exact Exec.gpr (fun i hi => hk i (by simpa [instrs] using hi)) (Exec.block e)
  | seq h₁ h₂ ih₁ ih₂ =>
    unfold keepsRdi at hk
    split at hk
    · rename_i v b cnd heq
      obtain ⟨rfl, rfl⟩ := Code.seq.inj heq
      cases h₂ with
      | seq hl hr =>
        cases h₁ with
        | block e₁ =>
          cases hr with
          | block e₃ =>
            have hx := (exec_scal hl hk).1
            simp only [execBlock, exec, XOp.exec, readSrc, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at e₁ e₃
            obtain ⟨rfl, -⟩ := e₁
            obtain ⟨rfl, -⟩ := e₃
            rw [VG.X86_64.RegUpd.gpr_setReg_self, hx]
            simp only [State.setReg, State.setXmm, ite_true, KeepReg.xmm_lo_append]
    · cases ‹Code.seq _ _ = Code.block _›
    · rename_i a b _ heq
      obtain ⟨rfl, rfl⟩ := Code.seq.inj heq
      simp only [Bool.and_eq_true] at hk
      exact (ih₂ hk.2).trans (ih₁ hk.1)
    · cases ‹Code.seq _ _ = Code.ite _ _ _›
    · cases ‹Code.seq _ _ = Code.loop _ _›
    · cases hk
  | iteT _ _ ih =>
    simp only [keepsRdi, Bool.and_eq_true] at hk; exact ih hk.1
  | iteF _ _ ih =>
    simp only [keepsRdi, Bool.and_eq_true] at hk; exact ih hk.2
  | loopExit _ _ ih => simp only [keepsRdi] at hk; exact ih hk
  | loopNext _ _ _ ih₁ ih₂ =>
    exact (ih₂ hk).trans (ih₁ (by simpa only [keepsRdi] using hk))
  | call => simp only [keepsRdi] at hk; cases hk
  | frame => simp only [keepsRdi] at hk; cases hk

end VG.X86_64
