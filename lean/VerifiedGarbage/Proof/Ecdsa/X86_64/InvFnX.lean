module
import Mathlib.Data.Nat.Prime.Defs
public import VerifiedGarbage.Impl.Ecdsa.X86_64
import Mathlib.Tactic.Tauto
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg

import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsWrap

/-!
# The functions of four words: the callee-saved registers come back

`Cfg.invFnX body` copies the callee-saved registers into `xmm0`–`xmm5`, runs
`body` and copies them back. If `body` writes no vector register and calls
nothing, each comes back with its value (`invFnX_gpr`), as for the point
functions (`PointOps.wrap_gpr`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64.PointOps (Exec.xmm_of)

theorem invFnX_gpr {body : Prog isa} (hv : body.allInstrs (fun i => !KeepReg.writesVec i) = true)
    (hn : body.noCalls = true) {s s' : State} {t : List Leak} (he : Exec isa (Cfg.invFnX body) s t s') :
    ∀ r ∈ Cfg.invKeptX.map Prod.fst, s'.gpr r = s.gpr r := by
  intro r hr
  cases he with
  | seq h₁ h₂ =>
    cases h₂ with
    | seq h₂ h₃ =>
      have hs := KeepReg.Exec.holds (v := s.gpr r) h₁ (a := ⟨true, .empty⟩) rfl
        ⟨fun _ => rfl, fun x hx => absurd hx (RegSet.not_mem_empty x)⟩
      let A := KeepReg.run r (Cfg.invKeptX.map fun (r, x) => Instr.xop (.movq x r)) true 0
      have hA : KeepReg.Holds r (s.gpr r) ⟨false, A.xs⟩ _ :=
        hs.mono (a := ⟨false, A.xs⟩) (by
          simp only [KeepReg.le, Bool.not_false, Bool.true_or, Bool.true_and]
          rw [RegSet.subset_eq]
          simp only [A, show (RegSet.empty : RegSet XReg).bits = 0 from rfl, Nat.and_self, beq_self_eq_true])
      have hx := Exec.xmm_of h₂ hv hn
      have hB : KeepReg.Holds r (s.gpr r) ⟨false, A.xs⟩ _ := ⟨nofun, fun x h => by
        rw [hx]; exact hA.2 x h⟩
      have hr' := KeepReg.Exec.holds (v := s.gpr r) h₃ (a := ⟨false, A.xs⟩) rfl hB
      refine hr'.1 ?_
      simp only [Cfg.invKeptX, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Ecdsa.X86_64
