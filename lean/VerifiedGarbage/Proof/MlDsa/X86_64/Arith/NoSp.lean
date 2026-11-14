module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk

/-!
# ML-DSA on x86-64: never writing `rsp`, and how deep calls nest, by evaluation

What the functions calling a backend need of their own code, evaluated with
every function of the backend empty (`Same`): that it never writes `rsp`
(`noSpB`, `noSp_of`), and how deep its calls nest (`depthCompN`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64

/-- Calls nesting at most `n + 1` deep, from functions whose calls nest at most `n` deep. -/
theorem depthCompN (n : Nat) : Comp (fun c => decide (c.depth ≤ n + 1)) (fun c => decide (c.depth ≤ n)) := by
  refine ⟨fun a b => ?_, fun _ t e => ?_, fun _ _ => rfl, fun _ b => ?_, rfl⟩
  · simp only [Code.depth, Nat.max_le, Bool.decide_and]
  · simp only [Code.depth, Nat.max_le, Bool.decide_and]
  · simp only [Code.depth]
    exact decide_eq_decide.mpr (by omega_using [])

/-- `NoSp` from evaluating the code. -/
noncomputable abbrev noSpB (c : Prog isa) : Bool := c.allInstrs fun i => !Taint.clobbers i .rsp

theorem noSp_of {c : Prog isa} (h : noSpB c = true) : NoSp c := Proof.MlKem.X86_64.nosp_of h

theorem noSpB_of {c : Prog isa} (h : NoSp c) : noSpB c = true := by
  rw [noSpB, Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

end VG.Proof.MlDsa.X86_64
