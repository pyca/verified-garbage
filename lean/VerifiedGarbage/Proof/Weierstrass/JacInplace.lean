import VerifiedGarbage.Proof.Weierstrass.JacMul

/-! The direct-product doubling schedule permits its input and output to coincide. -/
namespace VG.Proof.Weierstrass
open VG.Impl.Weierstrass

theorem dblJMul_inplace_run {F : Type _} [Lean.Grind.CommRing F]
    {S : RcbSlots} {p : Pt} (h : (rcbW S p).Nodup) (e : Nat → F) :
    (runOps (dblJMul S p p) e p.x,runOps (dblJMul S p p) e p.y,
      runOps (dblJMul S p p) e p.z)=dblJF (e p.x) (e p.y) (e p.z) := by
  simp only [rcbW,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,
    not_or] at h
  dsimp only [dblJMul,runOps,List.foldl,FOp.run,Function.update]
  simp only [dblJF,Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

end VG.Proof.Weierstrass
