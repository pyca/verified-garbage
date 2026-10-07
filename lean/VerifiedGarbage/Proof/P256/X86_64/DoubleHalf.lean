import VerifiedGarbage.Impl.P256.X86_64.DoubleHalf
import VerifiedGarbage.Proof.P256.X86_64.HalfField
import VerifiedGarbage.Proof.Weierstrass.Jac

/-! The in-place halving schedule computes the usual Jacobian double. -/
namespace VG.Proof.P256.X86_64
open VG VG.Impl.Weierstrass VG.Impl.P256.X86_64 VG.Proof.Weierstrass

def doubleSlots (S : RcbSlots) (p : Pt) : List Nat :=
  [S.t0,S.t1,S.t2,S.t3,S.t4,p.x,p.y,p.z]

def doubleHalfEnv (S : RcbSlots) (p : Pt) (E : Nat → Fin Spec.P256.p) : Nat → Fin Spec.P256.p :=
  let E₁ := runOps (DoubleHalf.before S p) E
  runOps (DoubleHalf.after S p) (Function.update E₁ S.t1 (halfFe (E₁ S.t1)))

private theorem half_fourth {F : Type _} [Lean.Grind.CommRing F]
    {y i : F} (hi : (2:F)*i=1) :
    ((y+y)*(y+y)*((y+y)*(y+y)))*i = 8*(y*y*(y*y)) := by
  have h := congrArg (fun z => (y*y*(y*y))*z) hi
  grind

theorem doubleHalfEnv_run (S : RcbSlots) (p : Pt) (E : Nat → Fin Spec.P256.p)
    (hd : (doubleSlots S p).Nodup) :
    (doubleHalfEnv S p E p.x,doubleHalfEnv S p E p.y,doubleHalfEnv S p E p.z)=
      dblJF (E p.x) (E p.y) (E p.z) := by
  have hi : (2 : Fin Spec.P256.p) * Fin.ofNat Spec.P256.p ((Spec.P256.p+1)/2)=1 := by decide
  have hh := half_fourth (y:=E p.y) hi
  simp only [doubleSlots,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hd
  rcases hd with ⟨⟨h01,h02,h03,h04,h05,h06,h07⟩,⟨h12,h13,h14,h15,h16,h17⟩,⟨h23,h24,h25,h26,h27⟩,⟨h34,h35,h36,h37⟩,⟨h45,h46,h47⟩,⟨h56,h57⟩,h67,_⟩
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h30 := Ne.symm h03
  have h40 := Ne.symm h04
  have h50 := Ne.symm h05
  have h60 := Ne.symm h06
  have h70 := Ne.symm h07
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h41 := Ne.symm h14
  have h51 := Ne.symm h15
  have h61 := Ne.symm h16
  have h71 := Ne.symm h17
  have h32 := Ne.symm h23
  have h42 := Ne.symm h24
  have h52 := Ne.symm h25
  have h62 := Ne.symm h26
  have h72 := Ne.symm h27
  have h43 := Ne.symm h34
  have h53 := Ne.symm h35
  have h63 := Ne.symm h36
  have h73 := Ne.symm h37
  have h54 := Ne.symm h45
  have h64 := Ne.symm h46
  have h74 := Ne.symm h47
  have h65 := Ne.symm h56
  have h75 := Ne.symm h57
  have h76 := Ne.symm h67
  simp only [doubleHalfEnv,DoubleHalf.before,DoubleHalf.after,runOps,List.foldl,FOp.run,
    Function.update_apply,halfFe,dblJF,Prod.mk.injEq, *,ite_true,ite_false]
  constructor
  · grind
  constructor <;> grind

end VG.Proof.P256.X86_64
