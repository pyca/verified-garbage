module

public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Relate recovery calls with equal public pointers, lengths, and stack position -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86

structure Pair (g : CallGeometry) (s t : State) : Prop where
  left : Inputs g s
  right : Inputs g t
  sp : s.gpr .esp = t.gpr .esp

theorem Pair.agree {g : CallGeometry} {s t : State} (h : Pair g s t) :
    VG.X86.Taint.Agree argumentTaint s t := by
  apply agree_regs (rs := [.edi, .esp])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact BitVec.eq_of_toNat_eq (h.left.ws.workspace.edi_toNat.trans h.right.ws.workspace.edi_toNat.symm)
  · exact h.sp

theorem Pair.workspace {g : CallGeometry} {s t : State} (h : Pair g s t) :
    VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) s t := by
  apply agree_regs
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h.agree.rf.1 _ (by decide)

theorem Pair.after {g : CallGeometry} {s t u v : State} {regs : List Reg} (h : Pair g s t)
    (hu : Inputs g u) (hv : Inputs g v) (ku : Keeps regs s u) (kv : Keeps regs t v)
    (sp : .esp ∉ regs) : Pair g u v :=
  ⟨hu, hv, (ku.1 _ sp).trans (h.sp.trans (kv.1 _ sp).symm)⟩

theorem Pair.keepMem {g : CallGeometry} {s t u v : State} {regs : List Reg} (h : Pair g s t)
    (ks : Keeps regs s u) (kt : Keeps regs t v) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (ms : u.mem = s.mem) (mt : v.mem = t.mem) : Pair g u v :=
  h.after (h.left.after ks di sp (by rw [ms]; exact Frame.refl _ _))
    (h.right.after kt di sp (by rw [mt]; exact Frame.refl _ _)) ks kt sp

end VG.Proof.Rsa.X86.Recover
