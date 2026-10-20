module

public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Relate two calls with the same public lengths and pointers -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure Pair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop where
  left : Inputs base bytes len args s
  right : Inputs base bytes len args t
  sp : s.gpr .esp = t.gpr .esp

theorem Pair.agree {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (H : Pair base bytes len args s t) : VG.X86.Taint.Agree argumentTaint s t := by
  apply agree_regs (rs := [.edi, .esp])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    exact H.left.scratch.edi_toNat.trans H.right.scratch.edi_toNat.symm
  · exact H.sp

theorem Pair.keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t u v : State}
    (H : Pair base bytes len args s t) {regs : List Reg}
    (Ks : Keeps regs s u) (Kt : Keeps regs t v) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (Os : Outside base 0 bytes s.mem u.mem) (Ot : Outside base 0 bytes t.mem v.mem) :
    Pair base bytes len args u v :=
  ⟨H.left.keep Ks di sp Os, H.right.keep Kt di sp Ot, (Ks.1 _ sp).trans (H.sp.trans (Kt.1 _ sp).symm)⟩

end VG.Proof.Bignum.X86.Crt
