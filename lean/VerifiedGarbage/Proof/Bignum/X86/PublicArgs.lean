module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps

/-! # Reading public RSA arguments through the unchanged cdecl stack pointer -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem argument_keep {s t : State} {regs : List Reg} (K : Keeps regs s t)
    (sp : .esp ∉ regs) (M : t.mem = s.mem) (i : Nat) :
    readSrc t (.mem (PublicFn.argument i)) = readSrc s (.mem (PublicFn.argument i)) := by
  simp only [readSrc, PublicFn.argument, VG.Impl.Mont.X86.at_, State.ea, State.load32,
    K.1 .esp sp, K.2.1, K.2.2, M]
  rfl

theorem argumentPair_ok {s : State} {d : Reg} {i j : Nat} {p c : BitVec 32}
    (de : d ≠ .esp) (dc : d ≠ .ecx)
    (P : readSrc s (.mem (PublicFn.argument i)) = some p)
    (C : readSrc s (.mem (PublicFn.argument j)) = some c) :
    WP isa (.block [.mov d (.mem (PublicFn.argument i)), .mov .ecx (.mem (PublicFn.argument j))]) s
      fun t => t.gpr d = p ∧ t.gpr .ecx = c ∧ t.mem = s.mem ∧ Keeps [d, .ecx] s t := by
  refine wp_movS P fun u a _ => ?_
  refine wp_movS (by rw [argument_keep a.keeps (by simp [Ne.symm de]) a.mem j]; exact C)
    fun t b _ => WP.block_nil ?_
  exact ⟨(b.other d dc).trans a.gpr, b.gpr, b.mem.trans a.mem,
    (a.keeps.mono (by simp)).trans (b.keeps.mono (by simp))⟩

end VG.Proof.Bignum.X86
