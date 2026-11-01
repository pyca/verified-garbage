module

public import VerifiedGarbage.Proof.Bignum.X86.PublicInputs
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # What the pieces of public RSA at a run-time width need of their inputs

The working space, the arguments on the stack, the output and the input:
what `PublicInputs` and `PrecomputedInputs` share (`RtIn`). The width of
the numbers is read from `out_len` (argument 1), which is the modulus's
length in both.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86

structure RtIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base bytes
  lower : 64 ≤ len
  upper : len ≤ 1024
  space : size (Spec.Rsa.modulusWords len) ≤ bytes
  stack : CallArguments s base bytes args
  outLen : args 1 = BitVec.ofNat 32 len
  inLen : args 7 = BitVec.ofNat 32 len
  outFit : (args 0).toNat + len ≤ 2 ^ 32
  inFit : (args 6).toNat + len ≤ 2 ^ 32
  outWrite : InRegions s.wr (byteAddr (args 0)) len
  inRead : InRegions (s.rd ++ s.wr) (byteAddr (args 6)) len
  outApart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args 0), len⟩
  inApart : Region.Disjoint ⟨byteAddr (args 6), len⟩ ⟨base, bytes⟩

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}

theorem _root_.VG.Proof.Bignum.X86.PublicInputs.rt (h : PublicInputs base bytes len args s) :
    RtIn base bytes len args s :=
  ⟨h.scratch, h.lower, h.upper, h.space, h.stack, h.outLen, h.inLen, h.outFit, h.inFit, h.outWrite,
    h.inRead, h.outApart, h.inApart⟩

theorem _root_.VG.Proof.Bignum.X86.PrecomputedInputs.rt (h : PrecomputedInputs base bytes len args s) :
    RtIn base bytes len args s :=
  ⟨h.scratch, h.lower, h.upper, h.space, h.stack, h.outLen, h.inLen, h.outFit, h.inFit, h.outWrite,
    h.inRead, h.outApart, h.inApart⟩

theorem RtIn.keep (h : RtIn base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) : RtIn base bytes len args t :=
  ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space, h.stack.keep K sp O, h.outLen, h.inLen, h.outFit,
    h.inFit, by rw [K.2.2]; exact h.outWrite, by rw [K.2.1, K.2.2]; exact h.inRead, h.outApart, h.inApart⟩

theorem RtIn.dimensions (h : RtIn base bytes len args s) :
    0 < Spec.Rsa.modulusWords len ∧ 128 * Spec.Rsa.modulusWords len < 2 ^ 32 ∧
      len ≤ 8 * Spec.Rsa.modulusWords len := by
  have := h.lower
  have := h.upper
  unfold Spec.Rsa.modulusWords
  omega

end

end VG.Proof.Bignum.X86.PublicRt
