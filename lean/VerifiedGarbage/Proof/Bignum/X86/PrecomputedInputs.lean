module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Packed-key call geometry preserved while the RSA scratch arrays change -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

structure PrecomputedInputs (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base bytes
  lower : 64 ≤ len
  upper : len ≤ 1024
  space : size (Spec.Rsa.modulusWords len) ≤ bytes
  stack : CallArguments s base bytes args
  outLen : args 1 = BitVec.ofNat 32 len
  preLen : args 3 = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords len)
  inLen : args 7 = BitVec.ofNat 32 len
  ePositive : 0 < (args 5).toNat
  eBound : (args 5).toNat ≤ len
  outFit : (args 0).toNat + len ≤ 2 ^ 32
  preFit : (args 2).toNat + 16 * Spec.Rsa.modulusWords len ≤ 2 ^ 32
  eFit : (args 4).toNat + (args 5).toNat ≤ 2 ^ 32
  inFit : (args 6).toNat + len ≤ 2 ^ 32
  outWrite : InRegions s.wr (byteAddr (args 0)) len
  preRead : InRegions (s.rd ++ s.wr) (byteAddr (args 2)) (16 * Spec.Rsa.modulusWords len)
  eRead : InRegions (s.rd ++ s.wr) (byteAddr (args 4)) (args 5).toNat
  inRead : InRegions (s.rd ++ s.wr) (byteAddr (args 6)) len
  outApart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args 0), len⟩
  preApart : Region.Disjoint ⟨byteAddr (args 2), 16 * Spec.Rsa.modulusWords len⟩ ⟨base, bytes⟩
  eApart : Region.Disjoint ⟨byteAddr (args 4), (args 5).toNat⟩ ⟨base, bytes⟩
  inApart : Region.Disjoint ⟨byteAddr (args 6), len⟩ ⟨base, bytes⟩

theorem PrecomputedInputs.keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (h : PrecomputedInputs base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    PrecomputedInputs base bytes len args t := by
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space, h.stack.keep K sp O,
    h.outLen, h.preLen, h.inLen, h.ePositive, h.eBound, h.outFit, h.preFit, h.eFit, h.inFit,
    ?_, ?_, ?_, ?_, h.outApart, h.preApart, h.eApart, h.inApart⟩
  · rw [K.2.2]; exact h.outWrite
  · rw [K.2.1, K.2.2]; exact h.preRead
  · rw [K.2.1, K.2.2]; exact h.eRead
  · rw [K.2.1, K.2.2]; exact h.inRead

theorem PrecomputedInputs.dimensions {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (h : PrecomputedInputs base bytes len args s) :
    0 < Spec.Rsa.modulusWords len ∧ 128 * Spec.Rsa.modulusWords len < 2 ^ 32 ∧
      len ≤ 8 * Spec.Rsa.modulusWords len := by
  have := h.lower
  have := h.upper
  unfold Spec.Rsa.modulusWords
  omega

end VG.Proof.Bignum.X86
