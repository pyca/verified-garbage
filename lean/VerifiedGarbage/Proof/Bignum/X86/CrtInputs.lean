module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

/-! # Stable resources for all eighteen private CRT arguments -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86.Crt

def componentArguments : List Nat := [2, 4, 6, 8, 10, 12, 14]

structure Inputs (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base bytes
  lower : 64 ≤ len
  upper : len ≤ 1024
  space : size (Spec.Rsa.modulusWords len) ≤ bytes
  stack : ∀ i, i < 18 → CallArgument s base bytes i (args i)
  outLen : args 1 = BitVec.ofNat 32 len
  nLen : args 3 = BitVec.ofNat 32 len
  inLen : args 5 = BitVec.ofNat 32 len
  pShort : (args 7).toNat < len
  qShort : (args 9).toNat < len
  dpLen : args 11 = args 7
  dqLen : args 13 = args 9
  qiLen : args 15 = args 7
  outFit : (args 0).toNat + len ≤ 2 ^ 32
  outWrite : InRegions s.wr (byteAddr (args 0)) len
  outApart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args 0), len⟩
  positive : ∀ i ∈ componentArguments, 0 < (args (i + 1)).toNat
  bounded : ∀ i ∈ componentArguments, (args (i + 1)).toNat ≤ len
  fits : ∀ i ∈ componentArguments, (args i).toNat + (args (i + 1)).toNat ≤ 2 ^ 32
  readable : ∀ i ∈ componentArguments,
    InRegions (s.rd ++ s.wr) (byteAddr (args i)) (args (i + 1)).toNat
  apart : ∀ i ∈ componentArguments,
    Region.Disjoint ⟨byteAddr (args i), (args (i + 1)).toNat⟩ ⟨base, bytes⟩

theorem Inputs.keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (h : Inputs base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    Inputs base bytes len args t := by
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space,
    fun i hi => (h.stack i hi).keep K sp O, h.outLen, h.nLen, h.inLen,
    h.pShort, h.qShort, h.dpLen, h.dqLen, h.qiLen, h.outFit, ?_, h.outApart,
    h.positive, h.bounded, h.fits, ?_, h.apart⟩
  · rw [K.2.2]; exact h.outWrite
  · intro i hi; rw [K.2.1, K.2.2]; exact h.readable i hi

theorem Inputs.dimensions {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (h : Inputs base bytes len args s) :
    0 < Spec.Rsa.modulusWords len ∧ 128 * Spec.Rsa.modulusWords len < 2 ^ 32 ∧
      len ≤ 8 * Spec.Rsa.modulusWords len := by
  have := h.lower
  have := h.upper
  unfold Spec.Rsa.modulusWords
  omega

end VG.Proof.Bignum.X86.Crt
