module
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract


/-! # Six-argument geometry for the public RSA precomputation call -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

structure PrecomputeInputs (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base bytes
  lower : 64 ≤ len
  upper : len ≤ 1024
  space : size (Spec.Rsa.modulusWords len) ≤ bytes
  stack : ∀ i, i < 6 → CallArgument s base bytes i (args i)
  preLen : args 1 = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords len)
  nLen : args 3 = BitVec.ofNat 32 len
  outFit : (args 0).toNat + 16 * Spec.Rsa.modulusWords len ≤ 2 ^ 32
  nFit : (args 2).toNat + len ≤ 2 ^ 32
  outWrite : InRegions s.wr (byteAddr (args 0)) (16 * Spec.Rsa.modulusWords len)
  nRead : InRegions (s.rd ++ s.wr) (byteAddr (args 2)) len
  outApart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args 0), 16 * Spec.Rsa.modulusWords len⟩
  nApart : Region.Disjoint ⟨byteAddr (args 2), len⟩ ⟨base, bytes⟩
  room : CallRoom (s.gpr .esp) base bytes
  top : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  hbase : (args 4).toNat = base.toNat
  hbytes : bytes = (args 5).toNat * 8
  argWrite : InRegions s.wr (VG.Proof.Dsa.X86.stackAddress s 1) 4
  nArg : Region.Disjoint ⟨byteAddr (args 2), len⟩ ⟨VG.Proof.Dsa.X86.stackAddress s 1, 4⟩
  outArgs : Region.Disjoint ⟨byteAddr (args 0), 16 * Spec.Rsa.modulusWords len⟩ ⟨argAddr s 0, 24⟩
  spScratch : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 28⟩ ⟨base, bytes⟩
  spOut : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 28⟩ ⟨byteAddr (args 0), 16 * Spec.Rsa.modulusWords len⟩

theorem PrecomputeInputs.keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (h : PrecomputeInputs base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    PrecomputeInputs base bytes len args t := by
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  have sa : VG.Proof.Dsa.X86.stackAddress t 1 = VG.Proof.Dsa.X86.stackAddress s 1 := by
    simp only [VG.Proof.Dsa.X86.stackAddress, esp]
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space,
    fun i hi => (h.stack i hi).keep K sp O, h.preLen, h.nLen, h.outFit, h.nFit,
    ?_, ?_, h.outApart, h.nApart, by rw [esp]; exact h.room, by rw [esp]; exact h.top, h.hbase, h.hbytes,
    by rw [K.2.2, sa]; exact h.argWrite, by rw [sa]; exact h.nArg, by simp only [argAddr, esp]; exact h.outArgs,
    by rw [esp]; exact h.spScratch, by rw [esp]; exact h.spOut⟩
  · rw [K.2.2]; exact h.outWrite
  · rw [K.2.1, K.2.2]; exact h.nRead

theorem PrecomputeInputs.dimensions {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State}
    (h : PrecomputeInputs base bytes len args s) :
    0 < Spec.Rsa.modulusWords len ∧ 128 * Spec.Rsa.modulusWords len < 2 ^ 32 ∧
      len ≤ 8 * Spec.Rsa.modulusWords len := by
  have := h.lower
  have := h.upper
  unfold Spec.Rsa.modulusWords
  omega

end VG.Proof.Bignum.X86
