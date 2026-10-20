module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.X86.State
public import Init.Data.List.Basic
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Stable resources for all eighteen private CRT arguments -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Dsa.X86

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
  room : VG.Proof.Mont.X86.CallRoom (s.gpr .esp) base bytes
  top : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32

theorem Inputs.keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (h : Inputs base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    Inputs base bytes len args t := by
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space,
    fun i hi => (h.stack i hi).keep K sp O, h.outLen, h.nLen, h.inLen,
    h.pShort, h.qShort, h.dpLen, h.dqLen, h.qiLen, h.outFit, ?_, h.outApart,
    h.positive, h.bounded, h.fits, ?_, h.apart, by rw [K.1 _ sp]; exact h.room, by rw [K.1 _ sp]; exact h.top⟩
  · rw [K.2.2]; exact h.outWrite
  · intro i hi; rw [K.2.1, K.2.2]; exact h.readable i hi

/-- A stack argument lies above the zone a call writes below `sp`. -/
theorem stackValue_keepZ {s t : State} {base : Addr} {bytes i : Nat} {regs : List Reg}
    (A : StackArgument s base bytes i) (K : Keeps regs s t) (hsp : .esp ∉ regs)
    (hi : i < 18) (top : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32) (low : 20 ≤ (s.gpr .esp).toNat)
    (O : VG.Proof.Mont.X86.OutsZ base (s.gpr .esp) [(0, bytes)] s.mem t.mem) :
    stackValue t i = stackValue s i := by
  unfold stackValue
  rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, K.1 _ hsp]]
  apply Mem.readW_congr
  intro j hj
  have H := A.apart (stackAddress s i + BitVec.ofNat 64 j)
    (Offset.contains_base _ (by omega) (by omega))
  change ¬ (ofs base (stackAddress s i + BitVec.ofNat 64 j) + 1 ≤ bytes) at H
  refine O _ (fun r hr => ?_) ?_
  · obtain rfl := List.mem_singleton.mp hr
    exact .inr (by simp only; omega)
  · simp only [Region.Contains, stackAddress, addr]
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

theorem Inputs.keepZ {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (h : Inputs base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (O : VG.Proof.Mont.X86.OutsZ base (s.gpr .esp) [(0, bytes)] s.mem t.mem) :
    Inputs base bytes len args t := by
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space,
    fun i hi => ⟨(h.stack i hi).stack.keep K sp,
      (stackValue_keepZ (h.stack i hi).stack K sp hi h.top (by have := h.room.low; omega) O).trans
        (h.stack i hi).value⟩, h.outLen, h.nLen, h.inLen,
    h.pShort, h.qShort, h.dpLen, h.dqLen, h.qiLen, h.outFit, ?_, h.outApart,
    h.positive, h.bounded, h.fits, ?_, h.apart, by rw [K.1 _ sp]; exact h.room, by rw [K.1 _ sp]; exact h.top⟩
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
