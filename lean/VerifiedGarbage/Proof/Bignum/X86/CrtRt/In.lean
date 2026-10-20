module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Base
import VerifiedGarbage.Proof.Framework.Omega

/-! # What the pieces of private CRT at a run-time width need of their inputs

`Crt.Inputs` (the working space, the eighteen arguments, the output and the
key's components), the room for the slots (`need`), and the working space's
address and length in arguments 16 and 17, which `edi` is reloaded from and
the calls are given.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)

structure In (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  crt : Crt.Inputs base bytes len args s
  need : need len ≤ bytes
  hbase : (args 16).toNat = base.toNat
  hbytes : bytes = (args 17).toNat * 8

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}

theorem In.keep (h : In base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) : In base bytes len args t :=
  ⟨h.crt.keep K di sp O, h.need, h.hbase, h.hbytes⟩

theorem In.keepZ (h : In base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (O : VG.Proof.Mont.X86.OutsZ base (s.gpr .esp) [(0, bytes)] s.mem t.mem) : In base bytes len args t :=
  ⟨h.crt.keepZ K di sp O, h.need, h.hbase, h.hbytes⟩

theorem In.ws (h : In base bytes len args s) : Ws s base bytes :=
  ⟨h.crt.scratch.wr, h.crt.scratch.nowrap⟩

theorem In.width (h : In base bytes len args s) : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len) := by
  have := (h.crt.stack 1 (by decide)).readSrc
  rw [h.crt.outLen] at this
  exact this

theorem In.arg (h : In base bytes len args s) {i : Nat} (hi : i < 18) :
    readSrc s (.mem (argAt 0 i)) = some (args i) :=
  (h.crt.stack i hi).readSrc

theorem In.edi (h : In base bytes len args s) : (s.gpr .edi).toNat = base.toNat :=
  h.crt.scratch.edi_toNat

theorem In.edi_eq (h : In base bytes len args s) : args 16 = s.gpr .edi :=
  BitVec.eq_of_toNat_eq (h.hbase.trans h.edi.symm)

theorem In.lower' (h : In base bytes len args s) : 64 ≤ len := h.crt.lower
theorem In.upper' (h : In base bytes len args s) : len ≤ 1024 := h.crt.upper

theorem In.bytes_lt (h : In base bytes len args s) : bytes < 2 ^ 32 := h.crt.scratch.size_lt

/-- A slot of a context, and the next, within the working space. -/
theorem In.slot_fit (h : In base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 27) :
    lo len (.slot c j) + st len c ≤ bytes := by
  have hn := h.need
  have hb := bc_half_le' len
  have hg := bc_ge h.lower' .wide
  have hst : st len c ≤ st len .wide := by cases c <;> simp only [st] <;> omega
  have : j * st len c ≤ 27 * st len .wide := Nat.mul_le_mul hj hst
  unfold CrtRt.need at hn
  simp only [lo] at *
  omega

/-- The product and its multiplicand within the header's bytes. -/
theorem In.prod_fit (h : In base bytes len args s) : prodOff + (2 * bc len .wide + 4) ≤ mulAOff ∧
    mulAOff + bc len .wide ≤ numBase ∧ numBase ≤ bytes := by
  have := bc_le h.upper' .wide
  have hn := h.need
  unfold CrtRt.need at hn
  simp only [prodOff, mulAOff, numBase] at *
  omega

end

end VG.Proof.Bignum.X86.CrtRt
