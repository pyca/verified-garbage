module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Base
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # What the pieces of private CRT at a run-time width need of their inputs

`In Ex`: the working space, the eighteen arguments on the stack (the
modulus's length in argument 1), the room for the slots (`need`), the
working space's address and length in arguments 16 and 17, which `edi` is
reloaded from and the calls are given, and facts `Ex` about the regions the
code may read and write, which every operation keeps. Private CRT's are
`CrtExtra` (the output and the key's components), with which `In` is
`Crt.Inputs` (`In.crt`); another caller of the operations states its own.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)

structure In (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat)
    (args : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base bytes
  lower : 64 ≤ len
  upper : len ≤ 1024
  stack : ∀ i, i < 18 → CallArgument s base bytes i (args i)
  outLen : args 1 = BitVec.ofNat 32 len
  room : VG.Proof.Mont.X86.CallRoom (s.gpr .esp) base bytes
  top : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32
  need : need len ≤ bytes
  hbase : (args 16).toNat = base.toNat
  hbytes : bytes = (args 17).toNat * 8
  extra : Ex s.rd s.wr

/-- What private CRT's inputs (`Crt.Inputs`) add to `In`: facts about the arguments and the
regions alone. -/
structure CrtExtra (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (rd wr : List Region) :
    Prop where
  space : VG.Impl.Bignum.X86.Crt.size (Spec.Rsa.modulusWords len) ≤ bytes
  nLen : args 3 = BitVec.ofNat 32 len
  inLen : args 5 = BitVec.ofNat 32 len
  pShort : (args 7).toNat < len
  qShort : (args 9).toNat < len
  dpLen : args 11 = args 7
  dqLen : args 13 = args 9
  qiLen : args 15 = args 7
  outFit : (args 0).toNat + len ≤ 2 ^ 32
  outWrite : InRegions wr (byteAddr (args 0)) len
  outApart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args 0), len⟩
  positive : ∀ i ∈ Crt.componentArguments, 0 < (args (i + 1)).toNat
  bounded : ∀ i ∈ Crt.componentArguments, (args (i + 1)).toNat ≤ len
  fits : ∀ i ∈ Crt.componentArguments, (args i).toNat + (args (i + 1)).toNat ≤ 2 ^ 32
  readable : ∀ i ∈ Crt.componentArguments,
    InRegions (rd ++ wr) (byteAddr (args i)) (args (i + 1)).toNat
  apart : ∀ i ∈ Crt.componentArguments,
    Region.Disjoint ⟨byteAddr (args i), (args (i + 1)).toNat⟩ ⟨base, bytes⟩

/-- Private CRT's `In`. -/
abbrev RIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop :=
  In (CrtExtra base bytes len args) base bytes len args s

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {s t : State}

theorem In.ofInputs (h : Crt.Inputs base bytes len args s) (need : CrtRt.need len ≤ bytes)
    (hbase : (args 16).toNat = base.toNat) (hbytes : bytes = (args 17).toNat * 8) : RIn base bytes len args s :=
  ⟨h.scratch, h.lower, h.upper, h.stack, h.outLen, h.room, h.top, need, hbase, hbytes,
    ⟨h.space, h.nLen, h.inLen, h.pShort, h.qShort, h.dpLen, h.dqLen, h.qiLen, h.outFit, h.outWrite, h.outApart,
      h.positive, h.bounded, h.fits, h.readable, h.apart⟩⟩

theorem In.crt (h : RIn base bytes len args s) : Crt.Inputs base bytes len args s :=
  ⟨h.scratch, h.lower, h.upper, h.extra.space, h.stack, h.outLen, h.extra.nLen, h.extra.inLen, h.extra.pShort,
    h.extra.qShort, h.extra.dpLen, h.extra.dqLen, h.extra.qiLen, h.extra.outFit, h.extra.outWrite,
    h.extra.outApart, h.extra.positive, h.extra.bounded, h.extra.fits, h.extra.readable, h.extra.apart, h.room,
    h.top⟩

theorem In.keep (h : In Ex base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) : In Ex base bytes len args t :=
  ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, fun i hi => (h.stack i hi).keep K sp O, h.outLen,
    by rw [K.1 _ sp]; exact h.room, by rw [K.1 _ sp]; exact h.top, h.need, h.hbase, h.hbytes,
    by rw [K.2.1, K.2.2]; exact h.extra⟩

theorem In.keepZ (h : In Ex base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (O : VG.Proof.Mont.X86.OutsZ base (s.gpr .esp) [(0, bytes)] s.mem t.mem) : In Ex base bytes len args t :=
  ⟨h.scratch.of_keeps K di sp, h.lower, h.upper,
    fun i hi => ⟨(h.stack i hi).stack.keep K sp,
      (Crt.stackValue_keepZ (h.stack i hi).stack K sp hi h.top (by have := h.room.low; omega) O).trans
        (h.stack i hi).value⟩, h.outLen,
    by rw [K.1 _ sp]; exact h.room, by rw [K.1 _ sp]; exact h.top, h.need, h.hbase, h.hbytes,
    by rw [K.2.1, K.2.2]; exact h.extra⟩

theorem In.ws (h : In Ex base bytes len args s) : Ws s base bytes :=
  ⟨h.scratch.wr, h.scratch.nowrap⟩

theorem In.width (h : In Ex base bytes len args s) : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len) := by
  have := (h.stack 1 (by decide)).readSrc
  rw [h.outLen] at this
  exact this

theorem In.arg (h : In Ex base bytes len args s) {i : Nat} (hi : i < 18) :
    readSrc s (.mem (argAt 0 i)) = some (args i) :=
  (h.stack i hi).readSrc

theorem In.edi (h : In Ex base bytes len args s) : (s.gpr .edi).toNat = base.toNat :=
  h.scratch.edi_toNat

theorem In.edi_eq (h : In Ex base bytes len args s) : args 16 = s.gpr .edi :=
  BitVec.eq_of_toNat_eq (h.hbase.trans h.edi.symm)

theorem In.lower' (h : In Ex base bytes len args s) : 64 ≤ len := h.lower
theorem In.upper' (h : In Ex base bytes len args s) : len ≤ 1024 := h.upper

theorem In.bytes_lt (h : In Ex base bytes len args s) : bytes < 2 ^ 32 := h.scratch.size_lt

/-- A slot of a context, and the next, within the working space. -/
theorem In.slot_fit (h : In Ex base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 27) :
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
theorem In.prod_fit (h : In Ex base bytes len args s) : prodOff + (2 * bc len .wide + 4) ≤ mulAOff ∧
    mulAOff + bc len .wide ≤ numBase ∧ numBase ≤ bytes := by
  have := bc_le h.upper' .wide
  have hn := h.need
  unfold CrtRt.need at hn
  simp only [prodOff, mulAOff, numBase] at *
  omega

end

end VG.Proof.Bignum.X86.CrtRt
