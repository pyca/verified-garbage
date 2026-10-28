module

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Impl.Bignum.X86.PublicRt
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
public import VerifiedGarbage.Proof.Mont.Words32

/-! # What the precomputation at a run-time width needs of its inputs

`PcIn`: the working space at `edi` (`args 4`, of `args 5` words), the six
arguments on the stack, `args 1` the modulus's length (to which the
computation sets it, the width `PublicRt`'s loops read) as `args 3` is, the
`2 B` writable bytes of `pre` and the readable modulus, apart from the
working space. From it, number `j` zeroed (`zero_ok`) or read from the
bytes of an argument (`load_ok`), as `PublicRt`'s.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputeRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt

structure PcIn (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base bytes
  lower : 64 ≤ len
  upper : len ≤ 1024
  space : PublicContext.size (Spec.Rsa.modulusWords len) ≤ bytes
  stack : ∀ i, i < 6 → CallArgument s base bytes i (args i)
  wLen : args 1 = BitVec.ofNat 32 len
  nLen : args 3 = BitVec.ofNat 32 len
  hbase : (args 4).toNat = base.toNat
  hbytes : bytes = (args 5).toNat * 8
  outFit : (args 0).toNat + 2 * wb len ≤ 2 ^ 32
  nFit : (args 2).toNat + len ≤ 2 ^ 32
  outWrite : InRegions s.wr (byteAddr (args 0)) (2 * wb len)
  nRead : InRegions (s.rd ++ s.wr) (byteAddr (args 2)) len
  outApart : Region.Disjoint ⟨byteAddr (args 0), 2 * wb len⟩ ⟨base, bytes⟩
  nApart : Region.Disjoint ⟨byteAddr (args 2), len⟩ ⟨base, bytes⟩
  outArgs : Region.Disjoint ⟨byteAddr (args 0), 2 * wb len⟩ ⟨argAddr s 0, 24⟩

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem PcIn.keep (h : PcIn base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) : PcIn base bytes len args t :=
  ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, h.space, fun i hi => (h.stack i hi).keep K sp O, h.wLen, h.nLen,
    h.hbase, h.hbytes, h.outFit, h.nFit, by rw [K.2.2]; exact h.outWrite, by rw [K.2.1, K.2.2]; exact h.nRead,
    h.outApart, h.nApart, by simp only [argAddr, K.1 _ sp]; exact h.outArgs⟩

theorem PcIn.dimensions (h : PcIn base bytes len args s) :
    0 < Spec.Rsa.modulusWords len ∧ 128 * Spec.Rsa.modulusWords len < 2 ^ 32 ∧
      len ≤ 8 * Spec.Rsa.modulusWords len := by
  have := h.lower
  have := h.upper
  unfold Spec.Rsa.modulusWords
  omega

theorem PcIn.ws (h : PcIn base bytes len args s) : Ws s base bytes :=
  ⟨h.scratch.wr, h.scratch.nowrap⟩

theorem PcIn.width (h : PcIn base bytes len args s) :
    readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len) := by
  have := (h.stack 1 (by decide)).readSrc
  rw [h.wLen] at this
  exact this

theorem PcIn.edi (h : PcIn base bytes len args s) : (s.gpr .edi).toNat = base.toNat :=
  h.scratch.edi_toNat

theorem PcIn.edi_eq (h : PcIn base bytes len args s) : args 4 = s.gpr .edi :=
  BitVec.eq_of_toNat_eq (h.hbase.trans h.edi.symm)

/-- Every number, and the multiplication's range after them, within the working space. -/
theorem PcIn.fits (h : PcIn base bytes len args s) {j : Nat} (hj : j ≤ 7) :
    numAt len j + wb len ≤ bytes ∧ numAt len 5 + (3 * wb len + 56) ≤ bytes := by
  have sp := h.space
  have := h.upper
  have := Nat.mul_le_mul_right (wb len) hj
  simp only [VG.Impl.Bignum.X86.PublicContext.size, VG.Impl.Bignum.X86.PublicContext.slot,
    VG.Impl.Bignum.X86.PublicContext.stride, VG.Impl.Bignum.hdrBytes] at sp
  simp only [numAt, numOff, wb] at *
  omega

end

/-! ## Zeroing and reading -/

theorem zero_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) {j : Nat} (hj : j ≤ 7) :
    WP isa (zero j) s fun u => Outside base (numAt len j) (wb len) s.mem u.mem ∧
      val32 u.mem base (numAt len j) (nw len) = 0 ∧ Keeps [.eax, .ecx, .ebp] s u := by
  have fit := (h.fits hj).1
  have := h.dimensions
  unfold zero
  refine WP.seq (slotPtr_ok (r := .ebp) (t := .ecx) (by decide) (by decide) h.edi h.width h.upper (by omega)
    fun u K m p c => wp_movS rfl fun u₁ up _ => WP.block_nil ?_)
  have p₁ : PtrAt u₁ base .ebp (numAt len j) := by rw [PtrAt, up.other _ (by decide)]; exact p
  have c₁ : (u₁.gpr .ecx).toNat = 4 * nw len := by
    rw [up.other _ (by decide), c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wb_le h.upper; omega),
      wb_eq]
  have K₁ : Keeps [.eax, .ecx, .ebp] s u₁ := (K.mono (by decide)).trans (up.keeps.mono (by decide))
  refine WP.mono (zeroLoop_ok (h.ws.of_keeps K₁) (N := nw len) (by simp only [nw]; omega)
    (by rw [← wb_eq]; exact fit) p₁ c₁ up.gpr) fun t ⟨O, V, Kt⟩ => ⟨?_, V, K₁.trans (Kt.mono (by decide))⟩
  rw [up.mem, m] at O
  rwa [wb_eq]

theorem load_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PcIn base bytes len args s) {j : Nat} (hj : j ≤ 7) :
    WP isa (load j 2 3) s fun t =>
      val32 t.mem base (numAt len j) (nw len) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) ∧
      Outside base (numAt len j) (wb len) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .ebp, .esi] s t := by
  have fit' := (h.fits hj).1
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have wbl := wb_le h.upper
  have wbg := len_le_wb len
  have wbe := wb_eq len
  have hlow := h.lower
  have fit := h.nFit
  have rd := h.nRead
  have apart := h.nApart
  have srcLen : len < 2 ^ 32 := by omega
  unfold load
  refine WP.seq (WP.mono (zero_ok h hj) fun u ⟨O, Z, K⟩ => ?_)
  have Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega)
  have hu := h.keep K (by decide) (by decide) Ou
  refine WP.seq (slotPtr_ok (r := .ebx) (t := .ecx) (by decide) (by decide) hu.edi hu.width h.upper (by omega)
    fun v Kv mv pv _ => ?_)
  have hv := hu.keep Kv (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
  refine wp_movS (hv.stack 2 (by decide)).readSrc fun v₁ u₁ _ => ?_
  have hv₁ := hv.keep u₁.keeps (by decide) (by decide) (by rw [u₁.mem]; exact Outside.refl _ _ _ _)
  refine wp_movS (hv₁.stack 3 (by decide)).readSrc fun v₂ u₂ _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  let dst := v.gpr .ebx
  have dstAddr : byteAddr dst = off base (numAt len j) := byteAddr_ptr pv (by omega)
  have dstNat : dst.toNat = base.toNat + numAt len j := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega)]
  have K₄ : Keeps [.ebx, .ecx, .esi] v v₄ :=
    (((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))
  have m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, mv]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 len := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h.nLen]
  have ebx₄ : v₄.gpr .ebx = dst := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have esi₄ : v₄.gpr .esi = args 2 + BitVec.ofNat 32 (len - 1) := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, h.nLen]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keep : Keeps [.eax, .ebx, .ecx, .ebp, .esi] s v₄ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  have vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (args 2)) len := by rw [keep.2.1, keep.2.2]; exact rd
  have vw : InRegions v₄.wr (byteAddr dst) len := by
    rw [keep.2.2, dstAddr]; exact h.scratch.write (by omega)
  have hsub : Region.Sub ⟨off base (numAt len j), len⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := numAt len j) (n := len) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  have hd : Region.Disjoint ⟨byteAddr (args 2), len⟩ ⟨off base (numAt len j), len⟩ := apart.sub_right hsub
  have ctx := reverseCtx_of_regions v₄ (args 2) dst srcLen fit (by omega) vr vw (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v₄ ctx (by omega) esi₄ ebx₄ ecx₄) fun t I => ?_
  have Ot : Outside base (numAt len j) (wb len) v₄.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    have ek : ofs base a = numAt len j + k := by
      rw [he, byteAddr_add (by omega), dstAddr]
      exact ofs_off base (by omega)
    omega
  have Ov : Outside base (numAt len j) (wb len) s.mem v₄.mem := by rw [m₄]; exact O
  have input : Spec.Rsa.bytesAt v₄.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len :=
    VG.Proof.Bignum.scratch_bytes (Ou.trans (by rw [m₄]; exact Outside.refl _ _ _ _)) (by omega) apart
  have padding : ∀ k, len ≤ k → k < wb len → t.mem (off base (numAt len j) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₄]
    · exact byte_zero_of_val32 Z (by omega)
    · intro i hi he
      rw [byteAddr_add (by omega), dstAddr] at he
      have e := congrArg (fun a => (a - off base (numAt len j)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64)] at e
      omega
  refine ⟨?_, Ov.trans Ot, keep.trans (I.rest.mono (by decide))⟩
  have value := I.os2ip fit (by omega : dst.toNat + len ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  rw [← read_eq_val32]
  have ext := val32_zero_extension t.mem (off base (numAt len j)) (n := nw len) (by omega : len ≤ 4 * nw len)
    (by intro k hk hkn; exact padding k hk (by omega))
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

end VG.Proof.Bignum.X86.PrecomputeRt
