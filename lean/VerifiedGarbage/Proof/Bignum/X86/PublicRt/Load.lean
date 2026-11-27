module

public import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Bignum.X86.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
public import VerifiedGarbage.Proof.Bignum.X86.LoadBE

/-! ### `Bignum.X86.PublicRt.Stages`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.PublicRt.In`, which only this module used -/

section

/-! # What the pieces of public RSA at a run-time width need of their inputs

The working space, the arguments on the stack, the output and the input:
what `PrecomputedInputs` needs of them (`RtIn`). The width of the numbers
is read from `out_len` (argument 1), which is the modulus's length.
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
  omega_arith

end

end VG.Proof.Bignum.X86.PublicRt

end

end


/-! # The stages of public RSA at a run-time width

From `RtIn`: number `j` zeroed (`zero_ok`), set to one
(`setOne_ok`), read from the bytes of an argument (`load_ok`); the input
compared with the modulus (`compare_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The words of a number: `2 ⌈len / 8⌉`. -/
abbrev nw (len : Nat) : Nat := 2 * Spec.Rsa.modulusWords len

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem wb_eq (len : Nat) : wb len = 4 * nw len := by simp only [wb, nw]; omega_using []

theorem RtIn.ws (h : RtIn base bytes len args s) : Ws s base bytes :=
  ⟨h.scratch.wr, h.scratch.nowrap⟩

theorem RtIn.width (h : RtIn base bytes len args s) :
    readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len) := by
  have := (h.stack 1 (by decide)).readSrc
  rw [h.outLen] at this
  exact this

theorem RtIn.edi (h : RtIn base bytes len args s) : (s.gpr .edi).toNat = base.toNat :=
  h.scratch.edi_toNat

/-- Every number, and the multiplication's range after them, within the working space. -/
theorem RtIn.fits (h : RtIn base bytes len args s) {j : Nat} (hj : j ≤ 7) :
    numAt len j + wb len ≤ bytes ∧ numAt len 5 + (3 * wb len + 56) ≤ bytes := by
  have sp := h.space
  have := h.upper
  have := Nat.mul_le_mul_right (wb len) hj
  simp only [VG.Impl.Bignum.X86.PublicContext.size, VG.Impl.Bignum.X86.PublicContext.slot,
    VG.Impl.Bignum.X86.PublicContext.stride, VG.Impl.Bignum.hdrBytes] at sp
  simp only [numAt, numOff, wb] at *
  omega_using [sp, this]

end

/-! ## Zeroing and one -/

theorem zero_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) {j : Nat} (hj : j ≤ 7) :
    WP isa (zero j) s fun u => Outside base (numAt len j) (wb len) s.mem u.mem ∧
      val32 u.mem base (numAt len j) (nw len) = 0 ∧ Keeps [.eax, .ecx, .ebp] s u := by
  have fit := (h.fits hj).1
  have := h.dimensions
  unfold zero
  refine WP.seq (slotPtr_ok (r := .ebp) (t := .ecx) (by decide) (by decide) h.edi h.width h.upper (by omega_using [hj])
    fun u K m p c => wp_movS rfl fun u₁ up _ => WP.block_nil ?_)
  have p₁ : PtrAt u₁ base .ebp (numAt len j) := by rw [PtrAt, up.other _ (by decide)]; exact p
  have c₁ : (u₁.gpr .ecx).toNat = 4 * nw len := by
    rw [up.other _ (by decide), c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := wb_le h.upper; omega_using [this]),
      wb_eq]
  have K₁ : Keeps [.eax, .ecx, .ebp] s u₁ := (K.mono (by decide)).trans (up.keeps.mono (by decide))
  refine WP.mono (zeroLoop_ok (h.ws.of_keeps K₁) (N := nw len) (by simp only [nw]; omega_using [this])
    (by rw [← wb_eq]; exact fit) p₁ c₁ up.gpr) fun t ⟨O, V, Kt⟩ => ⟨?_, V, K₁.trans (Kt.mono (by decide))⟩
  rw [up.mem, m] at O
  rwa [wb_eq]

theorem setOne_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) {j : Nat} (hj : j ≤ 7) :
    WP isa (setOne j) s fun u => Outside base (numAt len j) (wb len) s.mem u.mem ∧
      val32 u.mem base (numAt len j) (nw len) = 1 ∧ Keeps [.eax, .ecx, .ebp] s u := by
  have fit := (h.fits hj).1
  have := h.dimensions
  have hn := h.scratch.nowrap
  unfold setOne
  refine WP.seq (WP.mono (zero_ok h hj) fun u ⟨O, V, K⟩ => ?_)
  have hu := h.ws.of_keeps K
  have edi : (u.gpr .edi).toNat = base.toNat := by rw [K.1 _ (by decide)]; exact h.edi
  have wd : readSrc u (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len) := by
    have := ((h.stack 1 (by decide)).keep K (by decide) (O.mono (Nat.zero_le _) (by omega_using [fit]))).readSrc
    rw [h.outLen] at this; exact this
  refine slotPtr_ok (r := .eax) (t := .ecx) (by decide) (by decide) edi wd h.upper (by omega_using [hj])
    fun v Kv mv pv _ => wp_movS rfl fun v₁ u₁ _ => ?_
  have hv₁ := hu.of_keeps (Kv.trans (u₁.keeps.mono (by decide)))
  have p₁ : PtrAt v₁ base .eax (numAt len j) := by rw [PtrAt, u₁.other _ (by decide)]; exact pv
  refine wp_storeS (ea_ptr hv₁ p₁ (d := 0) (by have := wb_ge h.lower; omega_using [fit, this]))
    (ws_write hv₁ (y := numAt len j + 0) (n := 4) (by have := wb_ge h.lower; omega_using [fit, this])) fun w m => WP.block_nil ?_
  have Kw : Keeps [.eax, .ecx, .ebp] s w :=
    (K.trans ((Kv.mono (by decide)).trans (u₁.keeps.mono (by decide)))).trans (m.keeps _)
  have mv₁ : v₁.mem = u.mem := by rw [u₁.mem, mv]
  have hN : 0 < nw len := by simp only [nw]; omega_using [this]
  refine ⟨?_, ?_, Kw⟩
  · rw [m.mem, mv₁, Nat.add_zero]
    exact O.trans ((writeW32_outside _ _ _ (by omega_using [fit, hn])).mono (by omega_using []) (by have := wb_ge h.lower; omega_using [this]))
  · -- Word 0 is one; the others stay zero.
    rw [m.mem, mv₁, Nat.add_zero, u₁.gpr]
    obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by omega_using [hN]⟩
    rw [hk] at V ⊢
    have V' := V
    rw [val32] at V'
    rw [val32, w32_write_self]
    have rest : val32 (u.mem.writeW (off base (numAt len j)) 1) base (numAt len j + 4) k =
        val32 u.mem base (numAt len j + 4) k :=
      (writeW32_outside u.mem base 1 (by omega_using [fit, hn])).val32 (by omega_using []) (by have := wb_eq len; omega_using [fit, hn, hk, this])
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [rest, e1]
    omega_using [V']

end VG.Proof.Bignum.X86.PublicRt

end

end

/-! # Reading a number of public RSA at a run-time width

`load j p l`: number `j` is the big-endian bytes at argument `p`, as many as
argument `l` says (`load_ok`), as `loadBE_ok` at a fixed offset.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- A register holding `W + x`, below `2³²`, as an address. -/
theorem byteAddr_ptr {s : State} {W : Addr} {r : Reg} {x : Nat} (hp : PtrAt s W r x)
    (hx : W.toNat + x < 2 ^ 32) : byteAddr (s.gpr r) = off W x := by
  apply BitVec.eq_of_toNat_eq
  have hW : W.toNat < 2 ^ 64 := W.isLt
  simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (s.gpr r).toNat) (by have := (s.gpr r).isLt; omega_using []), hp,
    Nat.mod_eq_of_lt (a := W.toNat + x) hx, Nat.mod_eq_of_lt (a := x) (by omega_using [hx]), Nat.mod_eq_of_lt (by omega_using [hx])]

theorem load_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) {j p l : Nat} (hj : j ≤ 7) (hp : p < 10) (hl : l < 10)
    (hlen : args l = BitVec.ofNat 32 len) (fit : (args p).toNat + len ≤ 2 ^ 32)
    (rd : InRegions (s.rd ++ s.wr) (byteAddr (args p)) len)
    (apart : Region.Disjoint ⟨byteAddr (args p), len⟩ ⟨base, bytes⟩) :
    WP isa (load j p l) s fun t =>
      val32 t.mem base (numAt len j) (nw len) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args p)) len) ∧
      Outside base (numAt len j) (wb len) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .ebp, .esi] s t := by
  obtain fit' := (h.fits hj).1
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  obtain wbl := wb_le h.upper
  obtain wbg := len_le_wb len
  obtain wbe := wb_eq len
  have hlow := h.lower
  obtain srcLen : len < 2 ^ 32 := by omega_using [dims]
  unfold load
  refine WP.seq (WP.mono (zero_ok h hj) fun u ⟨O, Z, K⟩ => ?_)
  obtain Ou : Outside base 0 bytes s.mem u.mem := O.mono (Nat.zero_le _) (by omega_using [fit'])
  obtain hu := h.keep K (by decide) (by decide) Ou
  refine WP.seq (slotPtr_ok (r := .ebx) (t := .ecx) (by decide) (by decide) hu.edi hu.width h.upper (by omega_using [hj])
    fun v Kv mv pv _ => ?_)
  obtain hv := hu.keep Kv (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
  refine wp_movS (hv.stack p hp).readSrc fun v₁ u₁ _ => ?_
  obtain hv₁ := hv.keep u₁.keeps (by decide) (by decide) (by rw [u₁.mem]; exact Outside.refl _ _ _ _)
  refine wp_movS (hv₁.stack l hl).readSrc fun v₂ u₂ _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  let dst := v.gpr .ebx
  obtain dstAddr : byteAddr dst = off base (numAt len j) := byteAddr_ptr pv (by omega_using [fit', nw', wbg, hlow])
  obtain dstNat : dst.toNat = base.toNat + numAt len j := by
    show (v.gpr .ebx).toNat = _; rw [pv, Nat.mod_eq_of_lt (by omega_using [fit', nw', wbg, hlow])]
  obtain K₄ : Keeps [.ebx, .ecx, .esi] v v₄ :=
    (((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))
  obtain m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, mv]
  obtain ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 len := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hlen]
  obtain ebx₄ : v₄.gpr .ebx = dst := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain esi₄ : v₄.gpr .esi = args p + BitVec.ofNat 32 (len - 1) := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, hlen]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hlow])]
  obtain keep : Keeps [.eax, .ebx, .ecx, .ebp, .esi] s v₄ :=
    (K.mono (by decide)).trans ((Kv.mono (by decide)).trans (K₄.mono (by decide)))
  obtain vr : InRegions (v₄.rd ++ v₄.wr) (byteAddr (args p)) len := by rw [keep.2.1, keep.2.2]; exact rd
  obtain vw : InRegions v₄.wr (byteAddr dst) len := by
    rw [keep.2.2, dstAddr]; exact h.scratch.write (by omega_using [fit', wbg])
  obtain hsub : Region.Sub ⟨off base (numAt len j), len⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := numAt len j) (n := len) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [fit', wbg])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  obtain hd : Region.Disjoint ⟨byteAddr (args p), len⟩ ⟨off base (numAt len j), len⟩ := apart.sub_right hsub
  obtain ctx := reverseCtx_of_regions v₄ (args p) dst srcLen fit (by omega_using [fit', nw', wbg, dstNat]) vr vw (by rw [dstAddr]; exact hd)
  refine WP.mono (reverseBytes_ok v₄ ctx (by omega_using [hlow]) esi₄ ebx₄ ecx₄) fun t I => ?_
  obtain Ot : Outside base (numAt len j) (wb len) v₄.mem t.mem := by
    intro a ha
    apply I.outside a
    intro k hk he
    obtain ek : ofs base a = numAt len j + k := by
      rw [he, byteAddr_add (by omega_using [fit', nw', wbg, dstNat, hk]), dstAddr]
      exact ofs_off base (by omega_using [fit, fit', nw', hk])
    omega_arith
  obtain Ov : Outside base (numAt len j) (wb len) s.mem v₄.mem := by rw [m₄]; exact O
  obtain input : Spec.Rsa.bytesAt v₄.mem (byteAddr (args p)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args p)) len :=
    VG.Proof.Bignum.scratch_bytes (Ou.trans (by rw [m₄]; exact Outside.refl _ _ _ _)) (by omega_using [fit]) apart
  obtain padding : ∀ k, len ≤ k → k < wb len → t.mem (off base (numAt len j) + BitVec.ofNat 64 k) = 0 := by
    intro k hk hkn
    rw [I.outside _ ?_, m₄]
    · exact byte_zero_of_val32 Z (by omega_using [wbe, hkn])
    · intro i hi he
      rw [byteAddr_add (by omega_using [fit', nw', wbg, dstNat, hi]), dstAddr] at he
      obtain e := congrArg (fun a => (a - off base (numAt len j)).toNat) he
      rw [Mem.sub_ofNat_toNat _ (by omega_using [wbl, hkn] : k < 2 ^ 64), Mem.sub_ofNat_toNat _ (by omega_using [fit, hi] : i < 2 ^ 64)] at e
      omega_arith
  refine ⟨?_, Ov.trans Ot, keep.trans (I.rest.mono (by decide))⟩
  obtain value := I.os2ip fit (by omega_using [fit', nw', wbg, dstNat] : dst.toNat + len ≤ 2 ^ 32)
  rw [dstAddr, input] at value
  rw [← read_eq_val32]
  obtain ext := val32_zero_extension t.mem (off base (numAt len j)) (n := nw len) (by omega_using [wbg, wbe] : len ≤ 4 * nw len)
    (by intro k hk hkn; exact padding k hk (by omega_using [wbe, hkn]))
  rw [← read_eq_val32] at ext
  simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ext.trans value

end VG.Proof.Bignum.X86.PublicRt
