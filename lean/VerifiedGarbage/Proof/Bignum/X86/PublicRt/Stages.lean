module

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.In
import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

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

theorem wb_eq (len : Nat) : wb len = 4 * nw len := by simp only [wb, nw]; omega

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
  omega

theorem RtIn.bytes_lt (h : RtIn base bytes len args s) : bytes < 2 ^ 32 :=
  h.scratch.size_lt

end

/-! ## Zeroing and one -/

theorem zero_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) {j : Nat} (hj : j ≤ 7) :
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
    have := ((h.stack 1 (by decide)).keep K (by decide) (O.mono (Nat.zero_le _) (by omega))).readSrc
    rw [h.outLen] at this; exact this
  refine slotPtr_ok (r := .eax) (t := .ecx) (by decide) (by decide) edi wd h.upper (by omega)
    fun v Kv mv pv _ => wp_movS rfl fun v₁ u₁ _ => ?_
  have hv₁ := hu.of_keeps (Kv.trans (u₁.keeps.mono (by decide)))
  have p₁ : PtrAt v₁ base .eax (numAt len j) := by rw [PtrAt, u₁.other _ (by decide)]; exact pv
  refine wp_storeS (ea_ptr hv₁ p₁ (d := 0) (by have := wb_ge h.lower; omega))
    (ws_write hv₁ (y := numAt len j + 0) (n := 4) (by have := wb_ge h.lower; omega)) fun w m => WP.block_nil ?_
  have Kw : Keeps [.eax, .ecx, .ebp] s w :=
    (K.trans ((Kv.mono (by decide)).trans (u₁.keeps.mono (by decide)))).trans (m.keeps _)
  have mv₁ : v₁.mem = u.mem := by rw [u₁.mem, mv]
  have hN : 0 < nw len := by simp only [nw]; omega
  refine ⟨?_, ?_, Kw⟩
  · rw [m.mem, mv₁, Nat.add_zero]
    exact O.trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by have := wb_ge h.lower; omega))
  · -- Word 0 is one; the others stay zero.
    rw [m.mem, mv₁, Nat.add_zero, u₁.gpr]
    obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by omega⟩
    rw [hk] at V ⊢
    have V' := V
    rw [val32] at V'
    rw [val32, w32_write_self]
    have rest : val32 (u.mem.writeW (off base (numAt len j)) 1) base (numAt len j + 4) k =
        val32 u.mem base (numAt len j + 4) k :=
      (writeW32_outside u.mem base 1 (by omega)).val32 (by omega) (by have := wb_eq len; omega)
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [rest, e1]
    omega

end VG.Proof.Bignum.X86.PublicRt
