module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # FFDH's context on PPC64LE: its rows

`rowPtr_ok`: the address of a row of the context, from its pointer in the
header. `storeRow_ok` and `loadRow_ok`: an array's `w` words to a row and
back, by `copyWords`. -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Ffdh.PPC64LE.Cached
open VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot)

/-- The offset of row `j` in a context of `w`-word rows. -/
abbrev rowOff (w j : Nat) : Nat := 24 + 8 * (w * j)

theorem row_bv {w j : Nat} (hw : w < 2 ^ 31) (hj : j < 2 ^ 16) :
    ((BitVec.ofNat 64 (2 * w) >>> 1) * BitVec.ofNat 64 j) <<< 3 = BitVec.ofNat 64 (8 * (w * j)) := by
  rw [mont_ofNat_shr1 (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hwj : w * j < 2 ^ 47 := by
    calc w * j < 2 ^ 31 * 2 ^ 16 := Nat.mul_lt_mul_of_lt_of_lt hw hj
      _ = 2 ^ 47 := by rw [← Nat.pow_add]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show w * j < 2 ^ 64 by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show w * j * 2 ^ 3 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * (w * j) < 2 ^ 64 by omega)]
  omega

/-- `rowPtr`: `r8 :=` the address of row `j` (in `r3`) of the context at `C`
(`r30`), with `2 w` in `r11`. -/
theorem rowPtr_ok {s : State} {C : Addr} {w j : Nat}
    (h30 : s.gpr .r30 = C) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h3 : s.gpr .r3 = BitVec.ofNat 64 j)
    (hw : w < 2 ^ 31) (hj : j < 2 ^ 16) :
    WP isa (.block rowPtr) s fun t => (t.gpr .r8 = off C (rowOff w j) ∧ t.mem = s.mem) ∧ Keep [.r8, .r9] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold rowPtr
  prun [h30, h11, h3, row_bv hw hj]
  rw [show 8 * (w * j) + 24 = rowOff w j by unfold rowOff; omega]

/-- The registers `storeRow` and `loadRow` write. -/
def rowRegs : List Reg := [.r0, .r8, .r9, .r14, .r15, .r17]

/-- `storeRow a`: array `a`'s `w` words to row `j` (in `r3`) of the context
at `C`, writable and apart from the working space. -/
theorem storeRow_ok {s : State} {B C : Addr} {Z Zc w j a : Nat} (h : Env s B Z w)
    (hp : Scr s C Zc) (h3 : s.gpr .r3 = BitVec.ofNat 64 j) (h30 : s.gpr .r30 = C)
    (ha : a < 28) (hj : j < 2 ^ 16) (hrow : rowOff w j + 8 * w ≤ Zc)
    (hsep : ∀ x, ofs B x < Z → Zc ≤ ofs C x) :
    WP isa (storeRow a) s fun t =>
      ((∀ i < w, word t.mem C (rowOff w j + 8 * i) = word s.mem B (slot w a + 8 * i)) ∧
        Outside C (rowOff w j) (8 * w) s.mem t.mem) ∧ Keep rowRegs s t := by
  have hw := h.hw; have hw' := h.hw'
  unfold storeRow
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_ok h30 h.h11 h3 (by omega) hj) fun t₁ ⟨⟨a8, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = off C (rowOff w j) ∧ t.mem = t₁.mem)
    (by prun [a8, BitVec.add_zero]) (by decide)) fun t₂ ⟨⟨a14, m2⟩, k2⟩ => ?_
  have e2 : Env t₂ B Z w := (h.keep k1 (by decide)).keep k2 (by decide)
  refine WP.mono (e2.base (rd := .r15) (by decide) (by decide) a) fun t₃ ⟨⟨a15, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have hm : t₃.mem = s.mem := by rw [m3, m2, m1]
  refine WP.mono (copyWords_ok (h.hs.congr k13.wr) (hp.congr k13.wr) a15 ((k3.gpr .r14 (by decide)).trans a14)
    ((k13.gpr .r11 (by decide)).trans h.h11) (by omega) (by omega) (h.arr ha |> fun h' => by omega) hrow hsep)
    fun t ⟨⟨_, hw₁, ho⟩, kt⟩ => ⟨⟨fun i hi => by have := hw₁ i hi; rw [hm] at this; exact this,
      by rw [← hm]; exact ho⟩,
      (k13.trans kt).mono (by decide)⟩

/-- `loadRow a`: row `j` (in `r3`) of the context at `C`, readable and apart
from the working space, to array `a`'s `w` words. -/
theorem loadRow_ok {s : State} {B C : Addr} {Z Zc w j a : Nat} (h : Env s B Z w)
    (h30 : s.gpr .r30 = C) (h3 : s.gpr .r3 = BitVec.ofNat 64 j)
    (ha : a < 28) (hj : j < 2 ^ 16) (hrow : rowOff w j + 8 * w ≤ Zc) (hCn : C.toNat + Zc ≤ 2 ^ 64)
    (hrd : ∀ i < w, InRegions (s.rd ++ s.wr) (off C (rowOff w j + 8 * i)) 8)
    (hsep : ∀ x, ofs C x < Zc → Z ≤ ofs B x) :
    WP isa (loadRow a) s fun t =>
      ((∀ i < w, word t.mem B (slot w a + 8 * i) = word s.mem C (rowOff w j + 8 * i)) ∧
        Outside B (slot w a) (8 * w) s.mem t.mem) ∧ Keep rowRegs s t := by
  have hw := h.hw; have hw' := h.hw'
  unfold loadRow
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_ok h30 h.h11 h3 (by omega) hj) fun t₁ ⟨⟨a8, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = off C (rowOff w j) ∧ t.mem = t₁.mem)
    (by prun [a8, BitVec.add_zero]) (by decide)) fun t₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have e2 : Env t₂ B Z w := (h.keep k1 (by decide)).keep k2 (by decide)
  refine WP.mono (e2.base (rd := .r14) (by decide) (by decide) a) fun t₃ ⟨⟨a14, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have hm : t₃.mem = s.mem := by rw [m3, m2, m1]
  refine WP.mono (Pub.copyIn_ok (h.hs.congr k13.wr) hCn (fun i hi => by rw [k13.rd, k13.wr]; exact hrd i hi)
    ((k3.gpr .r15 (by decide)).trans a15) a14 ((k13.gpr .r11 (by decide)).trans h.h11) (by omega) (by omega)
    hrow (h.arr ha |> fun h' => by omega) hsep)
    fun t ⟨⟨_, _, hw₁, ho⟩, kt⟩ => ⟨⟨fun i hi => by have := hw₁ i hi; rw [hm] at this; exact this,
      by rw [← hm]; exact ho⟩,
      (k13.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.PPC64LE.Cached
