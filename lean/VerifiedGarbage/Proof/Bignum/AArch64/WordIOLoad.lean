module
public import VerifiedGarbage.Impl.Bignum.AArch64.WordIO
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.WordIOBytes
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Big-endian bytes into words, a word at a time, on AArch64

`loadWords` reads the `k = 8 w` bytes at `src` into the `w` words of an
array: after `j` words, `x1 = src + 8 j`, `x2 = k - 8 j`, `x5` is the array's
word `w - j`, and the words from `w - j` up are digits of the OS2IP (`LWInv`).
`loadW` takes it or `loadBE` by `k mod 8` (`loadW_ok`, with `loadBE_ok`'s
statement but for the bytes' one region).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WordIO

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_zero)

theorem readW64 (m : Mem) (a : Addr) : m.readW a 64 = m.read a 8 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- After `j` words of `loadWords` from `s₀`. -/
structure LWInv (s₀ : State) (B : Addr) (Z ed k w : Nat) (src : Addr) (bs : List Byte) (j : Nat)
    (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x5] s₀ t
  x1 : t.gpr .x1 = src + BitVec.ofNat 64 (8 * j)
  x2 : t.gpr .x2 = BitVec.ofNat 64 (k - 8 * j)
  x5 : t.gpr .x5 = off B (ed + 8 * (w - j))
  words : ∀ q, w - j ≤ q → q < w → word t.mem B (ed + 8 * q) = BitVec.ofNat 64 (Spec.Rsa.os2ip bs / 256 ^ (8 * q))
  out : Outside B ed (8 * w) s₀.mem t.mem

theorem loadWordsStep_ok {s₀ t : State} {B src : Addr} {Z ed k w : Nat} {bs : List Byte}
    (hk : k = 8 * w) (hk' : k < 2 ^ 31) (hl : bs.length = k) (hed : ed + 8 * w ≤ Z)
    (hsrc : InRegions (s₀.rd ++ s₀.wr) src k)
    (hb : ∀ i (hi : i < k), s₀.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ ofs B (src + BitVec.ofNat 64 i))
    {j : Nat} (hj : j < w) (h : LWInv s₀ B Z ed k w src bs j t) :
    WP isa (.block [ld .x3 .x1, .rev .x3 .x3, .subImm .x .x5 .x5 8, st .x3 .x5, next .x1, .subImm .x .x2 .x2 8]) t
      fun u => LWInv s₀ B Z ed k w src bs (j + 1) u ∧ ((u.gpr .x2).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have hn := h.scr.nowrap
  have hread : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h.keep.rd, h.keep.wr]
    exact VG.CallLay.inRegions_sub hsrc (by omega) (by omega)
  have hbytes : ∀ i (hi : i < bs.length), t.mem (src + BitVec.ofNat 64 i) = bs[i] := by
    intro i hi
    rw [h.out _ (by have := hsep i (by omega); omega)]
    exact hb i (by omega)
  have hdigit := read_digit (q := w - 1 - j) (by omega) hbytes
  rw [hl, show k - 8 * (w - 1 - j + 1) = 8 * j by omega] at hdigit
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x5] (Q := fun u =>
    u.mem = t.mem.writeW (off B (ed + 8 * (w - 1 - j))) (BitVec.ofNat 64 (Spec.Rsa.os2ip bs / 256 ^ (8 * (w - 1 - j)))) ∧
    u.gpr .x1 = src + BitVec.ofNat 64 (8 * (j + 1)) ∧ u.gpr .x2 = BitVec.ofNat 64 (k - 8 * (j + 1)) ∧
    u.gpr .x5 = off B (ed + 8 * (w - (j + 1)))) ?_ (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨hm, h1, h2, h5⟩, ku⟩ => ?_
  · have hx5 : off B (ed + 8 * (w - j)) - BitVec.ofNat 64 8 = off B (ed + 8 * (w - 1 - j)) := by
      show B + _ - _ = B + _
      rw [VG.Offset.add_ofNat_sub B (by omega)]; congr 2; omega
    have hx1 : src + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = src + BitVec.ofNat 64 (8 * (j + 1)) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2
    have hx2 : BitVec.ofNat 64 (k - 8 * j) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (k - 8 * (j + 1)) := by
      rw [VG.Offset.ofNat_sub_ofNat (by omega)]; congr 1
    have hx5' : off B (ed + 8 * (w - 1 - j)) = off B (ed + 8 * (w - (j + 1))) := by
      rw [show w - (j + 1) = w - 1 - j by omega]
    brun [h.x1, h.x2, h.x5, hread, exec_rev, readW64, hdigit, hx5, hx1, hx2,
      h.scr.st (show ed + 8 * (w - 1 - j) + 8 ≤ Z by omega)]
    exact hx5'
  · have hw8 : ed + 8 * (w - 1 - j) + 8 ≤ 2 ^ 64 := by omega
    refine ⟨⟨h.scr.congr ku.wr, (h.keep.trans ku).mono (by decide), h1, h2, h5, fun q hq hq' => ?_, ?_⟩, ?_⟩
    · rw [hm]
      by_cases he : q = w - 1 - j
      · subst he; exact word_writeW_self _ _ _ _
      · rw [(writeW_outside t.mem B _ hw8).word (by omega) (by omega)]
        exact h.words q (by omega) hq'
    · intro x hx
      rw [hm, writeW_outside t.mem B _ hw8 x (by omega)]
      exact h.out x hx
    · rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega

theorem loadWords_ok {s : State} {B src : Addr} {Z ed k w : Nat} {bs : List Byte}
    (hs : Scr s B Z) (h1 : s.gpr .x1 = src) (h2 : s.gpr .x2 = BitVec.ofNat 64 k)
    (h8 : s.gpr .x8 = off B ed) (hk : k = 8 * w) (hk1 : 0 < k) (hk' : k < 2 ^ 31)
    (hl : bs.length = k) (hed : ed + 8 * w ≤ Z) (hsrc : InRegions (s.rd ++ s.wr) src k)
    (hb : ∀ i (hi : i < k), s.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ ofs B (src + BitVec.ofNat 64 i)) :
    WP isa loadWords s fun t => wv t.mem B ed w = Spec.Rsa.os2ip bs ∧
      Outside B ed (8 * w) s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x5] s t := by
  have hn := hs.nowrap
  unfold loadWords
  refine WP.seq (WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off B (ed + 8 * w) ∧ t.mem = s.mem)
    (by brun [h8, h2, hk]) (by decide) (by decide) (by decide +kernel)) fun a ⟨⟨h5, hm⟩, ka⟩ => ?_)
  have h0 : LWInv a B Z ed k w src bs 0 a :=
    ⟨hs.congr ka.wr, Keep.refl _ _, by rw [(ka.gpr .x1 (by decide)).trans h1]; exact (BitVec.add_zero src).symm,
      by rw [(ka.gpr .x2 (by decide)).trans h2, Nat.mul_zero, Nat.sub_zero], by rw [h5, Nat.sub_zero], fun q hq hq' => by omega,
      Outside.refl _ _ _ _⟩
  have hr : InRegions (a.rd ++ a.wr) src k := by rw [ka.rd, ka.wr]; exact hsrc
  refine WP.mono (count_loop (cr := .x2) (n := w) (by omega) (LWInv a B Z ed k w src bs)
    (fun j hj t h => loadWordsStep_ok hk hk' hl hed hr (fun i hi => by rw [hm]; exact hb i hi) hsep hj h) h0)
    fun t h => ⟨?_, by rw [← hm]; exact h.out, (ka.trans h.keep).mono (by decide)⟩
  rw [wv_digits w fun q hq => h.words q (by omega) hq, Nat.mod_eq_of_lt]
  have hlt := VG.Proof.Rsa.lt_of_os2ip bs
  rw [hl, hk, pow256] at hlt
  exact hlt

theorem and7_zero {k : Nat} (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k &&& (BitVec.ofNat 16 7).setWidth 64 == 0) = decide (k % 8 = 0) := by
  have e : (BitVec.ofNat 16 7).setWidth 64 = 7#64 := rfl
  rw [e]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, and7_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  rfl

/-- `loadW`: `loadBE` (`loadBE_ok`), for bytes in one region. -/
theorem loadW_ok {s : State} {B : Addr} {Z ed k w : Nat} {src : Addr} {bs : List Byte}
    (hs : Scr s B Z) (h1 : s.gpr .x1 = src) (h2 : s.gpr .x2 = BitVec.ofNat 64 k)
    (h8 : s.gpr .x8 = off B ed) (hk : bs.length = k) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hsrc : InRegions (s.rd ++ s.wr) src k)
    (hbytes : ∀ i (h : i < k), s.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega_using [hk, h]))
    (hsep : ∀ i < k, ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ ofs B (src + BitVec.ofNat 64 i)) :
    WP isa loadW s fun t =>
      wv t.mem B ed w = Spec.Rsa.os2ip bs ∧ Outside B ed (8 * w) s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6] s t := by
  unfold loadW
  refine WP.seq (WP.mono (WP.keep [.x4, .x6] (Q := fun a => a.gpr .x4 = BitVec.ofNat 64 k &&& (BitVec.ofNat 16 7).setWidth 64 ∧
      a.mem = s.mem) (by brun [h2]) (by decide) (by decide) (by decide +kernel)) fun a ⟨⟨h4, hm⟩, ka⟩ => ?_)
  have hs' := hs.congr ka.wr
  have hr : InRegions (a.rd ++ a.wr) src k := by rw [ka.rd, ka.wr]; exact hsrc
  have hb' : ∀ i (hi : i < k), a.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega) :=
    fun i hi => by rw [hm]; exact hbytes i hi
  have a1 := (ka.gpr .x1 (by decide)).trans h1
  have a2 := (ka.gpr .x2 (by decide)).trans h2
  have a8 := (ka.gpr .x8 (by decide)).trans h8
  refine WP.ite (decide (k % 8 = 0)) (by rw [eval_zero, h4, and7_zero (by omega)]) ?_ ?_
  · intro h8'
    have h8' := of_decide_eq_true h8'
    refine WP.mono (loadWords_ok hs' a1 a2 a8 (w := w) (by omega) (by omega) hk' hk hed hr hb' hsep)
      fun t ⟨hv, ho, kt⟩ => ⟨hv, by rw [← hm]; exact ho, (ka.trans kt).mono (by decide)⟩
  · intro _
    refine WP.mono (loadBE_ok hs' a1 a2 a8 hk hk1 hk' hw hed
      (fun i hi => VG.CallLay.inRegions_sub hr (by omega) (by omega)) hb' hsep)
      fun t ⟨hv, ho, kt⟩ => ⟨hv, by rw [← hm]; exact ho, (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WordIO
