module

public import VerifiedGarbage.Impl.Rsa.AArch64
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Bignum.AArch64.WordIO
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.ByteDigits
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Bignum.AArch64.WordIOLoad`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.WordIOBytes`, which this module and modules that import it used -/

section

/-!
# Big-endian words on AArch64: `rev`

`rev` maps byte `j` of a word to byte `7 - j` (`rev64_byte`), so `rev` of the
eight bytes at `src + k - 8 (q + 1)`, read little-endian, is digit `q` (in
radix `2^64`) of the OS2IP of the `k` bytes at `src` (`read_digit`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WordIO

open VG VG.AArch64 VG.Proof.Bignum.ByteDigits

/-- Byte reversal maps byte `j` to byte `7 - j`. -/
theorem rev64_byte (v : BitVec 64) {j : Nat} (hj : j < 8) :
    (rev64 v).extractLsb' (8 * j) 8 = v.extractLsb' (8 * (7 - j)) 8 := by
  ext r hr
  simp only [BitVec.getElem_extractLsb', rev64, VG.AArch64.getLsbD_append_block _ _ _ hr]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := omega_using [hr]) only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and, Nat.add_comm]

theorem read_digit {m : Mem} {src : Addr} {bs : List Byte} {q : Nat} (hq : 8 * (q + 1) ≤ bs.length)
    (hb : ∀ i (hi : i < bs.length), m (src + BitVec.ofNat 64 i) = bs[i]) :
    rev64 (m.read (src + BitVec.ofNat 64 (bs.length - 8 * (q + 1))) 8) =
      BitVec.ofNat 64 (Spec.Rsa.os2ip bs / 256 ^ (8 * q)) := by
  apply eq_of_bytes
  intro j hj
  rw [rev64_byte _ hj, extract_nat _ hj, Mem.extractLsb'_read _ _ (by omega_using []), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, hb _ (by omega_using [hq]), os2ip_byte]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega_using [hq, hj]

end VG.Proof.Bignum.AArch64.WordIO

end

end

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
    (hb : ∀ i (hi : i < k), s₀.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega_arith))
    (hsep : ∀ i < k, ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ ofs B (src + BitVec.ofNat 64 i))
    {j : Nat} (hj : j < w) (h : LWInv s₀ B Z ed k w src bs j t) :
    WP isa (.block [ld .x3 .x1, .rev .x3 .x3, .subImm .x .x5 .x5 8, st .x3 .x5, next .x1, .subImm .x .x2 .x2 8]) t
      fun u => LWInv s₀ B Z ed k w src bs (j + 1) u ∧ ((u.gpr .x2).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have hn := h.scr.nowrap
  have hread : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h.keep.rd, h.keep.wr]
    exact VG.CallLay.inRegions_sub hsrc (by omega_arith) (by omega_arith)
  have hbytes : ∀ i (hi : i < bs.length), t.mem (src + BitVec.ofNat 64 i) = bs[i] := by
    intro i hi
    rw [h.out _ (by have := hsep i (by omega_arith); omega_arith)]
    exact hb i (by omega_arith)
  have hdigit := read_digit (q := w - 1 - j) (by omega_arith) hbytes
  rw [hl, show k - 8 * (w - 1 - j + 1) = 8 * j by omega_arith] at hdigit
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x5] (Q := fun u =>
    u.mem = t.mem.writeW (off B (ed + 8 * (w - 1 - j))) (BitVec.ofNat 64 (Spec.Rsa.os2ip bs / 256 ^ (8 * (w - 1 - j)))) ∧
    u.gpr .x1 = src + BitVec.ofNat 64 (8 * (j + 1)) ∧ u.gpr .x2 = BitVec.ofNat 64 (k - 8 * (j + 1)) ∧
    u.gpr .x5 = off B (ed + 8 * (w - (j + 1)))) ?_ (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨hm, h1, h2, h5⟩, ku⟩ => ?_
  · have hx5 : off B (ed + 8 * (w - j)) - BitVec.ofNat 64 8 = off B (ed + 8 * (w - 1 - j)) := by
      show B + _ - _ = B + _
      rw [VG.Offset.add_ofNat_sub B (by omega_arith)]; congr 2; omega_arith
    have hx1 : src + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = src + BitVec.ofNat 64 (8 * (j + 1)) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2
    have hx2 : BitVec.ofNat 64 (k - 8 * j) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (k - 8 * (j + 1)) := by
      rw [VG.Offset.ofNat_sub_ofNat (by omega_arith)]; congr 1
    have hx5' : off B (ed + 8 * (w - 1 - j)) = off B (ed + 8 * (w - (j + 1))) := by
      rw [show w - (j + 1) = w - 1 - j by omega_arith]
    brun [h.x1, h.x2, h.x5, hread, exec_rev, readW64, hdigit, hx5, hx1, hx2,
      h.scr.st (show ed + 8 * (w - 1 - j) + 8 ≤ Z by omega_arith)]
    exact hx5'
  · have hw8 : ed + 8 * (w - 1 - j) + 8 ≤ 2 ^ 64 := by omega_arith
    refine ⟨⟨h.scr.congr ku.wr, (h.keep.trans ku).mono (by decide), h1, h2, h5, fun q hq hq' => ?_, ?_⟩, ?_⟩
    · rw [hm]
      by_cases he : q = w - 1 - j
      · subst he; exact word_writeW_self _ _ _ _
      · rw [(writeW_outside t.mem B _ hw8).word (by omega_arith) (by omega_arith)]
        exact h.words q (by omega_arith) hq'
    · intro x hx
      rw [hm, writeW_outside t.mem B _ hw8 x (by omega_arith)]
      exact h.out x hx
    · rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith

theorem loadWords_ok {s : State} {B src : Addr} {Z ed k w : Nat} {bs : List Byte}
    (hs : Scr s B Z) (h1 : s.gpr .x1 = src) (h2 : s.gpr .x2 = BitVec.ofNat 64 k)
    (h8 : s.gpr .x8 = off B ed) (hk : k = 8 * w) (hk1 : 0 < k) (hk' : k < 2 ^ 31)
    (hl : bs.length = k) (hed : ed + 8 * w ≤ Z) (hsrc : InRegions (s.rd ++ s.wr) src k)
    (hb : ∀ i (hi : i < k), s.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega_using [hl, hi]))
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
  rw [wv_digits w fun q hq => h.words q (by omega_using []) hq, Nat.mod_eq_of_lt]
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
  have hb' : ∀ i (hi : i < k), a.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega_using [hk, hi]) :=
    fun i hi => by rw [hm]; exact hbytes i hi
  have a1 := (ka.gpr .x1 (by decide)).trans h1
  have a2 := (ka.gpr .x2 (by decide)).trans h2
  have a8 := (ka.gpr .x8 (by decide)).trans h8
  refine WP.ite (decide (k % 8 = 0)) (by rw [eval_zero, h4, and7_zero (by omega_using [hk'])]) ?_ ?_
  · intro h8'
    have h8' := of_decide_eq_true h8'
    refine WP.mono (loadWords_ok hs' a1 a2 a8 (w := w) (by omega_using [hw, h8']) (by omega_using [hk1]) hk' hk hed hr hb' hsep)
      fun t ⟨hv, ho, kt⟩ => ⟨hv, by rw [← hm]; exact ho, (ka.trans kt).mono (by decide)⟩
  · intro _
    refine WP.mono (loadBE_ok hs' a1 a2 a8 hk hk1 hk' hw hed
      (fun i hi => VG.CallLay.inRegions_sub hr (by omega_using [hi]) (by omega_using [hk'])) hb' hsep)
      fun t ⟨hv, ho, kt⟩ => ⟨hv, by rw [← hm]; exact ho, (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WordIO

end

end

/-!
# RSA on AArch64: the setup

From a header holding `k` (slot `sK`): `w = ⌈k / 8⌉` and the arrays' bases
(`head_ok`); bytes outside the working space (`Src`) into an array
(`loadArr_ok`, a word at a time by `loadArrW_ok`); and `pcLoad` and
`pcLoadW`, the modulus into array `aN` and `-m⁻¹` into its slot
(`pcLoad_ok`, `pcLoadW_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## `w` and the bases -/

theorem shr3_w (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega_arith

/-- `head`: `w` into `x12` and its slot, and the arrays' bases. -/
theorem head_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk : k < 2 ^ 32) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) :
    WP isa (.block head) s fun t =>
      t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.x3, .x4, .x12] s t := by
  have hn := hs.nowrap
  have eK : sK = 18 := rfl
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  have eaN : aN = 0 := rfl
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  unfold head
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧
      t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 ((k + 7) / 8))) ?_ (by decide) (by decide)
      (by decide +kernel))
    fun t₁ ⟨⟨h12, hm₁⟩, k₁⟩ => ?_
  · brun [h0, hdr_enc (show sK < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs.ld (d := 8 * sK) (by omega_arith), hs.st (d := 8 * sW) (by omega_arith), hK, shr3_w k hk]
  obtain hs₁ := hs.congr k₁.wr
  refine WP.mono (setBases_ok hs₁ ((k₁.gpr .x0 (by decide)).trans h0) h12 (by unfold sArr; omega_arith))
    fun t ⟨hb, ho, k₂⟩ => ⟨(k₂.gpr .x12 (by decide)).trans h12, ?_, hb, ?_, (k₁.trans k₂).mono (by decide)⟩
  · rw [ho.word (by omega_arith) (by omega_arith), hm₁, word_writeW_self]
  · have hw₁ : Outside B (8 * sW) 8 s.mem t₁.mem := by rw [hm₁]; exact writeW_outside s.mem B _ (by omega_arith)
    exact (Frm.of_outside hw₁ (by simp)).trans (Frm.of_outside ho (by simp))

/-! ## Byte strings outside the working space -/

/-- The bytes `bs` at `p`, readable, outside the working space. -/
structure Src (s : State) (B : Addr) (Z : Nat) (p : Addr) (bs : List Byte) : Prop where
  rd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1
  val : ∀ i (h : i < bs.length), s.mem (p + BitVec.ofNat 64 i) = bs[i]
  out : ∀ i < bs.length, Z ≤ ofs B (p + BitVec.ofNat 64 i)

theorem Src.congr {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs)
    (hm : InScr B Z s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t B Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => by rw [hm _ (h.out i hi)]; exact h.val i hi, h.out⟩

theorem Src.congrK {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} {rs : List Reg}
    (h : Src s B Z p bs) (hm : InScr B Z s.mem t.mem) (k : Keep rs s t) : Src t B Z p bs :=
  h.congr hm k.rd k.wr

theorem src_of_region {s : State} {B : Addr} {Z : Nat} {p : Addr} {len : Nat}
    (hr : (⟨p, len⟩ : Region) ∈ s.rd ++ s.wr) (hlen : len ≤ 2 ^ 64)
    (hd : (⟨p, len⟩ : Region).Disjoint ⟨B, Z⟩) : Src s B Z p (Spec.Rsa.bytesAt s.mem p len) := by
  obtain hl : (Spec.Rsa.bytesAt s.mem p len).length = len := by simp [Spec.Rsa.bytesAt]
  refine ⟨fun i hi => ⟨_, hr, contains_byte p (by omega_arith) hlen⟩, fun i hi => ?_,
    fun i hi => out_scr hd (contains_byte p (by omega_arith) hlen)⟩
  simp [Spec.Rsa.bytesAt]

/-- A region's bytes are in the regions it is one of. -/
theorem span_of_region {X : List Region} {p : Addr} {len : Nat} (hr : (⟨p, len⟩ : Region) ∈ X) :
    InRegions X p len :=
  ⟨_, hr, by simp [Region.Contains]⟩

/-- `loadW` of bytes outside the working space into array `j`. -/
theorem loadArrW_ok {s : State} {B : Addr} {Z k : Nat} {p : Addr} {bs : List Byte} {j : Nat} (hs : Scr s B Z)
    (hj : j < 8) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hsrc : Src s B Z p bs) (hspan : InRegions (s.rd ++ s.wr) p k)
    (hk : bs.length = k) (hk1 : 1 ≤ k)
    (hk' : k < 2 ^ 31) (h1 : s.gpr .x1 = p) (h2 : s.gpr .x2 = BitVec.ofNat 64 k)
    (h8 : s.gpr .x8 = off B (slot ((k + 7) / 8) j)) :
    WP isa loadW s fun t =>
      wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) = Spec.Rsa.os2ip bs ∧
      Arrays B ((k + 7) / 8) [j] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6] s t := by
  have := slot_le (w := (k + 7) / 8) hj
  refine WP.mono (WordIO.loadW_ok hs h1 h2 h8 hk hk1 hk' rfl (by omega_arith) hspan
    (fun i hi => hsrc.val i (by omega_arith)) (fun i hi => Or.inr (by have := hsrc.out i (by omega_arith); omega_arith)))
    fun t ⟨h1, h2, h3⟩ => ⟨h1, Arrays.of_outside (List.mem_singleton_self j) h2 (Nat.le_refl _) (by omega_arith), h3⟩

/-- `loadBE` of bytes outside the working space into array `j`. -/
theorem loadArr_ok {s : State} {B : Addr} {Z k : Nat} {p : Addr} {bs : List Byte} {j : Nat} (hs : Scr s B Z)
    (hj : j < 8) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hsrc : Src s B Z p bs) (hk : bs.length = k) (hk1 : 1 ≤ k)
    (hk' : k < 2 ^ 31) (h1 : s.gpr .x1 = p) (h2 : s.gpr .x2 = BitVec.ofNat 64 k)
    (h8 : s.gpr .x8 = off B (slot ((k + 7) / 8) j)) :
    WP isa loadBE s fun t =>
      wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) = Spec.Rsa.os2ip bs ∧
      Arrays B ((k + 7) / 8) [j] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6] s t := by
  have := slot_le (w := (k + 7) / 8) hj
  refine WP.mono (loadBE_ok hs h1 h2 h8 hk hk1 hk' rfl (by omega_arith) (fun i hi => hsrc.rd i (by omega_arith))
    (fun i hi => hsrc.val i (by omega_arith)) (fun i hi => Or.inr (by have := hsrc.out i (by omega_arith); omega_arith)))
    fun t ⟨h1, h2, h3⟩ => ⟨h1, Arrays.of_outside (List.mem_singleton_self j) h2 (Nat.le_refl _) (by omega_arith), h3⟩

/-! ## `pcLoad` -/

/-- `pcLoad`'s first block: `head`, then `m`'s pointer, base and length. -/
theorem pcHead_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk : k < 2 ^ 32)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np) :
    WP isa (.block (head ++ ([ldh .x1 sN, ldh .x8 (sArr aN), ldh .x2 sK] : List Instr))) s fun t =>
      t.gpr .x1 = np ∧ t.gpr .x2 = BitVec.ofNat 64 k ∧ t.gpr .x8 = off B (slot ((k + 7) / 8) aN) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x8, .x12] s t := by
  have hn := hs.nowrap
  have eK : sK = 18 := rfl
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  have eaN : aN = 0 := rfl
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  rw [WP.block_append_iff]
  refine WP.mono (head_ok hs h0 hZ hk hK) fun t₁ ⟨_, hW₁, hb₁, hf₁, k₁⟩ => ?_
  obtain hs₁ := hs.congr k₁.wr
  obtain hw₁ : ∀ i, 8 * i + 8 ≤ 8 * sW ∨ (16 ≤ i ∧ i < 32) → word t₁.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi => hf₁.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> omega_arith) (by omega_arith)
  refine WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = np ∧ t.gpr .x2 = BitVec.ofNat 64 k ∧
      t.gpr .x8 = off B (slot ((k + 7) / 8) aN) ∧ t.mem = t₁.mem) (by
    brun [(k₁.gpr .x0 (by decide)).trans h0, hdr_enc (show sN < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (show sArr aN < 32 by decide), hs₁.ld (d := 8 * sN) (by omega_arith),
      hs₁.ld (d := 8 * sK) (by omega_arith), hs₁.ld (d := 8 * sArr aN) (by omega_arith),
      hw₁ sN (by omega_arith), hw₁ sK (by omega_arith), hN, hK, hb₁ aN (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h1, h2, h8', hm⟩, k₂⟩ => ?_
  exact ⟨h1, h2, h8', by rw [hm]; exact hW₁, fun j hj => by rw [hm]; exact hb₁ j hj,
    by rw [hm]; exact hf₁, (k₁.trans k₂).mono (by decide)⟩

/-- The load by `load`, which reads `m` as `loadBE` does: `w`, the bases, `m`,
and `-m⁻¹` for the odd `m`. -/
theorem pcLoadWith_ok {load : Prog isa} {s : State} {B : Addr} {Z k : Nat} {np : Addr} {nb : List Byte}
    (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hnb : Src s B Z np nb) (hnl : nb.length = k) (hodd : Spec.Rsa.os2ip nb % 2 = 1)
    (hld : ∀ t : State, Scr t B Z → Src t B Z np nb → t.rd = s.rd → t.wr = s.wr → t.gpr .x1 = np →
      t.gpr .x2 = BitVec.ofNat 64 k → t.gpr .x8 = off B (slot ((k + 7) / 8) aN) →
      WP isa load t fun u => wv u.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
        Arrays B ((k + 7) / 8) [aN] t.mem u.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6] t u) :
    WP isa (seqs (pcLoadWith load)) s fun t => ∃ minv, Good t B Z ((k + 7) / 8) minv ∧
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
      ((word t.mem B (slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have eK : sK = 18 := rfl
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  have eaN : aN = 0 := rfl
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  obtain h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  obtain hsN := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
  obtain hsl : ∀ r ∈ pcLoadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr =>
    Nat.le_trans (pcLoadRanges_le _ r hr) hZ
  unfold pcLoadWith
  refine WP.seq (WP.mono (pcHead_ok hs h0 hZ (by omega) hK hN)
    fun t₁ ⟨h1, h2, h8', hW₁, hb₁, hf₁, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.wr
  obtain hf₁' : Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [pcLoadRanges])
  refine WP.seq (WP.mono (hld t₁ hs₁ (hnb.congrK (InScr.of_frm hf₁' hsl) k₁) k₁.rd k₁.wr h1 h2 h8')
    fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.wr
  obtain hf₂ : Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays1 ha₂ (by simp [pcLoadRanges]))
  obtain h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0)
  obtain hb₂ : ∀ j < 8, word t₂.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ha₂.hslot (by unfold sArr; omega_using [hj])]; exact hb₁ j hj
  obtain hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ha₂.hslot (by decide)]; exact hW₁
  obtain hodd₀ : (word t₂.mem B (slot ((k + 7) / 8) aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ (k + 7) / 8 by omega_using [hk1]), Nat.mod_mod_of_dvd _ (by decide), hv₂, hodd]
  obtain h8₂ : t₂.gpr .x8 = off B (slot ((k + 7) / 8) aN) := (k₂.gpr .x8 (by decide)).trans h8'
  show WP isa (.block ([ld .x3 .x8] ++ minv ++ [sth .x15 sMinv])) t₂ _
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = word t₂.mem B (slot ((k + 7) / 8) aN) ∧
      t.mem = t₂.mem) (by
    brun [h8₂, hs₂.ld (d := slot ((k + 7) / 8) aN) (by omega_using [hZ, hsN])]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h3₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [h3₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [h3₃] at hinv
  obtain hs₄ := (hs₂.congr k₃.wr).congr k₄.wr
  obtain h0₄ : t₄.gpr .x0 = B := (k₄.gpr .x0 (by decide)).trans ((k₃.gpr .x0 (by decide)).trans h0₂)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)) (by
    brun [h0₄, hdr_enc (show sMinv < 32 by decide), hs₄.st (d := 8 * sMinv) (by omega_using [hZ, eM, h8, h0'])])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₅⟩ => ?_
  obtain hm' : t.mem = t₂.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15) := by rw [hm, hm₄, hm₃]
  obtain hwo : Outside B (8 * sMinv) 8 t₂.mem t.mem := by rw [hm']; exact writeW_outside _ B _ (by omega_using [eM])
  refine ⟨t₄.gpr .x15, ⟨hs₄.congr k₅.wr, (k₅.gpr .x0 (by decide)).trans h0₄, ⟨?_, ?_, fun j hj => ?_⟩⟩, ?_, ?_,
    hf₂.trans (Frm.of_outside hwo (by simp [pcLoadRanges])),
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)⟩
  · rw [hwo.word (by omega_using [eW, eM]) (by omega_using [eW])]; exact hW₂
  · rw [hm', word_writeW_self]
  · rw [hwo.word (d := 8 * sArr j) (by unfold sArr sMinv; omega_using []) (by unfold sArr; omega_using [hj])]; exact hb₂ j hj
  · rw [hwo.wv (by have := hdr_lt_slot ((k + 7) / 8) aN (show sMinv < 32 by decide); omega_using [this]) (by omega_using [hZ, hn, hsN])]
    exact hv₂
  · rw [hwo.word (by have := hdr_lt_slot ((k + 7) / 8) aN (show sMinv < 32 by decide); omega_using [this]) (by omega_using [hZ, hn, hsN])]
    exact hinv

/-- The load a byte at a time: `w`, the bases, `m`, and `-m⁻¹` for the odd
`m`. -/
theorem pcLoad_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} {nb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hnb : Src s B Z np nb) (hnl : nb.length = k) (hodd : Spec.Rsa.os2ip nb % 2 = 1) :
    WP isa (seqs pcLoad) s fun t => ∃ minv, Good t B Z ((k + 7) / 8) minv ∧
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
      ((word t.mem B (slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t :=
  pcLoadWith_ok hs h0 hZ hk1 hk hK hN hnb hnl hodd fun _ ht hsrc _ _ h1 h2 h8 =>
    loadArr_ok ht (by decide) hZ hsrc hnl (by omega_arith) hk h1 h2 h8

/-- The load a word at a time, for `m` in one region: `w`, the bases, `m`,
and `-m⁻¹` for the odd `m`. -/
theorem pcLoadW_ok {s : State} {B : Addr} {Z k : Nat} {np : Addr} {nb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hnb : Src s B Z np nb) (hnspan : InRegions (s.rd ++ s.wr) np k) (hnl : nb.length = k)
    (hodd : Spec.Rsa.os2ip nb % 2 = 1) :
    WP isa (seqs pcLoadW) s fun t => ∃ minv, Good t B Z ((k + 7) / 8) minv ∧
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb ∧
      ((word t.mem B (slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t :=
  pcLoadWith_ok hs h0 hZ hk1 hk hK hN hnb hnl hodd fun _ ht hsrc hrd hwr h1 h2 h8 =>
    loadArrW_ok ht (by decide) hZ hsrc (by rw [hrd, hwr]; exact hnspan) hnl (by omega_arith) hk h1 h2 h8

end VG.Proof.Bignum.AArch64
