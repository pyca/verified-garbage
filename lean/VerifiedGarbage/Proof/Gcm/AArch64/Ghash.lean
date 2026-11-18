module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.Gcm.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Spec.Gcm.Powers8
import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Impl.Gcm.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Spec.Gcm.Powers8
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Spec.Gcm.Prepared
meta import VerifiedGarbage.Proof.AesGcm.Rounds
meta import VerifiedGarbage.Spec.Gcm.Prepared

/-! ### `Gcm.Prepared8Contract`, which this module and modules that import it used -/

section

/-!
# AES-GCM with eight prepared GHASH powers

Not trusted: a 384-byte key-context format for implementations that read only
the first eight prepared powers. The first 256 bytes are the existing key
context (`KeyRepr`'s layout: the key schedule, and the hash subkey at byte
240); the remaining 128 bytes hold 4 pairs, laid out exactly as the first 4
pairs of `PreparedPowersRepr` (bytes 256 through 383 of the 1024-byte
prepared format): pair `k` is `preparedPower(H^(2k+2))` then
`preparedPower(H^(2k+1))`, each stored little-endian. This is a storage
convention, not a change to GCM's field arithmetic (NIST SP 800-38D §6.3).
The 1024-byte prepared format (`Spec/Gcm/Prepared.lean`) is unchanged.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- The first 4 pairs of `PreparedPowersRepr`: pair `k`, at byte `256 + 32 k`,
contains the encoded `H^(2k+2)` then `H^(2k+1)`, each as a little-endian
128-bit word. The 4 pairs occupy bytes 256 through 383. -/
def PreparedPowers8Repr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 4,
    m.readW (p + BitVec.ofNat 64 (256 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 2)) ∧
    m.readW (p + BitVec.ofNat 64 (272 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 1))

end VG.Proof.Gcm

end

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.AArch64.Step`.

@[expose] public section

section

/-!
# GHASH on AArch64: shifts of a 128-bit value in two registers

What the instructions that shift the two halves of a 128-bit value by one
bit compute, stated on the whole value.
-/

namespace VG.Proof.Gcm.AArch64

open VG VG.AArch64 VG.Impl.Gcm.AArch64 VG.Proof.Gcm
open VG.Spec.Gcm (Block)

/-! ## The bit manipulations -/

/-- `lsl hi, hi, 1; lsr t, lo, 63; orr hi, hi, t; lsl lo, lo, 1` shifts
`hi ++ lo` left by one bit. -/
theorem shl1 (a b : BitVec 64) : (a <<< 1 ||| b >>> 63) ++ b <<< 1 = (a ++ b) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight]
  by_cases h1 : i < 64
  · by_cases h0 : i = 0
    · subst h0; simp
    · simp [h1, h0, hi, show i - 1 < 64 by omega_using [hi, h1]]
  · by_cases h64 : i = 64
    · subst h64; simp
    · simp [h1, hi, show i - 64 < 64 by omega_using [hi, h1], show ¬ i - 1 < 64 by omega_using [hi, h1, h64]]
      rw [BitVec.getLsbD_of_ge b (63 + (i - 64)) (by omega_using [hi, h1, h64]), Bool.or_false,
        decide_eq_false (show i - 64 ≠ 0 by omega_using [hi, h1, h64]), decide_eq_false (show i ≠ 0 by omega_using [hi, h1])]
      simp only [Bool.not_false, Bool.true_and]
      congr 1

/-- `0 − (x >>> 63)` is all ones if the top bit of `x` is set, and zero otherwise. -/
theorem neg_msb (x : BitVec 64) :
    (0 : BitVec 64) - x >>> 63 = if x.msb then BitVec.allOnes 64 else 0 := by
  have h : x >>> 63 = if x.msb then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
    rcases (by omega_using [hi] : i = 0 ∨ 0 < i) with h | h
    · subst h; cases x.getLsbD (64 - 1) <;> simp
    · simp only [show 63 + i ≥ 64 by omega_using [hi, h], BitVec.getLsbD_of_ge]
      split <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega_using [hi, h]]
  rw [h]; split <;> decide

/-- `lsr lo, lo, 1; lsl t, hi, 63; orr lo, lo, t; lsr hi, hi, 1` shifts
`hi ++ lo` right by one bit. -/
theorem shr1 (a b : BitVec 64) : a >>> 1 ++ (b >>> 1 ||| a <<< 63) = (a ++ b) >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  rcases (by omega_using [hi] : i < 63 ∨ i = 63 ∨ 64 ≤ i) with h | h | h
  · simp [h, show 1 + i < 64 by omega_using [hi, h], show i < 64 by omega_using [hi, h]]
  · subst h; simp
  · simp only [show ¬ 1 + i < 64 by omega_using [hi, h], show ¬ i < 64 by omega_using [hi, h], ite_false]
    congr 1; omega_using [hi, h]

end VG.Proof.Gcm.AArch64

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.AArch64.Ghash`.
section

/-!
# GHASH on AArch64: the contracts, and what the proofs of their implementations share
-/

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.AArch64 in
/-- AArch64 contract for `vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data:
*const [u8; 16], n: usize, scratch: *mut [u64; 32])`: replaces the block `Y` at
`y` with `GHASH_H` continued from `Y` over the `n` blocks at `data`, where `H`
is the block at `h`.

The code may read `h` (16 bytes) and `data` (`16 * n` bytes), and read and
write `y` (16 bytes) and `scratch` (256 bytes, whose contents on exit are
unspecified). `y` and `scratch` may not overlap each other or the other
buffers. The pointers and `n` are public; `H`, `Y` and the data are
secret. -/
def ghashAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 16⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch
  post s s' :=
    blockAt s'.mem (s.gpr .x1) =
      ghashFrom (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
        (blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_ghash_prepared(h = x0, y = x1, data = x2, n = x3, scratch = x4)`:
`ghashAArch64`, with `h` the 144 bytes from byte 240 of a 384-byte key
context with the eight prepared powers (`Proof.Gcm.PreparedPowers8Repr`). -/
def ghashPreparedAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 144⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch ∧ Proof.Gcm.PreparedPowers8Repr s.mem (s.gpr .x0 - 240)
  post := ghashAArch64.post
  pub := ghashAArch64.pub

section
open Spec.Gcm

open VG.AArch64 in
/-- `vg_ghash_with_powers(h = x0, y = x1, data = x2, n = x3, scratch = x4,
pw = x5)`: `ghashAArch64`, with the 8 prepared powers of the hash subkey at
`pw` (`Spec.Gcm.Powers8Repr`), which the code may read (128 bytes). -/
def ghashWithAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 16⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    let pw : Region := ⟨s.gpr .x5, 128⟩
    s.rd = [h, data, pw] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    y.Disjoint pw ∧ data.Disjoint scratch ∧ scratch.Disjoint pw ∧
    Powers8Repr s.mem (s.gpr .x5) (blockAt s.mem (s.gpr .x0))
  post := ghashAArch64.post
  pub s₁ s₂ := ghashAArch64.pub s₁ s₂ ∧ s₁.gpr .x5 = s₂.gpr .x5

end

end VG.Proof.Gcm

namespace VG.Proof.Gcm.AArch64

open VG VG.AArch64 VG.Impl.Gcm.AArch64 VG.Proof.Gcm
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Big-endian halves -/

/-- `rev` is `byteRev64`, an involution. -/
theorem rev64_rev64 (a : BitVec 64) : rev64 (rev64 a) = a := byteRev64_byteRev64 a

/-- The 16 bytes as 8 bytes. -/
theorem bytesAt_16 (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 16 =
    [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 3), m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5),
      m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7), m (p + BitVec.ofNat 64 8),
      m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
      m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
      m (p + BitVec.ofNat 64 15)] := rfl

/-- Two 8-byte loads and `rev`s read a block. -/
theorem blockAt_rev (m : Mem) (p : Addr) :
    rev64 (m.readW (p + BitVec.ofNat 64 0) 64) ++ rev64 (m.readW (p + BitVec.ofNat 64 8) 64) =
      blockAt m p := by
  have e : ∀ j : Nat, j < 15 → p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) :=
    fun j _ => Offset.add_add p j 1
  rw [rev64_readW, rev64_readW]
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 8 (by decide), e 9 (by decide), e 10 (by decide), e 11 (by decide),
    e 12 (by decide), e 13 (by decide), e 14 (by decide)]
  rw [Spec.Gcm.blockAt, bytesAt_16, ofBytes_16]

theorem read_8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW]; exact (BitVec.setWidth_eq _).symm

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev hA : Addr := s₀.gpr .x0
abbrev yp : Addr := s₀.gpr .x1
abbrev dp : Addr := s₀.gpr .x2
abbrev nb : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 256⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_y : (hR s₀).Disjoint (yR s₀)
  h_scr : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Gcm.ghashAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega_using [hn]

theorem in_h {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨hR s₀, by simp [h.rd], contains_offset hd (by omega_using [hd])⟩

theorem in_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (yp s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨yR s₀, by simp [h.wr], contains_offset hd (by omega_using [hd])⟩

theorem out_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions s₀.wr (yp s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨yR s₀, by simp [h.wr], contains_offset hd (by omega_using [hd])⟩

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨blkAddr s₀ i, 16⟩ (dR s₀) := by
  have := h.nb_lt
  exact sub_offset (by omega_using [hi]) (by omega_using [hi, this])

theorem in_blk {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := h.nb_lt
  refine ⟨dR s₀, by simp [h.rd], ?_⟩
  rw [blkAddr, Offset.add_add]
  exact contains_offset (by omega_using [hi, hd]) (by omega_using [hi, hd, this])

end Pre

theorem write_8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW]; exact congrArg (m.write a 8) (BitVec.setWidth_eq _).symm

/-- The memory after storing `Z` at `p`. -/
def storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) : Mem :=
  (m.writeW (p + BitVec.ofNat 64 0) (rev64 zh)).writeW (p + BitVec.ofNat 64 8) (rev64 zl)

theorem half_sep (p : Addr) : Mem.Sep (p + BitVec.ofNat 64 0) 8 (p + BitVec.ofNat 64 8) 8 :=
  Offset.sep p (by decide) (by decide) (by decide)

theorem blockAt_storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) :
    blockAt (storeMem m p zh zl) p = zh ++ zl := by
  rw [← blockAt_rev, storeMem, Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (half_sep p) (by decide), Mem.readW_writeW_self64, rev64_rev64,
    rev64_rev64]

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

end VG.Proof.Gcm.AArch64

end
