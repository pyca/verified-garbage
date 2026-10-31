module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # GHASH on PPC64LE: contracts, buffers and memory facts -/

@[expose] public section

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.PPC64LE in
/-- PPC64LE contract for `vg_ghash(h = r3, y = r4, data = r5, n = r6,
scratch = r7)`: replaces the block `Y` at `y` with `GHASH_H` continued from
`Y` over the `n` blocks at `data`, where `H` is the block at `h`.

The code may read `h` (16 bytes) and `data` (`16 * n` bytes), and read and
write `y` (16 bytes) and `scratch` (256 bytes, whose contents on exit are
unspecified). `y` and `scratch` may not overlap each other or the other
buffers. The pointers and `n` are public; `H`, `Y` and the data are
secret. -/
def ghashPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let h : Region := ⟨s.gpr .r3, 16⟩
    let y : Region := ⟨s.gpr .r4, 16⟩
    let data : Region := ⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 256⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch
  post s s' :=
    blockAt s'.mem (s.gpr .r4) =
      ghashFrom (blockAt s.mem (s.gpr .r3)) (blockAt s.mem (s.gpr .r4))
        (blocksAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

end VG.Proof.Gcm

namespace VG.Proof.Gcm.PPC64LE

open VG VG.PPC64LE VG.Proof.Gcm
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Big-endian halves -/

/-- The 16 bytes as 8 bytes. -/
theorem bytesAt_16 (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 16 =
    [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 3), m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5),
      m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7), m (p + BitVec.ofNat 64 8),
      m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
      m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
      m (p + BitVec.ofNat 64 15)] := rfl

/-- Two byte-reversed 8-byte loads read a block. -/
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

/-- `rev64` is an involution. -/
theorem rev64_rev64 (a : BitVec 64) : rev64 (rev64 a) = a := byteRev64_byteRev64 a

/-! ## Addresses and regions -/

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev hA : Addr := s₀.gpr .r3
abbrev yp : Addr := s₀.gpr .r4
abbrev dp : Addr := s₀.gpr .r5
abbrev nb : Nat := (s₀.gpr .r6).toNat
abbrev scr : Addr := s₀.gpr .r7
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

theorem pre_of (s₀ : State) (h : Proof.Gcm.ghashPPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The precondition depends only on the registers and the permissions. -/
theorem Pre.congr {s₀ s : State} (h : Pre s₀) (hg : s.gpr = s₀.gpr) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : Pre s := by
  have e : ∀ r, s.gpr r = s₀.gpr r := fun r => by rw [hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hR, yR, dR, scrR, hA, yp, dp, nb, scr, e, hrd, hwr]
  exacts [h.rd, h.wr, h.h_y, h.h_scr, h.y_d, h.y_scr, h.d_scr]

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega

theorem in_h {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨hR s₀, by simp [h.rd], contains_offset hd (by omega)⟩

theorem in_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (yp s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨yR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions s₀.wr (yp s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨yR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_scr {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨blkAddr s₀ i, 16⟩ (dR s₀) := by
  have := h.nb_lt
  exact sub_offset (by omega) (by omega)

theorem in_blk {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := h.nb_lt
  refine ⟨dR s₀, by simp [h.rd], ?_⟩
  rw [blkAddr, Offset.add_add]
  exact contains_offset (by omega) (by omega)

end Pre

/-! ## Memory outside a frame -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p :=
  blockAt_congr fun _ hk => hf.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem blocksAt_frame {s₀ : State} (hp : Pre s₀) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) :
    blocksAt m' (dp s₀) (nb s₀) = blocksAt m (dp s₀) (nb s₀) := by
  simp only [blocksAt]
  refine List.map_congr_left fun i hi => blockAt_frame hf fun r hr => ?_
  exact (hd r hr).sub_left (hp.blk_sub (List.mem_range.mp hi))


end VG.Proof.Gcm.PPC64LE
