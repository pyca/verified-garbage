module

public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Spec.Gcm.Powers8
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# GHASH on AArch64: the contracts, and blocks as two words

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.AArch64 in
/-- AArch64 contract for `vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data:
*const [u8; 16], n: usize, scratch: *mut [u64; 32])`: replaces the block `Y` at
`y` with `GHASH_H` continued from `Y` over the `n` blocks at `data`, where `H`
is the block at `h`. The pointers and `n` are public; `H`, `Y` and the data
are secret. -/
def ghashAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 16⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧ data.Disjoint scratch
  post s s' :=
    blockAt s'.mem (s.gpr .x1) =
      ghashFrom (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
        (blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- `ghashAArch64` with the first eight prepared powers of `H` at `x5`. -/
def ghashWithAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 16⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    let pw : Region := ⟨s.gpr .x5, 128⟩
    s.rd = [h, data, pw] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧ y.Disjoint pw ∧
    data.Disjoint scratch ∧ scratch.Disjoint pw ∧
    Powers8Repr s.mem (s.gpr .x5) (blockAt s.mem (s.gpr .x0))
  post := ghashAArch64.post
  pub s₁ s₂ := ghashAArch64.pub s₁ s₂ ∧ s₁.gpr .x5 = s₂.gpr .x5

/-- The first eight prepared powers in a prepared context. -/
def PreparedPowers8Repr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 4,
    m.readW (p + BitVec.ofNat 64 (256 + 32 * k)) 128 = preparedPower (hpow (ctxH m p) (2 * k + 2)) ∧
    m.readW (p + BitVec.ofNat 64 (272 + 32 * k)) 128 = preparedPower (hpow (ctxH m p) (2 * k + 1))

open VG.AArch64 in
/-- `ghashAArch64`, the hash subkey followed by its first eight prepared
powers. -/
def ghashPreparedAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 144⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧ data.Disjoint scratch ∧
    PreparedPowers8Repr s.mem (s.gpr .x0 - 240)
  post := ghashAArch64.post
  pub := ghashAArch64.pub

end VG.Proof.Gcm

namespace VG.Proof.Gcm.AArch64

open VG VG.AArch64
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

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

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)

end

/-- `ghashAArch64.pre`, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_y : (hR s₀).Disjoint (yR s₀)
  h_s : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_s : (yR s₀).Disjoint (scrR s₀)
  d_s : (dR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : ghashAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem Pre.nb_lt {s₀ : State} (h : Pre s₀) : 16 * nb s₀ < 2 ^ 64 := by
  rcases Nat.lt_or_ge (16 * nb s₀) (2 ^ 64) with hl | hn
  · exact hl
  exfalso
  refine h.y_d (yp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega_using [this, hn]

/-! ## Blocks as two words -/

/-- Two loads and byte reversals read a block. -/
theorem blockAt_rev (m : Mem) (p : Addr) :
    rev64 (m.readW (p + BitVec.ofNat 64 0) 64) ++ rev64 (m.readW (p + BitVec.ofNat 64 8) 64) = blockAt m p := by
  have h : Spec.Aes.bytesAt m p 16 =
      [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2), m (p + BitVec.ofNat 64 3),
        m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5), m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7),
        m (p + BitVec.ofNat 64 8), m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
        m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
        m (p + BitVec.ofNat 64 15)] := rfl
  have e : ∀ j : Nat, p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) := fun j => Offset.add_add p j 1
  show (byteRev64 _ ++ byteRev64 _ : BitVec (64 + 64)) = _
  rw [byteRev64_readW, byteRev64_readW]
  simp only [e, Nat.reduceAdd]
  rw [blockAt, h, ofBytes_16]

/-- The words `zh` and `zl` stored byte-reversed at `p`. -/
def storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) : Mem :=
  (m.writeW (p + BitVec.ofNat 64 0) (rev64 zh)).writeW (p + BitVec.ofNat 64 8) (rev64 zl)

theorem blockAt_storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) : blockAt (storeMem m p zh zl) p = zh ++ zl := by
  rw [← blockAt_rev, storeMem, Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (Offset.sep p (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64]
  show (byteRev64 (byteRev64 zh) ++ byteRev64 (byteRev64 zl) : BitVec (64 + 64)) = _
  rw [byteRev64_byteRev64, byteRev64_byteRev64]

/-- A state satisfying `ghashAArch64`'s precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

end VG.Proof.Gcm.AArch64
