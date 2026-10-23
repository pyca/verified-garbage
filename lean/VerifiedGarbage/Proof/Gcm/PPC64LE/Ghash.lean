module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Step
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Step
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Gcm.Bits

/-!
# GHASH on PPC64LE: the whole function

The nonvolatile registers are saved in the scratch buffer, the blocks are
hashed as on AArch64 (`Proof/Gcm/AArch64/Ghash.lean`: `load`, the 128 steps
of `Step.lean`, `store`), and the registers are restored.
-/

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

open VG VG.PPC64LE VG.Impl.Gcm.PPC64LE VG.Proof.Gcm
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

/-! ## Saving and restoring the nonvolatile registers -/

theorem saved_inj : ∀ i < 5, ∀ j < 5, saved i = saved j → i = j := by decide

theorem saved_ne_scr : ∀ i < 5, saved i ≠ SCR := by decide

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 5) (hj : j < 5) (h : i ≠ j) :
    Mem.Sep (w + BitVec.ofNat 64 (8 * i)) 8 (w + BitVec.ofNat 64 (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (scr s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 5) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) SCR (8 * n)]) s (SI s₀ (n + 1)) := by
  have hw : s.gpr SCR = scr s₀ := by rw [h.gpr]; rfl
  have hout : InRegions s.wr (s.gpr SCR + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.wr, hw]; exact hp.out_scr (by omega_using [hn])
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show SCR ≠ .r0 by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by
      omega_using [hn]) hout, Option.some.injEq, exists_eq_left', hw]
  refine ⟨h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _
    (contains_offset (by omega_using [hn]) (by omega_using [hn])), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

theorem save_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block save) s₀ (SI s₀ 5) :=
  wp_range_flatMap (M := isa) (SI s₀) (fun _ _ hk h => save_step hp hk h) 5 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 5, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem restore_step (sB : State) {v : Nat → BitVec 64}
    (hin : ∀ i < 5, InRegions (sB.rd ++ sB.wr) (sB.gpr SCR + BitVec.ofNat 64 (8 * i)) 8)
    (hsav : ∀ i < 5, sB.mem.readW (sB.gpr SCR + BitVec.ofNat 64 (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 5) {s : State} (h : RI sB v n s) :
    WP isa (.block [.load .d (saved n) SCR (8 * n)]) s (RI sB v (n + 1)) := by
  have hw : s.gpr SCR = sB.gpr SCR := h.others SCR fun i hi => (saved_ne_scr i hi).symm
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr SCR + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.rd, h.wr, hw]; exact hin n hn
  have hv : s.mem.readW (s.gpr SCR + BitVec.ofNat 64 (8 * n)) 64 = v n := by
    rw [h.mem, hw]; exact hsav n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show SCR ≠ .r0 by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by
      omega_using [hn]) hin', Option.some.injEq, exists_eq_left', hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n hn e) (by omega_using [hi])
      rw [ite_eq_right e]; exact h.restored i hi
    · rw [ite_eq_left rfl]
  · simp only [State.write]
    rw [ite_eq_right (hr n hn)]; exact h.others r hr

theorem restore_ok (sB : State) {v : Nat → BitVec 64}
    (hin : ∀ i < 5, InRegions (sB.rd ++ sB.wr) (sB.gpr SCR + BitVec.ofNat 64 (8 * i)) 8)
    (hsav : ∀ i < 5, sB.mem.readW (sB.gpr SCR + BitVec.ofNat 64 (8 * i)) 64 = v i) :
    WP isa (.block restore) sB (RI sB v 5) :=
  wp_range_flatMap (M := isa) (RI sB v) (fun _ _ hk h => restore_step sB hin hsav hk h) 5
    (Nat.le_refl _) sB ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl⟩

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = hA s₀
  r4 : s.gpr .r4 = yp s₀
  r7 : s.gpr .r7 = scr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [yR s₀] s₀.mem s.mem
  y : blockAt s.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r5 : s.gpr .r5 = blkAddr s₀ i
  r6 : s.gpr .r6 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_ok (s : State)
    (hh : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 d) 8)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 d) 8)
    (hd : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 d) 8) :
    WP isa (.block load) s fun s₁ =>
      Inner (blockAt s.mem (s.gpr .r4) ^^^ blockAt s.mem (s.gpr .r5)) (blockAt s.mem (s.gpr .r3))
        s 0 s₁ ∧ s₁.gpr CNT = BitVec.ofNat 64 (128 / unroll) := by
  have h0 := hh 0 (by decide); have h8 := hh 8 (by decide)
  have y0 := hy 0 (by decide); have y8 := hy 8 (by decide)
  have d0 := hd 0 (by decide); have d8 := hd 8 (by decide)
  apply WP.of_runBlock
  simp only [load, XH, XL, ZH, ZL, VH, VL, M, T, RH, CNT, ZERO]
  simp only [reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, Nat.reducePow, Nat.reduceLT,
    unroll, Nat.reduceDiv, runBlock_cons, runStep_some, runBlock_nil, exec, addrX, State.load, h0, h8, y0, y8, d0, d8, State.write, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
  · simp only [reduceCtorEq, ↓reduceIte, XH, XL]
    rw [BitVec.shiftLeft_zero, ← BitVec.xor_append, read_8, read_8, read_8, read_8, blockAt_rev,
      blockAt_rev]
  · simp only [reduceCtorEq, ↓reduceIte, ZH, ZL, VH, VL]
    rw [mulSteps_zero, read_8, read_8, blockAt_rev]
    rfl
  · simp only [reduceCtorEq, ↓reduceIte, RH]
    decide
  · simp only [reduceCtorEq, ↓reduceIte, ZERO]
    rfl
  · simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ↓reduceIte]

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

theorem store_ok (s : State) (hz : s.gpr ZERO = 0)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 d) 8) :
    WP isa (.block store) s fun s' =>
      s'.mem = storeMem s.mem (s.gpr .r4) (s.gpr ZH) (s.gpr ZL) ∧
      s'.gpr .r5 = s.gpr .r5 + BitVec.ofNat 64 16 ∧ s'.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ M → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have y0 := hy 0 (by decide); have y8 := hy 8 (by decide)
  simp only [ZERO, BitVec.ofNat_eq_ofNat] at hz
  have y0' : InRegions s.wr (s.gpr .r4 + s.gpr .r18) 8 := by rw [hz]; exact y0
  apply WP.of_runBlock
  simp only [store, ZH, ZL, ZERO, M]
  simp only [reduceCtorEq, ↓reduceIte, ne_eq, not_false_eq_true, Nat.reducePow, Nat.reduceLT,
    Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, addrX, State.store,
    y0', y8, State.write, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [storeMem, write_8, write_8, hz], trivial, trivial, fun r h2 h3 h0 => ?_, trivial⟩
  simp only [h2, h3, h0, ite_false]

theorem storeMem_frame {s₀ : State} {m m' : Mem} (h : Frame [yR s₀] m m') (zh zl : BitVec 64) :
    Frame [yR s₀] m (storeMem m' (yp s₀) zh zl) :=
  (h.writeW (List.mem_cons_self ..) _ (contains_offset (by decide) (by decide))).writeW
    (List.mem_cons_self ..) _ (contains_offset (by decide) (by decide))

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .d .r6) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .d .r6) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok s
    (fun d hd => by rw [hL.rd, hL.wr, hL.r3]; exact hp.in_h hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.r4]; exact hp.in_y hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.r5]; exact hp.in_blk hi hd)) fun s₁ ⟨hI₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (mul_ok hI₁ hc₁) fun s₂ hI₂ => ?_)
  have hr4₂ : s₂.gpr .r4 = yp s₀ := (hI₂.keep .r4 (by decide)).trans hL.r4
  refine WP.mono (store_ok s₂ hI₂.zero fun d hd => by rw [hI₂.wr, hL.wr, hr4₂]; exact hp.out_y hd)
    fun s₃ ⟨hm₃, hr5₃, hr6₃, hk₃, hrd₃, hwr₃⟩ => ?_
  have hk : ∀ r ∈ keepRegs, s₂.gpr r = s.gpr r := hI₂.keep
  have hr6 : s₂.gpr .r6 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hk .r6 (by decide), hL.r6, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hy : blockAt s₃.mem (yp s₀) =
      ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 1)) := by
    have hz1 := congrArg Prod.fst hI₂.zv
    simp only at hz1
    rw [hm₃, hr4₂, blockAt_storeMem, ghashFrom_blocksAt_succ, ← hL.y, mul_eq, hz1, hL.r4, hL.r5,
      hL.r3, blockAt_frame (p := hA s₀) hL.frame (by simpa using hp.h_y),
      blockAt_frame (p := blkAddr s₀ i) hL.frame
        (by simpa using hp.y_d.symm.sub_left (hp.blk_sub hi))]
  have hcommon : Common s₀ (i + 1) s₃ := by
    refine ⟨by rw [hk₃ _ (by decide) (by decide) (by decide), hk .r3 (by decide), hL.r3],
      by rw [hk₃ _ (by decide) (by decide) (by decide), hr4₂],
      by rw [hk₃ _ (by decide) (by decide) (by decide), hk .r7 (by decide), hL.r7],
      by rw [hrd₃, hI₂.rd, hL.rd], by rw [hwr₃, hI₂.wr, hL.wr], ?_, hy⟩
    rw [hm₃, hr4₂, hI₂.mem]; exact storeMem_frame hL.frame _ _
  have hev : eval (.nonzero .d .r6) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hr6₃, hr6]
  by_cases hlast : i + 1 = nb s₀
  · left
    rw [hlast, Nat.sub_self] at hev
    exact ⟨hev.trans (by decide), hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with r5 := ?_, r6 := ?_ }⟩
    · have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      exact hev.trans (by simpa using h0)
    · rw [hr5₃, hk .r5 (by decide), hL.r5, blkAddr, blkAddr, Offset.add_add, Nat.mul_succ]
    · rw [hr6₃, hr6]

/-! ## The loop over the blocks -/

theorem common_zero (s₀ : State) : Common s₀ 0 s₀ :=
  ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, (ghashFrom_blocksAt_zero _ _ _ _).symm⟩

/-- The blocks, after the registers are saved. -/
def loops : Prog isa := .ite (.zero .d .r6) (.block []) (.loop body (.nonzero .d .r6))

theorem loops_ok {s₀ : State} (hp : Pre s₀) : WP isa loops s₀ (Common s₀ (nb s₀)) := by
  have hev : eval (.zero .d .r6) s₀ = some (s₀.gpr .r6 == 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  refine WP.ite (s₀.gpr .r6 == 0) hev (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ common_zero s₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .d .r6) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .d .r6) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₀ :=
      { common_zero s₀ with
        r5 := by simp [blkAddr]
        r6 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩

/-! ## The whole function -/

theorem ghash_eq : ghash = .seq (.block save) (.seq loops (.block restore)) := rfl

theorem correct {s₀ : State} (hp₀ : Pre s₀) :
    WP isa ghash s₀ fun s' =>
      (∀ i < 5, s'.gpr (saved i) = s₀.gpr (saved i)) ∧ Proof.Gcm.ghashPPC64LE.post s₀ s' := by
  rw [ghash_eq]
  refine WP.seq (WP.mono (save_ok hp₀) fun s₁ hs₁ => ?_)
  have hp : Pre s₁ := hp₀.congr hs₁.gpr hs₁.rd hs₁.wr
  have hg : ∀ r, s₁.gpr r = s₀.gpr r := fun r => by rw [hs₁.gpr]
  refine WP.seq (WP.mono (loops_ok hp) fun s₂ hc => ?_)
  have hd : ∀ (R : Region), R.Disjoint (scrR s₀) → ∀ r ∈ [scrR s₀], R.Disjoint r := by
    intro R h r hr; simp only [List.mem_singleton] at hr; subst hr; exact h
  have hsav : ∀ i < 5, s₂.mem.readW (s₂.gpr SCR + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i) := by
    intro i hi
    have hc' : (scrR s₁).Contains (scr s₁ + BitVec.ofNat 64 (8 * i)) (64 / 8) :=
      contains_offset (by omega_using [hi]) (by omega_using [hi])
    rw [show s₂.gpr SCR = scr s₁ from hc.r7,
      hc.frame.readW (r := scrR s₁) hc' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.y_scr.symm) (by decide)]
    rw [show scr s₁ = scr s₀ from hg _]
    exact hs₁.saved i hi
  have hin : ∀ i < 5, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr SCR + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hc.rd, hc.wr, show s₂.gpr SCR = scr s₁ from hc.r7]
    exact ⟨scrR s₁, by simp [hp.wr], contains_offset (by omega_using [hi]) (by omega_using [hi])⟩
  refine WP.mono (restore_ok s₂ hin hsav) fun s' hr => ⟨hr.restored, ?_⟩
  show blockAt s'.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (nb s₀))
  have e₁ : yp s₀ = yp s₁ := (hg _).symm
  rw [hr.mem, e₁, hc.y]
  have hH : H₀ s₁ = H₀ s₀ := by
    rw [H₀, H₀, show hA s₁ = hA s₀ from hg _]
    exact blockAt_frame hs₁.frame (hd _ hp₀.h_scr)
  have hY : Y₀ s₁ = Y₀ s₀ := by
    rw [Y₀, Y₀, show yp s₁ = yp s₀ from hg _]
    exact blockAt_frame hs₁.frame (hd _ hp₀.y_scr)
  rw [hH, hY]
  rw [show dp s₁ = dp s₀ from hg _, show nb s₁ = nb s₀ by simp only [nb, hg]]
  exact congrArg _ (blocksAt_frame hp₀ hs₁.frame (hd _ hp₀.d_scr))

/-- The registers the code writes. -/
def written : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15,
  .r16, .r17, .r18]

theorem preserved_cases : ∀ r ∈ preserved, (∃ i < 5, r = saved i) ∨ r ∉ written := by decide

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Gcm.PPC64LE.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashPPC64LE.post s s' := by
  obtain ⟨t, s', he, ⟨hr, h⟩, hkeep⟩ :=
    WP.keep written (correct (pre_of s hs)) (by decide +kernel)
  refine ⟨t, s', he, ⟨fun r hr' => ?_, Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
  rcases preserved_cases r hr' with ⟨i, hi, rfl⟩ | hk
  · exact hr i hi
  · exact hkeep.gpr hk

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashPPC64LE.pre Proof.Gcm.ghashPPC64LE.pub
    Impl.Gcm.PPC64LE.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_verified :
    Verified PPC64LE.target Impl.Gcm.PPC64LE.ghash (Spec.Gcm.ghashContract PPC64LE.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashPPC64LE, PPC64LE.abi,
      PPC64LE.argRegs] [Proof.Gcm.PPC64LE.satState] using Proof.Gcm.PPC64LE.satState)

end VG.Proof.Gcm.PPC64LE
