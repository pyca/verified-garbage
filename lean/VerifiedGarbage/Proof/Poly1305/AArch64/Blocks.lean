module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Poly1305.AArch64
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
public import VerifiedGarbage.Proof.Poly1305.Spec
public import VerifiedGarbage.Proof.Poly1305.Radix26
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Contract
meta import VerifiedGarbage.Proof.Poly1305.Contract

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.AArch64.Steps`.
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.Poly1305.AArch64
meta import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
meta import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Spec.Poly1305.Contract
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

section

section

/-!
# Poly1305 on AArch64: the arithmetic in radix `2²⁶`

The numbers the code computes, as natural numbers (`Proof/Poly1305/Radix26.lean`).
-/

namespace VG.Proof.Poly1305.AArch64

export VG.Proof.Poly1305.Radix26 (val5 lim lim0 lim1 lim2 lim3 lim4 val5_lim lim_lt lim4_lt split_arith product_identity mul_lt' dsum_arith val5_lt val5_le dm26 mod64 carry_arith reduce_arith pack_arith addCarry_arith)

end VG.Proof.Poly1305.AArch64

end

/-!
# Poly1305 on AArch64: the steps of the code

Each lemma runs a few instructions symbolically and states their effect on the
numbers in the registers, unconditionally (modulo `2⁶⁴` where the code wraps).
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64

/-- Two states agree except on the registers `rs`, in memory and regions. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-! ## Numbers -/

theorem lsr_toNat (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end VG.Proof.Poly1305.AArch64

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.AArch64.Setup`.
section

section

/-!
# Poly1305 on AArch64: absorbing a block
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P)

/-- The 64-bit word at `p + d`, as a number. -/
abbrev w64 (m : Mem) (p : Addr) (d : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 d) 64).toNat

end VG.Proof.Poly1305.AArch64

end

section

/-!
# Poly1305 on AArch64: the state in memory
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (off base d) n := Offset.contains_base base h hd

theorem sep_off (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 16)
    (hk : k ≤ 16) (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (off p d) n (off p e) k := Offset.sep p h (by omega_using [hd, hn]) (by omega_using [he, hk])

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (sep_off p hd he (by decide) (by decide) h) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨off st 24, 32⟩
/-- The working space. -/
abbrev wR : Region := ⟨off st 56, 72⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨off st d, n⟩ (sR st) :=
  Offset.sub_base st h

theorem kR_disjoint (st : Addr) : ∀ r ∈ [hR st, wR st], (kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint_base st (by decide) (by decide)
  · exact Offset.disjoint st (by decide) (by decide) (by decide)

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') :
    bytesAt m' (off st 24) 32 = bytesAt m (off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := kR st) (kR_disjoint st) (by simp only [Nat.reducePow, Nat.reduceLeDiff]) (List.mem_range.mp hi)

theorem hR_contains (st : Addr) {d : Nat} (h : d + 8 ≤ 24) : (hR st).Contains (off st d) 8 :=
  contains_off h (by omega_using [h])

/-! ## The accumulator and the key as numbers -/

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem add_ofNat_add (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := Offset.add_add p d e

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = w64 m st 0 + 2 ^ 64 * w64 m st 8 + 2 ^ 128 * w64 m st 16 := by
  rw [Poly1305.leNum_bytesAt_24, w64, add_ofNat_zero]
  rfl

/-- The key stored in the state is the 32 bytes at `off st 24`. -/
theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (off st 24) 32).take 16 = bytesAt m (off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add, List.take_left' (Poly1305.length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (off st 24) 32).drop 16).take 16 = bytesAt m (off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add, List.drop_left' (Poly1305.length_bytesAt _ _ _),
    List.take_of_length_le (by rw [Poly1305.length_bytesAt])]
  congr 1
  simp only [off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = w64 m p 0 + 2 ^ 64 * w64 m p 8 := by
  rw [Poly1305.leNum_bytesAt_16, w64, add_ofNat_zero]
  rfl

theorem off_off (p : Addr) (d e : Nat) : off (off p d) e = off p (d + e) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The clamping masks. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

/-- The clamped `r` of the key in the state. -/
abbrev Rk (m : Mem) (st : Addr) : Nat :=
  (m.readW (off st 24) 64 &&& M0).toNat + 2 ^ 64 * (m.readW (off st 32) 64 &&& M1).toNat

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (off st 24) 32).take 16)) = Rk m st := by
  rw [key_take, leNum_key, w64, w64, off, add_ofNat_zero, add_ofNat_add, Poly1305.clamp_words]

end VG.Proof.Poly1305.AArch64

end

/-!
# Poly1305 on AArch64: the coefficients and the accumulator on entry
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-- The coefficients' region. -/
abbrev cR (st : Addr) : Region := ⟨off st 72, 36⟩

end VG.Proof.Poly1305.AArch64

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.AArch64.Blocks`.
section

/-!
# Poly1305 on AArch64: `blocks`
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.AArch64 in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let key : Region := ⟨s.gpr .x1, 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key
  post s s' := Repr s'.mem (s.gpr .x0) (bytesAt s.mem (s.gpr .x1) 32) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n:
usize)`. -/
def blocksAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let blocks : Region := ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .x1).toNat + 16 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .x0) key msg →
    Repr s'.mem (s.gpr .x0) key (msg ++ bytesAt s.mem (s.gpr .x1) (16 * (s.gpr .x2).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

open VG.AArch64 in
/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len:
usize, …)`: only `count mod 16`, the number of bytes buffered, matters. The
state must be writable, and it may be permitted to write other regions (which it
does not). -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    s.rd = [data] ∧ state ∈ s.wr ∧ state.Disjoint data
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .x0) key msg →
    (s.gpr .x1).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .x0) key (msg ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16],
…)`: only `count mod 16`, the number of bytes buffered, matters. The state and
`out` must be writable, and it may be permitted to write other regions (which it
does not). -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let out : Region := ⟨s.gpr .x2, 16⟩
    state ∈ s.wr ∧ out ∈ s.wr ∧ state.Disjoint out
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .x0) key msg →
    (s.gpr .x1).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .x2) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-! ## Common to `blocks` and `finalize` -/

section
variable (s₀ : State)
/-- The state, on entry. -/
abbrev st : Addr := s₀.gpr .x0
/-- The clamped `r`. -/
abbrev Rn : Nat := Rk s₀.mem (st s₀)
/-- The accumulator on entry. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem (st s₀) 24)
end

theorem cR_sub_sR (st : Addr) : Region.Sub (cR st) (sR st) := sub_sR st (by decide)

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem A0_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : A0 s₀ < P := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2] at this
  exact this

theorem off_24 (p : Addr) : off p 24 = p + 24 := rfl

/-- The key of a state that represents a message, and its clamped `r`. -/
theorem repr_key {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    bytesAt s₀.mem (off (st s₀) 24) 32 = key := h.2.1

theorem repr_acc {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    accumulate (Rn s₀) msg = A0 s₀ := by
  rw [A0, h.2.2, ← repr_key h, clamp_key]

/-- The words of `h` stored. -/
def storeHm (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) : Mem :=
  ((m.writeW (off st 0) w0).writeW (off st 8) w1).writeW (off st 16) w2

theorem storeHm_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') (w0 w1 w2 : BitVec 64) :
    Frame [hR st, wR st] m (storeHm m' st w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd => hR_contains st hd
  exact ((hf.writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

set_option simprocs false in
theorem storeHm_acc (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) :
    leNum (bytesAt (storeHm m st w0 w1 w2) st 24) = w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat := by
  rw [leNum_acc]
  simp (config := {decide := true}) only [w64, storeHm, readW_writeW_off,
    Mem.readW_writeW_self64]

/-- No instruction of `c` writes a callee-saved register. -/
def Untouched (c : Prog isa) : Prop := ∀ r ∈ preserved, ∀ i ∈ instrs c, clobbers i r = false

theorem Untouched.of_all {c : Prog isa}
    (h : ((instrs c).all fun i => preserved.all fun r => !clobbers i r) = true) : Untouched c := by
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-! ## `blocks` -/

section
variable (s₀ : State)
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev blR : Region := ⟨bp s₀, 16 * nb s₀⟩
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (bp s₀) (16 * i)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksAArch64.pre s₀) : BPre s₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  have := (bp s₀).isLt
  by_contra h
  refine hp.st_bl (st s₀) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.zero_add, Nat.reduceLeDiff]) ?_
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega_using [h, this]

theorem blk_contains {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := hp.nb_lt
  rw [blkAddr, Offset.add_add]
  exact contains_off (by omega_using [hi, hd]) (by omega_using [hi, hd, this])

/-- Block words, in memory the code has written only in the coefficients. -/
theorem blk_word {m : Mem} (hf : Frame [cR (st s₀)] s₀.mem m) {i d : Nat} (hi : i < nb s₀)
    (hd : d + 8 ≤ 16) :
    m.readW (blkAddr s₀ i + BitVec.ofNat 64 d) 64 = s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 d) 64 :=
  hf.readW (hp.blk_contains hi hd) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.st_bl.symm.sub_right (cR_sub_sR _)) (by decide)

end BPre

set_option simprocs false in
theorem advance_ok (s : State) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 16 ∧ s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1 ∧
      Keeps [.x1, .x2] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, runBlock_cons, runStep_some, runBlock_nil,
    exec_addImm_x (show 16 < 4096 by decide), exec_subImm_x (show 1 < 4096 by decide), State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, by simp only [RegUpd.mem_write], by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2, hr.1, ite_false, RegUpd.gpr_write]

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value {s₀ : State} (hp : BPre s₀) {m : Mem} (hf : Frame [cR (st s₀)] s₀.mem m)
    {i : Nat} (hi : i < nb s₀) :
    w64 m (blkAddr s₀ i) 0 + 2 ^ 64 * w64 m (blkAddr s₀ i) 8 + 2 ^ 128 * true.toNat =
      leNum (bytesAt s₀.mem (blkAddr s₀ i) 16 ++ [0x01]) := by
  simp only [w64]
  rw [hp.blk_word hf hi (by decide), hp.blk_word hf hi (by decide), Poly1305.leNum_append,
    Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem (blkAddr s₀ i) 16 := by
  simp only [blks, blkAddr]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]

end VG.Proof.Poly1305.AArch64

end
