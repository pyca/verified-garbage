module

import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
public import VerifiedGarbage.Proof.AesGcm.X86_64.Run
public import VerifiedGarbage.Impl.AesGcm.X86_64.Short
public import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import Mathlib.Data.List.Induction
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Aes.SboxSpec
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Frame

/-!
# AES-GCM's short path on x86-64: copying bytes

Untrusted: everything here is checked by Lean. `copyBytes` copies `rcx`
bytes from `rsi` to `rdi`, 16 at a time through `xmm4` and then one at a
time (`copyBytes_ok`); the buffers do not overlap.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)

/-- The vector registers other than `rs` keep their lanes. -/
def ZKeep (rs : List XReg) (s s' : State) : Prop := ∀ r, r ∉ rs → ∀ l < 4, s'.zlane r l = s.zlane r l

theorem ZKeep.refl (rs : List XReg) (s : State) : ZKeep rs s s := fun _ _ _ _ => rfl

theorem ZKeep.trans {rs : List XReg} {s s' s'' : State} (h : ZKeep rs s s') (h' : ZKeep rs s' s'') :
    ZKeep rs s s'' := fun r hr l hl => by rw [h' r hr l hl, h r hr l hl]

theorem ZKeep.mono {rs rs' : List XReg} {s s' : State} (h : ZKeep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    ZKeep rs' s s' := fun r hr l hl => h r (fun h' => hr (hs r h')) l hl

theorem zlane_setReg (s : State) (r : Reg) (v : BitVec 64) (x : XReg) (l : Nat) :
    (s.setReg r v).zlane x l = s.zlane x l := rfl

theorem zlane_arithFlags (s : State) {w : Nat} (v : BitVec w) (c o : Bool) (x : XReg) (l : Nat) :
    (arithFlags s v c o).zlane x l = s.zlane x l := rfl

/-- A 16-byte store of a 16-byte load is a write of the bytes loaded. -/
theorem writeW_readW128 (m src : Mem) (a b : Addr) :
    m.writeW a (src.readW b 128) = writeBytes m a (bytesAt src b 16) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (128 / 8)) (BitVec.setWidth 128 (src.read b (128 / 8)))) =
    src.read b 16 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  exact Mem.extractLsb'_read src b (List.mem_range.mp hj)

/-- The 16-byte loop's body. -/
abbrev copy16Body : List Instr :=
  [.vmovdquLoad .l128 .xmm4 srcB, .vmovdquStore .l128 dstB .xmm4, .alu .add .r10 (imm 16),
    .alu .cmp .r10 (.reg .r8)]

theorem copy16Step_ok (s : State) {S D : Addr} {i k : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hk : s.gpr .r8 = BitVec.ofNat 64 k)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 16) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 16) :
    ∃ s', runBlock isa copy16Body s = some s' ∧
      s'.mem = writeBytes s.mem (D + BitVec.ofNat 64 i) (bytesAt s.mem (S + BitVec.ofNat 64 i) 16) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 16 ∧
      s'.zf = some (BitVec.ofNat 64 i + 16 - BitVec.ofNat 64 k == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [.xmm4] s s' := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  refine ⟨_, by
    simp only [copy16Body, srcB, dstB, imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, State.load128, State.store128, State.ea, e₁, r, ite_true, Option.map_some, Option.bind_some]
    simp only [State.setV, ite_true, e₂, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    exact writeW_readW128 _ _ _ _
  · simp [gpr_setReg, gpr_arithFlags, hi]
  · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk]
  · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
  · intro r hr l hl
    simp only [List.mem_singleton] at hr
    exact (State.zlane_setV128 s .xmm4 r _ 0 hl).trans (by simp [hr])

theorem shl_ofNat {a k : Nat} (h : a * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  have ha : a < 2 ^ 64 := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * 2 ^ k := Nat.mul_le_mul_left a this
      _ < 2 ^ 64 := h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftLeft_eq]

/-- What `copyBytes` needs: `n` bytes to read at `S` and to write at `D`, apart. -/
structure CopyPre (s : State) (S D : Addr) (n : Nat) : Prop where
  rsi : s.gpr .rsi = S
  rdi : s.gpr .rdi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  lt : n < 2 ^ 63
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- What `copyBytes` leaves. -/
def CopyPost (s : State) (S D : Addr) (n : Nat) (s' : State) : Prop :=
  s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    ZKeep [.xmm4] s s'

theorem in_of_covers16 {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i + 16 ≤ n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 16 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p hi (by omega)⟩

/-- The setup: `r10 = 0` and `r8 = 16 ⌊n / 16⌋`. -/
theorem copySetup_ok (s : State) {n : Nat} (hn : s.gpr .rcx = BitVec.ofNat 64 n) (hlt : n < 2 ^ 63) :
    WP isa (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 4, .shift .shl .r8 4,
        .alu .cmp .r8 (imm 0)]) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 0 ∧ s'.gpr .r8 = BitVec.ofNat 64 (16 * (n / 16)) ∧
      s'.zf = some (decide (16 * (n / 16) = 0)) ∧
      (∀ r, r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ZKeep [] s s' := by
  have e₁ : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := shr4 n (by omega)
  have e₂ : BitVec.ofNat 64 (n / 16) <<< 4 = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [shl_ofNat (by omega)]; congr 1; omega
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, hn, e₁, e₂], ?_⟩
  refine ⟨by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags], by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags],
    ?_, fun r h₁ h₂ => by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂], rfl, rfl, rfl,
    fun _ _ _ _ => rfl⟩
  simp only [zf_arithFlags]
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, sub_beq (by omega) (by decide)]

/-- A 64-byte store of a 64-byte load is a write of the bytes loaded. -/
theorem writeW_readW512 (m src : Mem) (a b : Addr) :
    m.writeW a (src.readW b 512) = writeBytes m a (bytesAt src b 64) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (512 / 8)) (BitVec.setWidth 512 (src.read b (512 / 8)))) =
    src.read b 64 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  exact Mem.extractLsb'_read src b (List.mem_range.mp hj)

/-- The 512-bit register written by lanes from a value holds it. -/
theorem zmm_setZ_lanes (s : State) (d : XReg) (v : BitVec 512) :
    (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128)).zmm d = v := by
  simp only [State.zmm, State.ymm, State.setZ, ite_true]
  exact StraightZ.split_eq v

/-- The 64-byte loop's body. -/
abbrev copy64Body : List Instr :=
  [.vmovdqu32Load .xmm4 srcB, .vmovdqu32Store dstB .xmm4, .alu .add .r10 (imm 64),
    .alu .cmp .r10 (.reg .r8)]

theorem copy64Step_ok (s : State) {S D : Addr} {i k : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hk : s.gpr .r8 = BitVec.ofNat 64 k)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 64) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 64) :
    ∃ s', runBlock isa copy64Body s = some s' ∧
      s'.mem = writeBytes s.mem (D + BitVec.ofNat 64 i) (bytesAt s.mem (S + BitVec.ofNat 64 i) 64) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 64 ∧
      s'.zf = some (BitVec.ofNat 64 i + 64 - BitVec.ofNat 64 k == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [.xmm4] s s' := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  refine ⟨_, by
    simp only [copy64Body, srcB, dstB, imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, State.load512, State.store512, State.ea, e₁, r, ite_true, Option.map_some, Option.bind_some]
    simp only [State.setZ_ea, State.setZ_wr, State.setZ_gpr, e₂, zmm_setZ_lanes, w, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    exact writeW_readW512 _ _ _ _
  · simp [gpr_setReg, gpr_arithFlags, hi]
  · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk]
  · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
  · intro r hr l hl
    simp only [List.mem_singleton] at hr
    exact (State.zlane_setZ s .xmm4 r _ _ _ _ hl).trans (by simp [hr])

/-- The setup: `r10 = 0` and `r8 = 64 ⌊n / 64⌋`. -/
theorem copySetup64_ok (s : State) {n : Nat} (hn : s.gpr .rcx = BitVec.ofNat 64 n) (hlt : n < 2 ^ 63) :
    WP isa (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 6, .shift .shl .r8 6,
        .alu .cmp .r8 (imm 0)]) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 0 ∧ s'.gpr .r8 = BitVec.ofNat 64 (64 * (n / 64)) ∧
      s'.zf = some (decide (64 * (n / 64) = 0)) ∧
      (∀ r, r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ZKeep [] s s' := by
  have e₁ : BitVec.ofNat 64 n >>> 6 = BitVec.ofNat 64 (n / 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  have e₂ : BitVec.ofNat 64 (n / 64) <<< 6 = BitVec.ofNat 64 (64 * (n / 64)) := by
    rw [shl_ofNat (by omega)]; congr 1; omega
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, hn, e₁, e₂], ?_⟩
  refine ⟨by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags], by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags],
    ?_, fun r h₁ h₂ => by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂], rfl, rfl, rfl,
    fun _ _ _ _ => rfl⟩
  simp only [zf_arithFlags]
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, sub_beq (by omega) (by decide)]

/-! ## The masked tail -/

theorem range_filter_lt (r : Nat) : ∀ n, (List.range n).filter (fun j => decide (j < r)) = List.range (min n r)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, range_filter_lt r n]
    by_cases h : n < r
    · simp only [List.filter_cons, List.filter_nil, decide_eq_true h, ↓reduceIte]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), List.range_succ]
    · simp only [List.filter_cons, List.filter_nil, decide_eq_false h, Bool.false_eq_true, ↓reduceIte,
        List.append_nil]
      rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

/-- The bytes the mask `2 ^ r - 1` enables are the first `r`. -/
theorem bOn_low {r : Nat} (hr : r < 64) : State.bOn (BitVec.ofNat 64 (2 ^ r - 1)) = List.range r := by
  simp only [State.bOn]
  rw [List.filter_congr (q := fun j => decide (j < r)) fun j hj => by
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    simp [List.mem_range.mp hj]]
  rw [range_filter_lt, Nat.min_eq_right (by omega)]

/-- Byte writes at `D`, `D + 1`, … of `g 0`, `g 1`, … are a write of their list. -/
theorem foldl_bwrites_range (g : Nat → Byte) (D : Addr) :
    ∀ (r : Nat) (m : Mem), r < 2 ^ 64 →
      (List.range r).foldl (fun m j => m.writeW (D + BitVec.ofNat 64 j) (g j)) m =
        writeBytes m D ((List.range r).map g)
  | 0, m, _ => by simp [writeBytes_nil]
  | r + 1, m, hr => by
    rw [List.range_succ, List.foldl_append, foldl_bwrites_range g D r m (by omega), List.map_append,
      List.map_singleton, writeBytes_snoc _ _ _ _ (by simp; omega)]
    simp

/-- Byte `j` of a 512-bit little-endian read. -/
theorem readW512_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 64) :
    (m.readW a 512).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 64) hj,
    show m.readW a 512 = m.read a 64 from by simp [Mem.readW]]

/-- `2 ^ k - 1` as `1` shifted left by `k`, less one. -/
theorem shl_one_sub_one {k : Nat} (hk : k < 64) :
    (1#64 <<< k) - 1#64 = BitVec.ofNat 64 (2 ^ k - 1) := by
  have hp : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    show 1 % 2 ^ 64 = 1 from rfl, Nat.one_mul]
  generalize 2 ^ k = p at hp h1
  omega

/-- The mask of the tail: `rax = 2 ^ (rcx mod 64) - 1`. -/
theorem maskSetup_ok (s : State) {k : Nat} (hn : (s.gpr .rcx).toNat % 64 = k) :
    WP isa (.block [.mov32 .rax (imm 1), .shiftCl .shl .rax, .alu .sub .rax (imm 1)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (2 ^ k - 1) ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [] s t := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShiftCl], ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr], rfl, rfl, rfl,
    fun _ _ _ _ => rfl⟩
  have hk : k < 64 := hn ▸ Nat.mod_lt _ (by decide)
  simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hn]
  simpa [VarShiftOp.eval] using shl_one_sub_one hk

/-- The mask `2 ^ k - 1` enables byte `j` if `j < k`. -/
theorem getLsbD_low {k j : Nat} (hj : j < k) (hk : k < 64) : (BitVec.ofNat 64 (2 ^ k - 1)).getLsbD j = true := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- A masked load of the `k` bytes at `A` (`srcB`), and a masked store of them at `B` (`dstB`),
with the mask `2 ^ k - 1` in `rax`. -/
theorem kCopy_ok (t : State) {A B : Addr} {k : Nat} (hk : k < 64)
    (ha : t.ea srcB = A) (hb : t.ea dstB = B) (hm : t.gpr .rax = BitVec.ofNat 64 (2 ^ k - 1))
    (r : ∀ j < k, InRegions (t.rd ++ t.wr) (A + BitVec.ofNat 64 j) 1)
    (w : ∀ j < k, InRegions t.wr (B + BitVec.ofNat 64 j) 1) :
    WP isa (.block [.kLoad8 .rax .xmm4 srcB, .kStore8 dstB .rax .xmm4]) t fun t' =>
      t'.mem = writeBytes t.mem B (bytesAt t.mem A k) ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ZKeep [.xmm4] t t' := by
  have hon := bOn_low hk
  generalize hV : Mem.readW (fun x => if (BitVec.ofNat 64 (2 ^ k - 1)).getLsbD (x - A).toNat then t.mem x else 0)
    A 512 = V
  have hl : t.loadMasked512B A (BitVec.ofNat 64 (2 ^ k - 1)) = some V := by
    unfold State.loadMasked512B
    rw [ite_eq_left (by rw [hon]; exact fun j hj => r j (List.mem_range.mp hj)), hV]
  generalize ht₁ : t.setZ .xmm4 (V.extractLsb' 0 128) (V.extractLsb' 128 128) (V.extractLsb' 256 128)
    (V.extractLsb' 384 128) = t₁
  have e₁ : exec (.kLoad8 .rax .xmm4 srcB) t = some t₁ := by
    simp only [exec, ha, hm, hl, Option.map_some, ht₁]
  have hz : t₁.zmm .xmm4 = V := by rw [← ht₁]; exact zmm_setZ_lanes t .xmm4 V
  have hs : t₁.storeMasked512B B (BitVec.ofNat 64 (2 ^ k - 1)) V =
      some { t₁ with mem := ((List.range k).foldl
        (fun m j => m.writeW (B + BitVec.ofNat 64 j) (V.extractLsb' (8 * j) 8)) t₁.mem) } := by
    unfold State.storeMasked512B
    rw [hon, ite_eq_left (by
      rw [← ht₁, State.setZ_wr]; exact fun j hj => w j (List.mem_range.mp hj))]
  have e₂ : exec (.kStore8 dstB .rax .xmm4) t₁ = some { t₁ with mem := ((List.range k).foldl
        (fun m j => m.writeW (B + BitVec.ofNat 64 j) (V.extractLsb' (8 * j) 8)) t₁.mem) } := by
    simp only [exec]
    rw [← hs, hz, ← hb, ← hm, ← ht₁, State.setZ_ea, State.setZ_gpr]
  refine WP.block_cons_iff.mpr ⟨_, e₁, WP.block_cons_iff.mpr ⟨_, e₂, WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · simp only
    rw [foldl_bwrites_range _ _ _ _ (by omega), ← ht₁, State.setZ_mem]
    congr 1
    simp only [bytesAt]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    rw [← hV, readW512_byte _ _ (by omega), Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), getLsbD_low hj hk]
    rfl
  · simp only; rw [← ht₁, State.setZ_gpr]
  · simp only; rw [← ht₁, State.setZ_rd]
  · simp only; rw [← ht₁, State.setZ_wr]
  · intro x hx l hl
    simp only [List.mem_singleton] at hx
    show t₁.zlane x l = t.zlane x l
    rw [← ht₁, State.zlane_setZ t .xmm4 x _ _ _ _ hl]
    simp [hx]

theorem in_of_covers64 {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i + 64 ≤ n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 64 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p hi (by omega)⟩

theorem copyBytes_ok (s : State) {S D : Addr} {n : Nat} (h : CopyPre s S D n) :
    WP isa copyBytes s (CopyPost s S D n) := by
  have hn63 := h.lt
  refine WP.seq (WP.mono (copySetup64_ok s h.rcx h.lt) fun s₁ ⟨r10₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  -- After the 64-byte loop: the first `64 ⌊n / 64⌋` bytes copied.
  let q := n / 64
  have mid : WP isa (.ite .e (.block []) (.loop (.block copy64Body) .ne)) s₁ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 (64 * q) ∧ t.mem = writeBytes s.mem D (bytesAt s.mem S (64 * q)) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm4] s t := by
    refine WP.ite (decide (64 * q = 0)) (by simp only [eval, zf₁, q]) (fun hz => ?_) (fun hz => ?_)
    · have hq : 64 * q = 0 := of_decide_eq_true hz
      refine WP.block_nil ⟨by rw [r10₁, hq], by rw [m₁, hq]; simp [bytesAt, writeBytes_nil],
        fun r a b c => g₁ r b c, rd₁, wr₁, z₁.mono (by simp)⟩
    · have hq : 0 < q := by have := of_decide_eq_false hz; omega
      refine WP.loop (M := isa) (body := .block copy64Body) (c := .ne)
        (fun (k : Nat) (t : State) => ∃ j, k = q - j ∧ j < q ∧ t.gpr .r10 = BitVec.ofNat 64 (64 * j) ∧
          t.mem = writeBytes s.mem D (bytesAt s.mem S (64 * j)) ∧
          (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
          t.gpr .r8 = BitVec.ofNat 64 (64 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t) ?_ (q - 0) _
        ⟨0, rfl, hq, by rw [r10₁], by rw [m₁]; simp [bytesAt, writeBytes_nil], fun r a b c => g₁ r b c,
          r8₁, rd₁, wr₁, z₁.mono (by simp)⟩
      rintro k t ⟨j, rfl, hj, r10, mem, g, r8, rd, wr, z⟩
      have hj64 : 64 * j + 64 ≤ n := by omega
      obtain ⟨t', run', mem', r10', zf', g', rd', wr', z'⟩ := copy64Step_ok t
        (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
        (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10 r8
        (by rw [rd, wr]; exact in_of_covers64 h.rd hj64 (by omega))
        (by rw [wr]; exact in_of_covers64 h.wr hj64 (by omega))
      refine WP.of_runBlock ⟨t', run', ?_⟩
      have hlen : (bytesAt s.mem S (64 * j)).length = 64 * j := length_bytesAt _ _ _
      have hsrc : bytesAt t.mem (S + BitVec.ofNat 64 (64 * j)) 64 = bytesAt s.mem (S + BitVec.ofNat 64 (64 * j)) 64 := by
        rw [mem]
        refine bytesAt_frame (writeBytes_frame' s.mem hlen) (fun r hr => ?_) (by decide)
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.disj.sub_left (Offset.sub_base S hj64)).sub_right (Region.sub_prefix (by omega))
      have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (64 * (j + 1))) := by
        rw [mem', hsrc, mem, show 64 * (j + 1) = 64 * j + 64 by omega, bytesAt_add]
        conv => lhs; rw [show D + BitVec.ofNat 64 (64 * j) = D + BitVec.ofNat 64 (bytesAt s.mem S (64 * j)).length
          by rw [hlen]]
        exact writeBytes_append s.mem D (bytesAt s.mem S (64 * j)) (bytesAt s.mem (S + BitVec.ofNat 64 (64 * j)) 64)
          (by rw [length_bytesAt, length_bytesAt]; omega)
      have hz : t'.zf = some (decide (j + 1 = q)) := by
        rw [zf', show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ofNat_add_ofNat, sub_beq (by omega) (by omega)]
        congr 1; simp only [decide_eq_decide]; omega
      have gg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c => by
        rw [g' r c, g r a b c]
      have r10'' : t'.gpr .r10 = BitVec.ofNat 64 (64 * (j + 1)) := by
        rw [r10', show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ofNat_add_ofNat]; congr 1
      by_cases he : j + 1 = q
      · left
        refine ⟨by simp [eval, hz, he], by rw [r10'', he], by rw [hmem, he], gg, by rw [rd', rd],
          by rw [wr', wr], z.trans z'⟩
      · right
        refine ⟨by simp [eval, hz, he], q - (j + 1), by omega, j + 1, rfl, by omega, r10'', hmem, gg,
          by rw [g' _ (by decide), r8], by rw [rd', rd], by rw [wr', wr], z.trans z'⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨r10₂, m₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- The last `n mod 64` bytes, in one masked move.
  have hcx : s₂.gpr .rcx = BitVec.ofNat 64 n := by rw [g₂ _ (by decide) (by decide) (by decide), h.rcx]
  have hk : (s₂.gpr .rcx).toNat % 64 = n % 64 := by
    rw [hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (b := 2 ^ 64) (by omega)]
  rw [show ([.mov32 .rax (imm 1), .shiftCl .shl .rax, .alu .sub .rax (imm 1), .kLoad8 .rax .xmm4 srcB,
      .kStore8 dstB .rax .xmm4] : List Instr) = [.mov32 .rax (imm 1), .shiftCl .shl .rax, .alu .sub .rax (imm 1)] ++
      [.kLoad8 .rax .xmm4 srcB, .kStore8 dstB .rax .xmm4] from rfl, WP.block_append_iff]
  refine WP.mono (maskSetup_ok s₂ hk) fun s₃ ⟨rax₃, g₃, m₃, rd₃, wr₃, z₃⟩ => ?_
  have hg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r a b c => by
    rw [g₃ r a, g₂ r a b c]
  have r10₃ : s₃.gpr .r10 = BitVec.ofNat 64 (64 * q) := by rw [g₃ _ (by decide), r10₂]
  have hA : s₃.ea srcB = S + BitVec.ofNat 64 (64 * q) :=
    ea_idx s₃ .rsi (by rw [hg _ (by decide) (by decide) (by decide), h.rsi]) r10₃
  have hB : s₃.ea dstB = D + BitVec.ofNat 64 (64 * q) :=
    ea_idx s₃ .rdi (by rw [hg _ (by decide) (by decide) (by decide), h.rdi]) r10₃
  have hqn : 64 * q + n % 64 = n := by omega
  refine WP.mono (kCopy_ok s₃ (Nat.mod_lt _ (by decide)) hA hB rax₃
    (fun j hj => by
      rw [rd₃, wr₃, rd₂, wr₂, Offset.add_add]; exact in_of_covers h.rd (by omega) (by omega))
    (fun j hj => by
      rw [wr₃, wr₂, Offset.add_add]; exact in_of_covers h.wr (by omega) (by omega)))
    fun s₄ ⟨m₄, g₄, rd₄, wr₄, z₄⟩ => ?_
  have hlen : (bytesAt s.mem S (64 * q)).length = 64 * q := length_bytesAt _ _ _
  have hsrc : bytesAt s₃.mem (S + BitVec.ofNat 64 (64 * q)) (n % 64) =
      bytesAt s.mem (S + BitVec.ofNat 64 (64 * q)) (n % 64) := by
    rw [m₃, m₂]
    refine bytesAt_frame (writeBytes_frame' s.mem hlen) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.disj.sub_left (Offset.sub_base S (by omega : 64 * q + n % 64 ≤ n))).sub_right
      (Region.sub_prefix (by omega))
  refine ⟨?_, fun r a b c => by rw [g₄, hg r a b c], by rw [rd₄, rd₃, rd₂], by rw [wr₄, wr₃, wr₂],
    z₂.trans ((z₃.mono (by simp)).trans z₄)⟩
  rw [m₄, hsrc, m₃, m₂]
  conv => lhs; rw [show D + BitVec.ofNat 64 (64 * q) = D + BitVec.ofNat 64 (bytesAt s.mem S (64 * q)).length
    by rw [hlen]]
  rw [writeBytes_append s.mem D _ _ (by rw [length_bytesAt, length_bytesAt]; omega), ← bytesAt_add, hqn]

end VG.Proof.AesGcm.X86_64.Short
