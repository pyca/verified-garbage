module

import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Finish
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
public import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
public import VerifiedGarbage.Impl.X86_64Scal
public import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `ChaCha20Poly1305.X86_64.Stitch.StoreRow`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.X86_64.Stitch.Chunk`, which the modules that import this one used -/

section

/-!
# ChaCha20 and Poly1305 together (x86-64): the blocks of Poly1305

A chunk's double rounds absorb the blocks at `rsi + 16 j` with the scalar
Poly1305, as `vg_poly1305_blocks` does, into the accumulator in `r11`,
`rbx`, `rbp`, under the clamped key in `r8`–`r10` (`Acc`), each in two
pieces: `Stitch.addProd j` (`addProd_ok`, from `prodsS_ok`), which leaves the
products of the sum (`Half`), and the carry (`carry1_ok`, from `carrySP_ok`).
The pieces read memory and write only Poly1305's registers (`absorbRegs`),
and no vector register (`WP.vecKeep`), so ChaCha20's quarter rounds, which
they run between, keep their state; `Acc` and `Half` read only registers,
which the quarter rounds keep.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.Poly1305.X86_64 (hval prodsS_ok carrySP_ok ProdsS Keeps absorbRegs)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (absorbAll)

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-- The clamped key `r = r0 + 2⁶⁴ r1`, as `setup` computes it. -/
structure Key (R0 R1 : BitVec 64) : Prop where
  r0 : R0.toNat < 2 ^ 60
  r1 : R1.toNat < 2 ^ 60
  r1_mod : R1.toNat % 4 = 0

/-- The key as a number. -/
abbrev rN (R0 R1 : BitVec 64) : Nat := R0.toNat + 2 ^ 64 * R1.toNat

/-- Poly1305's registers: the key `R0, R1` (and `s1 = 5 r1 / 4`) and an
accumulator congruent to `X`, partially reduced. -/
structure Acc (R0 R1 : BitVec 64) (X : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = R0
  r9 : s.gpr .r9 = R1
  r10 : (s.gpr .r10).toNat = 5 * (R1.toNat / 4)
  h2 : (s.gpr .rbp).toNat ≤ 4
  val : hval s % P = X % P

theorem scal_addProd (j : Nat) : scalCode (.block (addProd j)) = true := by
  simp only [scalCode, addProd, Impl.Poly1305.X86_64.addBlockAt,
    Impl.Poly1305.X86_64.productsS, Impl.Poly1305.X86_64.mulTo, Impl.Poly1305.X86_64.mulAdd,
    List.cons_append, List.nil_append, List.all_cons, List.all_nil, scalarI, Bool.and_true]

theorem scal_carry : scalCode (.block Impl.Poly1305.X86_64.carryS) = true := by
  simp only [scalCode, Impl.Poly1305.X86_64.carryS, List.all_cons, List.all_nil, scalarI, Bool.and_true]

/-- A block's two words and the bit above them, as `leNum` of its bytes and `0x01`. -/
theorem block_num (m : Mem) (p : Addr) (d : Nat) :
    Proof.Poly1305.X86_64.word m p d + 2 ^ 64 * Proof.Poly1305.X86_64.word m p (d + 8) +
      2 ^ 128 * (1 : BitVec 32).toNat =
      leNum (bytesAt m (p + BitVec.ofNat 64 d) 16 ++ [0x01]) := by
  rw [VG.Proof.Poly1305.leNum_append, VG.Proof.Poly1305.length_bytesAt,
    VG.Proof.Poly1305.leNum_bytesAt_16]
  simp only [Proof.Poly1305.X86_64.word, Proof.Poly1305.X86_64.ofInt_natCast]
  rw [show p + BitVec.ofNat 64 d + 8 = p + BitVec.ofNat 64 (d + 8) by
    rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  have h2 : (1 : BitVec 32).toNat = 1 := rfl
  rw [h1, h2]

/-- Halfway through a block (after `addProd`): the products of the sum of the
accumulator and the block, whose carry leaves an accumulator congruent to
`Y`, under the key. -/
structure Half (R0 R1 : BitVec 64) (Y : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = R0
  r9 : s.gpr .r9 = R1
  r10 : (s.gpr .r10).toNat = 5 * (R1.toNat / 4)
  prods : ∃ a0 a1 a2, ((a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2) * rN R0 R1) % P = Y % P ∧
    ProdsS a0 a1 a2 R0.toNat (R1.toNat / 4) s

/-- `Acc` and `Half` read only registers. -/
theorem Acc.of_gpr {R0 R1 : BitVec 64} {X : Nat} {s s' : State} (hg : s'.gpr = s.gpr)
    (h : Acc R0 R1 X s) : Acc R0 R1 X s' :=
  ⟨by rw [hg]; exact h.r8, by rw [hg]; exact h.r9, by rw [hg]; exact h.r10, by rw [hg]; exact h.h2,
    by simp only [hval, hg]; exact h.val⟩

theorem Half.of_gpr {R0 R1 : BitVec 64} {Y : Nat} {s s' : State} (hg : s'.gpr = s.gpr)
    (h : Half R0 R1 Y s) : Half R0 R1 Y s' := by
  obtain ⟨a0, a1, a2, e, hP⟩ := h.prods
  exact ⟨by rw [hg]; exact h.r8, by rw [hg]; exact h.r9, by rw [hg]; exact h.r10, a0, a1, a2, e,
    ⟨hP.ha0, hP.ha1, hP.ha2, hP.hr0, hP.hq, by rw [hg]; exact hP.x, by rw [hg]; exact hP.y,
      by rw [hg]; exact hP.z⟩⟩

/-- The first piece of the block at `rsi + 16 j`. -/
theorem addProd_ok {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {s : State} (h : Acc R0 R1 X s)
    {p : Addr} (hp : s.gpr .rsi = p) {j : Nat}
    (hin : ∀ e, e + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * j + e)) 8) :
    WP isa (.block (addProd j)) s fun s' =>
      Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem (p + BitVec.ofNat 64 (16 * j)) 16)) s' ∧
      Keeps absorbRegs s s' ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  have hq : R1.toNat / 4 < 2 ^ 58 := by have := hk.r1; omega_arith
  have hr1 : (s.gpr .r9).toNat = 4 * (R1.toNat / 4) := by rw [h.r9]; have := hk.r1_mod; omega_arith
  have i0 := hin 0 (by decide)
  have i8 := hin 8 (by decide)
  rw [Nat.add_zero] at i0
  refine WP.mono (WP.vecKeep (scal_addProd _) (prodsS_ok s (b := .rsi) (d := 16 * j) (by decide)
    (Or.inr rfl) (by rw [h.r8]; exact hk.r0) hr1 hq h.r10
    (by rw [hp, Proof.Poly1305.X86_64.ofInt_natCast]; exact i0)
    (by rw [hp, Proof.Poly1305.X86_64.ofInt_natCast]; exact i8)))
    fun s' ⟨⟨ha, k⟩, vx, vy⟩ => ⟨?_, k, vx, vy⟩
  obtain ⟨a0, a1, a2, ea, hP⟩ := ha h.h2
  rw [h.r8] at hP
  refine ⟨by rw [k.gpr' (r := .r8), h.r8], by rw [k.gpr' (r := .r9), h.r9],
    by rw [k.gpr' (r := .r10), h.r10], a0, a1, a2, ?_, hP⟩
  have hb1 : 0 < (bytesAt s.mem (p + BitVec.ofNat 64 (16 * j)) 16).length := by
    rw [VG.Proof.Poly1305.length_bytesAt]; decide
  have hb2 : (bytesAt s.mem (p + BitVec.ofNat 64 (16 * j)) 16).length ≤ 16 := by
    rw [VG.Proof.Poly1305.length_bytesAt]
  rw [ea, hp, block_num, mod_step h.val, VG.Proof.Poly1305.absorbAll_block hb1 hb2, Nat.mod_mod]

/-- The second piece, the carry. -/
theorem carry1_ok {R0 R1 : BitVec 64} (hk : Key R0 R1) {Y : Nat} {s : State} (h : Half R0 R1 Y s) :
    WP isa (.block Impl.Poly1305.X86_64.carryS) s fun s' =>
      Acc R0 R1 Y s' ∧ Keeps absorbRegs s s' ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  obtain ⟨a0, a1, a2, ea, hP⟩ := h.prods
  refine WP.mono (WP.vecKeep scal_carry (carrySP_ok s a0 a1 a2 R0.toNat (R1.toNat / 4)))
    fun s' ⟨⟨hc, k⟩, vx, vy⟩ => ⟨?_, k, vx, vy⟩
  obtain ⟨m, hb⟩ := hc hP
  have hr : R0.toNat + 2 ^ 64 * (4 * (R1.toNat / 4)) = rN R0 R1 := by
    have := hk.r1_mod; simp only [rN]; omega_arith
  refine ⟨by rw [k.gpr' (r := .r8), h.r8], by rw [k.gpr' (r := .r9), h.r9],
    by rw [k.gpr' (r := .r10), h.r10], hb, ?_⟩
  rw [m, hr, ea]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): a chunk

`Stitch.chunk` but for its counter update (`Stitch.next`): the AVX2
kernel's eight blocks (`Avx2.setup_ok`, `Avx2.doubleRound_ok`,
`Avx2.finish_ok`) XORed into the 512 bytes after `rsi`, with the 32 blocks at
`rsi` absorbed, in pieces, between the quarter rounds (`sround4_ok`,
`sround3_ok`).

The kernel's lemmas take the registers they use and the memory they read
from the state they start from, and the pieces of Poly1305 keep both (they
write only Poly1305's registers, `absorbRegs`, and no memory or vector
register), while the quarter rounds and swaps keep every general-purpose
register, on which alone Poly1305's state depends, and write only the
slots, apart from the blocks: so they compose step by step, under an
invariant of both (`SI`).
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds RI M8 Consts Incs stR bufR slotsR dR5 DWin W2 plus hiR
  setup_ok finish_ok W2_frame incs_frame slots_m8 hiR_slots hiR_sub slotsR_sub QSide quarter_step
  swap_step)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval Keeps absorbRegs)
open VG.Spec.ChaCha20 (stateAt serialize innerBlock qround)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- Blocks absorbed after `n` double rounds. -/
theorem firstBlock_succ (pre : Bool) (n : Nat) : firstBlock pre (n + 1) = firstBlock pre n + blocks pre n := by
  unfold firstBlock blocks
  cases pre
  · simp only [Bool.false_eq_true, ite_false]; split <;> split <;> omega_arith
  · simp only [ite_true]
    by_cases h0 : n = 0
    · subst h0; rfl
    · simp only [show n + 1 ≠ 0 by omega_arith, h0, ite_false]; split <;> omega_arith

theorem firstBlock_ten (pre : Bool) : firstBlock pre 10 = total pre := by cases pre <;> rfl

theorem total_le (pre : Bool) : total pre ≤ 32 := by cases pre <;> decide

theorem firstBlock_le (pre : Bool) {n : Nat} (hn : n ≤ 10) : firstBlock pre n ≤ total pre := by
  unfold firstBlock total; cases pre <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> split <;> omega_arith

theorem blocks_cases (pre : Bool) (n : Nat) : blocks pre n = 4 ∨ blocks pre n = 3 ∨ blocks pre n = 0 := by
  unfold blocks; cases pre <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> split <;>
    (try split) <;> simp

/-- The registers of the kernel and the reads of Poly1305 during the rounds,
relative to the state `s₁` after the kernel's setup. -/
structure SR (pre : Bool) (buf q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n : Nat) (s : State) : Prop where
  holds : Holds buf false (fun j => Nat.repeat innerBlock n (V j)) s
  m16 : ∀ l, s.lane .xmm15 l = rot16Mask
  frame : Frame [slotsR buf] s₁.mem s.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * firstBlock pre n))) s

section
variable {buf q : Addr} {R0 R1 : BitVec 64} {X : Nat} {V : Nat → CState} {s₁ : State}

/-- The bytes Poly1305 reads are apart from the slots the rounds write. -/
theorem bytes_frame {m m' : Mem} (hf : Frame [slotsR buf] m m') {B : Nat}
    (hd : (⟨q, B⟩ : Region).Disjoint (slotsR buf)) (hB : B ≤ 512) {j n : Nat} (hjn : j + n ≤ B) :
    bytesAt m' (q + BitVec.ofNat 64 j) n = bytesAt m (q + BitVec.ofNat 64 j) n := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Poly1305.bytesAt_succ, VG.Proof.Poly1305.bytesAt_succ, BitVec.add_assoc,
      show BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) by rw [BitVec.ofNat_add]; rfl, ih (by omega_arith)]
    congr 1
    refine hf _ ?_
    simp only [List.mem_singleton, forall_eq]
    intro hc
    exact hd.symm _ hc (Offset.contains_base q (d := j) (n := 1) (k := B) (by omega_arith) (by lit_omega))

/-- Within a double round: the eight states `vs` in layout `p` and the
kernel's registers as in `SR`, and Poly1305's registers satisfying `Q`. -/
structure SI (buf : Addr) (s₁ : State) (p : Bool) (vs : Nat → CState) (Q : State → Prop)
    (s : State) : Prop where
  holds : Holds buf p vs s
  m16 : ∀ l, s.lane .xmm15 l = rot16Mask
  frame : Frame [slotsR buf] s₁.mem s.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

theorem SI.m8 {p : Bool} {vs : Nat → CState} {Q : State → Prop} {s : State}
    (h : SI buf s₁ p vs Q s) (h8 : M8 s₁.mem buf) : M8 s.mem buf := by
  have e : s.mem.readW (buf + BitVec.ofNat 64 160) 256 = s₁.mem.readW (buf + BitVec.ofNat 64 160) 256 :=
    h.frame.readW (Region.contains_self _ _) (by simpa using slots_m8 buf) (by decide)
  exact ⟨by rw [e]; exact h8.1, by rw [e]; exact h8.2⟩

theorem quarter_si {p : Bool} {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hq : QSide p x y z w = true) {vs : Nat → CState} {Q : State → Prop}
    (hQ : ∀ s s' : State, s'.gpr = s.gpr → Q s → Q s') (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) (h8 : M8 s₁.mem buf) {s : State} (h : SI buf s₁ p vs Q s) :
    WP isa (Impl.ChaCha20.X86_64.Avx2.quarter x y z w) s
      (SI buf s₁ p (fun j => qround (vs j) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) Q) :=
  WP.mono (quarter_step hx hy hz hw hq (s₀ := s) ⟨h.holds, h.m16, Frame.refl _ _, rfl, rfl, rfl⟩
    (by rw [h.gpr _ (by decide), hrcx]) (by rw [h.wr]; exact hb) (h.m8 h8))
    fun s' r => ⟨r.holds, r.m16, h.frame.trans r.frame, fun r' hr' => by rw [r.gpr, h.gpr r' hr'],
      by rw [r.rd, h.rd], by rw [r.wr, h.wr], hQ s s' r.gpr h.poly⟩

theorem swap_si {p : Bool} {vs : Nat → CState} {Q : State → Prop}
    (hQ : ∀ s s' : State, s'.gpr = s.gpr → Q s → Q s') (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) {s : State} (h : SI buf s₁ p vs Q s) :
    WP isa (Impl.ChaCha20.X86_64.Avx2.swap (if p then 10 else 8) (if p then 8 else 10)) s
      (SI buf s₁ (!p) vs Q) :=
  WP.mono (swap_step (s₀ := s) ⟨h.holds, h.m16, Frame.refl _ _, rfl, rfl, rfl⟩
    (by rw [h.gpr _ (by decide), hrcx]) (by rw [h.wr]; exact hb))
    fun s' r => ⟨r.holds, r.m16, h.frame.trans r.frame, fun r' hr' => by rw [r.gpr, h.gpr r' hr'],
      by rw [r.rd, h.rd], by rw [r.wr, h.wr], hQ s s' r.gpr h.poly⟩

/-- A piece of Poly1305 keeps the kernel's state. -/
theorem SI.piece {p : Bool} {vs : Nat → CState} {Q Q' : State → Prop} {s s' : State}
    (h : SI buf s₁ p vs Q s) (hq : Q' s') (k : Keeps absorbRegs s s') (hx : s'.xmm = s.xmm)
    (hy : s'.ymmHi = s.ymmHi) : SI buf s₁ p vs Q' s' := by
  refine ⟨fun k' hk' l q' hl hq' => ?_, fun l => ?_, by rw [k.2.1]; exact h.frame,
    fun r hr => by rw [k.1 r hr, h.gpr r hr], by rw [k.2.2.1, h.rd], by rw [k.2.2.2, h.wr], hq⟩
  · have e := h.holds k' hk' l q' hl hq'
    split
    · rename_i hreg
      simp only [hreg, ite_true] at e
      simpa only [Proof.ChaCha20.X86_64.Avx2.vw, State.lane, hx, hy] using e
    · rename_i hreg
      simp only [hreg] at e
      rw [k.2.1]; exact e
  · simp only [State.lane, hx, hy]; exact h.m16 l

/-- The blocks before `j` absorbed. -/
abbrev AccTo (q : Addr) (R0 R1 : BitVec 64) (X : Nat) (s₁ : State) (j : Nat) : State → Prop :=
  Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j)))

/-- Block `j` halfway. -/
abbrev HalfTo (q : Addr) (R0 R1 : BitVec 64) (X : Nat) (s₁ : State) (j : Nat) : State → Prop :=
  Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1))))

theorem acc_gpr {R0 R1 : BitVec 64} {X : Nat} {j : Nat} :
    ∀ s s' : State, s'.gpr = s.gpr → AccTo q R0 R1 X s₁ j s → AccTo q R0 R1 X s₁ j s' :=
  fun _ _ hg h => h.of_gpr hg

theorem half_gpr {R0 R1 : BitVec 64} {X : Nat} {j : Nat} :
    ∀ s s' : State, s'.gpr = s.gpr → HalfTo q R0 R1 X s₁ j s → HalfTo q R0 R1 X s₁ j s' :=
  fun _ _ hg h => h.of_gpr hg

theorem addProd_si {R0 R1 : BitVec 64} {X : Nat} (hk : Key R0 R1) (hrsi : s₁.gpr .rsi = q)
    {T : Nat} (hd : (⟨q, 16 * T⟩ : Region).Disjoint (slotsR buf))
    (hT : T ≤ 32) (hin : ∀ off n, off + n ≤ 16 * T → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
    {j : Nat} (hj : j < T) {p : Bool} {vs : Nat → CState} {s : State}
    (h : SI buf s₁ p vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (.block (addProd j)) s (SI buf s₁ p vs (HalfTo q R0 R1 X s₁ j)) := by
  refine WP.mono (addProd_ok hk h.poly (p := q) (by rw [h.gpr _ (by decide), hrsi]) (j := j)
    fun e he => by rw [h.rd, h.wr]; exact hin _ _ (by omega_arith)) fun s' ⟨a, k, x, y⟩ => h.piece ?_ k x y
  show Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1)))) s'
  rw [Nat.mul_add, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega_arith),
    ← bytes_frame h.frame hd (by omega_arith) (j := 16 * j) (n := 16) (by omega_arith)]
  exact a

theorem carry_si {R0 R1 : BitVec 64} {X : Nat} (hk : Key R0 R1) {j : Nat} {p : Bool}
    {vs : Nat → CState} {s : State} (h : SI buf s₁ p vs (HalfTo q R0 R1 X s₁ j) s) :
    WP isa (.block Impl.Poly1305.X86_64.carryS) s (SI buf s₁ p vs (AccTo q R0 R1 X s₁ (j + 1))) :=
  WP.mono (carry1_ok hk h.poly) fun _ ⟨a, k, x, y⟩ => h.piece a k x y

section
variable (hk : Key R0 R1) (hrcx : s₁.gpr .rcx = buf)
  (hrsi : s₁.gpr .rsi = q) (hb : bufR buf ∈ s₁.wr) (h8 : M8 s₁.mem buf)
  {T : Nat} (hd : (⟨q, 16 * T⟩ : Region).Disjoint (slotsR buf))
  (hT : T ≤ 32) (hin : ∀ off n, off + n ≤ 16 * T → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
include hk hrcx hrsi hb h8 hd hT hin

theorem sround4_ok {j : Nat} (hj : j + 4 ≤ T) {vs : Nat → CState} {s : State}
    (h : SI buf s₁ false vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (sround4 j) s (SI buf s₁ false (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ (j + 4))) := by
  unfold sround4
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega_arith) h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (swap_si (p := false) acc_gpr hrcx hb h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega_arith) h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega_arith) h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (swap_si (p := true) acc_gpr hrcx hb h₁₃) fun t₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁₄) fun t₁₅ h₁₅ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega_arith) h₁₅) fun t₁₆ h₁₆ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₁₆) fun t₁₇ h₁₇ => ?_)
  exact carry_si hk h₁₇

theorem sround3_ok {j : Nat} (hj : j + 3 ≤ T) {vs : Nat → CState} {s : State}
    (h : SI buf s₁ false vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (sround3 j) s (SI buf s₁ false (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ (j + 3))) := by
  unfold sround3
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega_arith) h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (swap_si (p := false) half_gpr hrcx hb h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega_arith) h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (swap_si (p := true) acc_gpr hrcx hb h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega_arith) h₁₃) fun t₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₁₄) fun t₁₅ h₁₅ => ?_)
  exact carry_si hk h₁₅

omit hk hrsi hd hT hin in
/-- A double round absorbing nothing. -/
theorem sround0_ok {j : Nat} {vs : Nat → CState} {s : State}
    (h : SI buf s₁ false vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa Impl.ChaCha20.X86_64.Avx2.doubleRound s
      (SI buf s₁ false (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ j)) := by
  unfold Impl.ChaCha20.X86_64.Avx2.doubleRound
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (swap_si (p := false) acc_gpr hrcx hb h₂) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₅) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₇) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (swap_si (p := true) acc_gpr hrcx hb h₁₀) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁₂) fun t₁₃ h₁₃ => ?_)
  exact quarter_si (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁₃

theorem srounds_ok (pre : Bool) (htot : total pre ≤ T) : ∀ n, n ≤ 10 → SR pre buf q R0 R1 X V s₁ 0 s₁ →
    WP isa (srounds pre n) s₁ (SR pre buf q R0 R1 X V s₁ n)
  | 0, _, h => WP.block_nil h
  | n + 1, hn, h => by
    refine WP.seq (WP.mono (srounds_ok pre htot n (by omega_arith) h) fun s hs => ?_)
    have hs' : SI buf s₁ false (fun j => Nat.repeat innerBlock n (V j))
        (AccTo q R0 R1 X s₁ (firstBlock pre n)) s :=
      ⟨hs.holds, hs.m16, hs.frame, hs.gpr, hs.rd, hs.wr, hs.acc⟩
    have hb' : firstBlock pre n + blocks pre n ≤ T := by
      rw [← firstBlock_succ]; exact Nat.le_trans (firstBlock_le pre (by omega_arith)) htot
    have fin : ∀ {s'}, SI buf s₁ false (fun j => Nat.repeat innerBlock (n + 1) (V j))
        (AccTo q R0 R1 X s₁ (firstBlock pre n + blocks pre n)) s' → SR pre buf q R0 R1 X V s₁ (n + 1) s' :=
      fun h' => ⟨h'.holds, h'.m16, h'.frame, h'.gpr, h'.rd, h'.wr, by rw [firstBlock_succ]; exact h'.poly⟩
    show WP isa (sround pre n) s _
    unfold sround
    rcases blocks_cases pre n with e | e | e
    · rw [ite_eq_left e]
      rw [e] at hb' fin
      exact WP.mono (sround4_ok hk hrcx hrsi hb h8 hd hT hin hb' hs') fun _ h' => fin h'
    · rw [ite_eq_right (by omega_arith), ite_eq_left e]
      rw [e] at hb' fin
      exact WP.mono (sround3_ok hk hrcx hrsi hb h8 hd hT hin hb' hs') fun _ h' => fin h'
    · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
      rw [e, Nat.add_zero] at fin
      exact WP.mono (sround0_ok hrcx hb h8 hs') fun _ h' => fin h'

end

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): a chunk's rounds with `vprold`

`Stitch.sroundsVL` is `Stitch.srounds` with AVX-512VL's `vprold`, as
`Avx2.roundsVL` is `Avx2.rounds`: words 10 and 11 loaded into `ymm14`,
`ymm15` (`Avx2.loadV_ok`), the double rounds with every word in its register
(`Avx2.HoldsV`) and the pieces of Poly1305 between their quarter rounds, then
the words stored back (`Avx2.storeV_ok`). The quarter rounds keep memory and
every general-purpose register, and the pieces keep memory and the vector
registers, so they compose under an invariant of both (`SIV`), and the
rounds end in `SR`, as `srounds` does (`sroundsVL_ok`, and `sroundsFor_ok`
for either).
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds HoldsV RV M16 bufR slotsR quarterV_ok doubleRoundV_ok
  loadV_ok storeV_ok)
open VG.Proof.ChaCha20 (CState)
open VG.Proof.Poly1305.X86_64 (Keeps absorbRegs)
open VG.Spec.ChaCha20 (innerBlock qround)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- Within a double round with `vprold`: the eight states `vs` in their
registers (`HoldsV`), memory and the kernel's registers as at `s₁`, and
Poly1305's registers satisfying `Q`. -/
structure SIV (s₁ : State) (vs : Nat → CState) (Q : State → Prop) (s : State) : Prop where
  holds : HoldsV vs s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

section
variable {buf q : Addr} {R0 R1 : BitVec 64} {X : Nat} {s₁ : State}

theorem quarterV_siv {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : [x, y, z, w].Nodup) {vs : Nat → CState} {Q : State → Prop}
    (hQ : ∀ s s' : State, s'.gpr = s.gpr → Q s → Q s') {s : State} (h : SIV s₁ vs Q s) :
    WP isa (Impl.ChaCha20.X86_64.Avx2.quarterV x y z w) s
      (SIV s₁ (fun j => qround (vs j) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) Q) :=
  WP.mono (quarterV_ok hx hy hz hw hq h.holds) fun s' ⟨hh, hg, hm, hrd, hwr⟩ =>
    ⟨hh, by rw [hm, h.mem], fun r hr => by rw [hg, h.gpr r hr], by rw [hrd, h.rd],
      by rw [hwr, h.wr], hQ s s' hg h.poly⟩

/-- A piece of Poly1305 keeps the kernel's state. -/
theorem SIV.piece {vs : Nat → CState} {Q Q' : State → Prop} {s s' : State}
    (h : SIV s₁ vs Q s) (hq : Q' s') (k : Keeps absorbRegs s s') (hx : s'.xmm = s.xmm)
    (hy : s'.ymmHi = s.ymmHi) : SIV s₁ vs Q' s' :=
  ⟨fun k' hk' l q' hl hq' => by
      simpa only [Proof.ChaCha20.X86_64.Avx2.vw, State.lane, hx, hy] using h.holds k' hk' l q' hl hq',
    by rw [k.2.1, h.mem], fun r hr => by rw [k.1 r hr, h.gpr r hr], by rw [k.2.2.1, h.rd],
    by rw [k.2.2.2, h.wr], hq⟩

theorem addProdV_si (hk : Key R0 R1) (hrsi : s₁.gpr .rsi = q) {T : Nat}
    (hin : ∀ off n, off + n ≤ 16 * T → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
    {j : Nat} (hj : j < T) {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (.block (addProd j)) s (SIV s₁ vs (HalfTo q R0 R1 X s₁ j)) := by
  refine WP.mono (addProd_ok hk h.poly (p := q) (by rw [h.gpr _ (by decide), hrsi]) (j := j)
    fun e he => by rw [h.rd, h.wr]; exact hin _ _ (by omega_arith)) fun s' ⟨a, k, x, y⟩ => h.piece ?_ k x y
  show Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1)))) s'
  rw [Nat.mul_add, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega_arith)]
  rw [h.mem] at a
  exact a

theorem carryV_si (hk : Key R0 R1) {j : Nat} {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (HalfTo q R0 R1 X s₁ j) s) :
    WP isa (.block Impl.Poly1305.X86_64.carryS) s (SIV s₁ vs (AccTo q R0 R1 X s₁ (j + 1))) :=
  WP.mono (carry1_ok hk h.poly) fun _ ⟨a, k, x, y⟩ => h.piece a k x y

section
variable (hk : Key R0 R1) (hrsi : s₁.gpr .rsi = q) {T : Nat}
  (hin : ∀ off n, off + n ≤ 16 * T → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
include hk hrsi hin

theorem sround4V_ok {j : Nat} (hj : j + 4 ≤ T) {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (sround4V j) s (SIV s₁ (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ (j + 4))) := by
  unfold sround4V
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega_arith) h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₄) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega_arith) h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega_arith) h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₁₃) fun t₁₅ h₁₅ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega_arith) h₁₅) fun t₁₆ h₁₆ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₁₆) fun t₁₇ h₁₇ => ?_)
  exact carryV_si hk h₁₇

theorem sround3V_ok {j : Nat} (hj : j + 3 ≤ T) {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (sround3V j) s (SIV s₁ (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ (j + 3))) := by
  unfold sround3V
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega_arith) h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₃) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega_arith) h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₁₁) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega_arith) h₁₃) fun t₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₁₄) fun t₁₅ h₁₅ => ?_)
  exact carryV_si hk h₁₅

omit hk hrsi hin in
/-- A double round with `vprold` absorbing nothing. -/
theorem sround0V_ok {j : Nat} {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa Impl.ChaCha20.X86_64.Avx2.doubleRoundV s
      (SIV s₁ (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ j)) :=
  WP.mono (doubleRoundV_ok (s₁ := s) ⟨h.holds, rfl, rfl, rfl, rfl⟩) fun s' ⟨hh, hg, hm, hrd, hwr⟩ =>
    ⟨hh, by rw [hm, h.mem], fun r hr => by rw [hg, h.gpr r hr], by rw [hrd, h.rd],
      by rw [hwr, h.wr], acc_gpr s s' hg h.poly⟩

theorem sroundsV_ok (pre : Bool) (htot : total pre ≤ T) {V : Nat → CState} {s : State}
    (h : SIV s₁ V (AccTo q R0 R1 X s₁ (firstBlock pre 0)) s) : ∀ n, n ≤ 10 →
    WP isa (sroundsV pre n) s
      (SIV s₁ (fun j => Nat.repeat innerBlock n (V j)) (AccTo q R0 R1 X s₁ (firstBlock pre n)))
  | 0, _ => WP.block_nil h
  | n + 1, hn => by
    refine WP.seq (WP.mono (sroundsV_ok pre htot h n (by omega_arith)) fun s hs => ?_)
    have hb' : firstBlock pre n + blocks pre n ≤ T := by
      rw [← firstBlock_succ]; exact Nat.le_trans (firstBlock_le pre (by omega_arith)) htot
    show WP isa (sroundV pre n) s _
    rw [firstBlock_succ]
    unfold sroundV
    rcases blocks_cases pre n with e | e | e
    · rw [ite_eq_left e]
      rw [e] at hb' ⊢
      exact sround4V_ok hk hrsi hin hb' hs
    · rw [ite_eq_right (by omega_arith), ite_eq_left e]
      rw [e] at hb' ⊢
      exact sround3V_ok hk hrsi hin hb' hs
    · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), e, Nat.add_zero]
      exact sround0V_ok hs

/-- A chunk's rounds with `vprold` end as `srounds` does. -/
theorem sroundsVL_ok (pre : Bool) (htot : total pre ≤ T) {V : Nat → CState} (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) (h16 : M16 s₁.mem buf) (n : Nat) (hn : n ≤ 10)
    (h : SR pre buf q R0 R1 X V s₁ 0 s₁) :
    WP isa (sroundsVL pre n) s₁ (SR pre buf q R0 R1 X V s₁ n) := by
  unfold sroundsVL
  refine WP.seq (WP.mono (loadV_ok h.holds hrcx hb) fun s₂ ⟨h₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have i₂ : SIV s₁ V (AccTo q R0 R1 X s₁ (firstBlock pre 0)) s₂ :=
    ⟨h₂, m₂, fun r _ => by rw [g₂], rd₂, wr₂, acc_gpr s₁ s₂ g₂ h.acc⟩
  refine WP.seq (WP.mono (sroundsV_ok hk hrsi hin pre htot i₂ n hn) fun s₃ h₃ => ?_)
  have r₃ : s₃.gpr .rcx = buf := by rw [h₃.gpr _ (by decide), hrcx]
  refine WP.mono (storeV_ok (s₀ := s₃) ⟨h₃.holds, rfl, rfl, rfl, rfl⟩ r₃ (by rw [h₃.wr]; exact hb)
    (by rw [h₃.mem]; exact h16)) fun s₄ h₄ => ?_
  exact ⟨h₄.holds, h₄.m16, by rw [← h₃.mem]; exact h₄.frame, fun r hr => by rw [h₄.gpr, h₃.gpr r hr],
    by rw [h₄.rd, h₃.rd], by rw [h₄.wr, h₃.wr], acc_gpr s₃ s₄ h₄.gpr h₃.poly⟩

/-- A chunk's rounds, with `vprold` or without. -/
theorem sroundsFor_ok (vl pre : Bool) (htot : total pre ≤ T) (hT : T ≤ 32) {V : Nat → CState} (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) (h8 : Proof.ChaCha20.X86_64.Avx2.M8 s₁.mem buf) (h16 : M16 s₁.mem buf)
    (hd : (⟨q, 16 * T⟩ : Region).Disjoint (slotsR buf))
    (h : SR pre buf q R0 R1 X V s₁ 0 s₁) :
    WP isa (sroundsFor vl pre) s₁ (SR pre buf q R0 R1 X V s₁ 10) := by
  cases vl
  · exact srounds_ok hk hrcx hrsi hb h8 hd hT hin pre htot 10 (by decide) h
  · exact sroundsVL_ok hk hrsi hin pre htot hrcx hb h16 10 (by decide) h

end

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds RI M8 Consts Incs stR bufR slotsR dR5 DWin W2 plus hiR
  setup_ok doubleRound_ok finish_ok W2_frame incs_frame slots_m8 hiR_slots hiR_sub slotsR_sub)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval Keeps absorbRegs)
open VG.Spec.ChaCha20 (stateAt serialize innerBlock)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

set_option simprocs false in
theorem addRsi_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 512)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 512 ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨?_, fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial⟩
  rfl

/-- The bytes a chunk's rounds absorb, as an address offset. -/
abbrev tot (pre : Bool) : Addr := BitVec.ofNat 64 (16 * total pre)

theorem se_tot (pre : Bool) : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * total pre)) = tot pre := by
  cases pre <;> decide

set_option simprocs false in
theorem addRsiP_ok (pre : Bool) (s : State) :
    WP isa (.block [.alu .add .rsi (.imm (BitVec.ofNat 32 (16 * total pre)))]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + tot pre ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true, se_tot]
  exact ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial⟩

/-- The `16 total` bytes after the `16 total` bytes at `q` (the chunk before,
or with `pre` the 448 bytes before the first chunk) XORed with eight blocks
of keystream from the state at `st`, while those at `q` are absorbed. -/
theorem chunkMain_ok (vl pre : Bool) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hwd : DWin s.wr (q + tot pre))
    (hin : ∀ off n, off + n ≤ 512 → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsd : (stR st).Disjoint (dR5 (q + tot pre))) (dsb : (stR st).Disjoint (bufR buf))
    (dbd : (bufR buf).Disjoint (dR5 (q + tot pre))) (dqs : (dR5 q).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa (chunkMain vl pre) s fun s' =>
        (∀ k < 512, s'.mem (q + tot pre + BitVec.ofNat 64 k) = s.mem (q + tot pre + BitVec.ofNat 64 k) ^^^
          (serialize (plus (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j))
            (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
        Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q (16 * total pre))) s' ∧
        Frame [slotsR buf, dR5 (q + tot pre)] s.mem s'.mem ∧
        (∀ r, r ∉ absorbRegs → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.gpr .rsi = q + tot pre ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ht := total_le pre
  unfold chunkMain
  refine WP.seq (WP.mono (setup_ok hrdi hrcx hst hb hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem buf := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR buf] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  have q₁ : bytesAt s₁.mem q (16 * total pre) = bytesAt s.mem q (16 * total pre) := by
    have := bytes_frame F₁ dqs (by decide) (j := 0) (n := 16 * total pre) (by omega_arith)
    simpa using this
  have h0 : SR pre buf q R0 R1 X (fun j => ctr (stateAt s.mem st) j) s₁ 0 s₁ :=
    ⟨hh, h15, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      rw [show 16 * firstBlock pre 0 = 0 by cases pre <;> rfl, show bytesAt s₁.mem q 0 = [] from rfl,
        VG.Proof.Poly1305.absorbAll_nil]
      exact ⟨by rw [g₁]; exact hacc.r8, by rw [g₁]; exact hacc.r9, by rw [g₁]; exact hacc.r10,
        by rw [g₁]; exact hacc.h2, by simp only [hval, g₁]; exact hacc.val⟩⟩
  refine WP.seq (WP.mono (sroundsFor_ok (T := 32) hk (by rw [g₁, hrsi]) (by rw [rd₁, wr₁]; exact hin) vl pre ht (Nat.le_refl 32)
    (by rw [g₁, hrcx]) (by rw [wr₁]; exact hb) c₁.m8 ⟨c₁.lo16, c₁.hi16⟩ dqs h0) fun s₂ h₂ => ?_)
  refine WP.block_append (WP.mono (addRsiP_ok pre s₂) fun s₃ ⟨rsi₃, g₃, x₃, y₃, m₃, rd₃, wr₃⟩ => ?_)
  have gk : ∀ r, r ∉ absorbRegs → r ≠ .rsi → s₃.gpr r = s.gpr r := fun r hr hs => by
    rw [g₃ r hs, h₂.gpr r hr, g₁]
  have rsi₃' : s₃.gpr .rsi = q + tot pre := by rw [rsi₃, h₂.gpr _ (by decide), g₁, hrsi]
  have F₃ : Frame [slotsR buf] s.mem s₃.mem := by rw [m₃]; exact F₁.trans h₂.frame
  have hh₃ : Holds buf false (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j)) s₃ := by
    intro k hk' l q' hl hq
    have e := h₂.holds k hk' l q' hl hq
    split
    · rename_i hreg
      simp only [hreg, ite_true] at e
      simpa only [Proof.ChaCha20.X86_64.Avx2.vw, State.lane, x₃, y₃] using e
    · rename_i hreg
      simp only [hreg] at e
      rw [m₃]; exact e
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, h₂.wr, wr₁]
  have inc₃ : Incs buf s₃.mem := incs_frame hc.inc F₃ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _)
  refine WP.mono (finish_ok hh₃ (st := st) (by rw [gk _ (by decide) (by decide), hrdi])
    (by rw [gk _ (by decide) (by decide), hrcx]) rsi₃' (by rw [wr₃']; exact hst) (by rw [wr₃']; exact hb)
    (by rw [wr₃']; exact hwd) inc₃ dsd dsb dbd) fun s₄ ⟨d₄, f₄, g₄, rd₄, wr₄⟩ => ?_
  have hS : stateAt s₃.mem st = stateAt s.mem st :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₃ (by simpa using dsb.sub_right (slotsR_sub buf))
  have hq₃ : ∀ k < 512, s₃.mem (q + tot pre + BitVec.ofNat 64 k) = s.mem (q + tot pre + BitVec.ofNat 64 k) := by
    intro k hk'
    refine F₃ _ ?_
    simp only [List.mem_singleton, forall_eq]
    intro hc'
    exact dbd _ ((slotsR_sub buf) _ hc') (Offset.contains_base (q + tot pre) (d := k) (n := 1) (k := 512)
      (by omega_arith) (by lit_omega))
  refine ⟨fun k hk' => by rw [d₄ k hk', hS, hq₃ k hk'], ?_, (F₃.mono (by simp)).trans f₄,
    fun r hr hs => by rw [g₄, gk r hr hs], by rw [g₄, rsi₃'], by rw [rd₄, rd₃, h₂.rd, rd₁],
    by rw [wr₄, wr₃']⟩
  have a₂ := h₂.acc
  rw [firstBlock_ten, q₁] at a₂
  exact ⟨by rw [g₄, g₃ _ (by decide)]; exact a₂.r8, by rw [g₄, g₃ _ (by decide)]; exact a₂.r9,
    by rw [g₄, g₃ _ (by decide)]; exact a₂.r10, by rw [g₄, g₃ _ (by decide)]; exact a₂.h2,
    by simp only [hval, g₄, g₃ _ (show Reg.r11 ≠ .rsi by decide), g₃ _ (show Reg.rbx ≠ .rsi by decide),
      g₃ _ (show Reg.rbp ≠ .rsi by decide)]; exact a₂.val⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): the end of a chunk

`Stitch.next`: the ChaCha20 counter advanced by 8, as the kernel's `next`
does, and the number of bytes left, kept at `buf + lenOff`, decreased by 512.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (stR)
open VG.Spec.ChaCha20 (stateAt)

/-- The slot of the bytes left. -/
abbrev slot (buf : Addr) : Addr := buf + BitVec.ofInt 64 ((lenOff : Nat) : Int)

theorem next_ok {st buf : Addr} {s : State} (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf)
    (hst : stR st ∈ s.wr) (hsl : InRegions s.wr (slot buf) 8)
    (dsl : (stR st).Disjoint ⟨slot buf, 8⟩) {n : Nat} (hn : n < 2 ^ 64) (h512 : 512 ≤ n)
    (hv : s.mem.readW (slot buf) 64 = BitVec.ofNat 64 n) :
    WP isa (.block next) s fun s' =>
      s'.gpr .rdx = BitVec.ofNat 64 (n - 512) ∧ s'.mem.readW (slot buf) 64 = BitVec.ofNat 64 (n - 512) ∧
      stateAt s'.mem st = (stateAt s.mem st).set 12 ((stateAt s.mem st)[12]'(by decide) + 8) (by decide) ∧
      Frame [stR st, ⟨slot buf, 8⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.cf = some (decide (n - 512 < 512)) := by
  have c₁ : (stR st).Contains (Proof.ChaCha20.X86_64.Xor.off st 48) 4 :=
    Proof.ChaCha20.X86_64.contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (Proof.ChaCha20.X86_64.Xor.off st 48) 4 :=
    ⟨stR st, List.mem_append_right _ hst, c₁⟩
  have o₁ : InRegions s.wr (Proof.ChaCha20.X86_64.Xor.off st 48) 4 := ⟨stR st, hst, c₁⟩
  have i₂ : InRegions (s.rd ++ s.wr) (slot buf) 8 :=
    let ⟨r, hr, hc⟩ := hsl; ⟨r, List.mem_append_right _ hr, hc⟩
  have f₁ : Frame [stR st] s.mem (s.mem.writeW (Proof.ChaCha20.X86_64.Xor.off st 48)
      ((stateAt s.mem st)[12]'(by decide) + 8)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have hr : (s.mem.writeW (Proof.ChaCha20.X86_64.Xor.off st 48) ((stateAt s.mem st)[12]'(by decide) + 8)).readW
      (slot buf) 64 = BitVec.ofNat 64 n := by
    rw [← hv]
    exact f₁.readW (Region.contains_self _ _) (by simpa using dsl.symm) (by decide)
  have hfs : Frame [stR st, ⟨slot buf, 8⟩] s.mem ((s.mem.writeW (Proof.ChaCha20.X86_64.Xor.off st 48)
      ((stateAt s.mem st)[12]'(by decide) + 8)).writeW (slot buf) (BitVec.ofNat 64 (n - 512))) :=
    ((f₁.mono (by simp))).writeW (by simp) _ (Region.contains_self _ _)
  have hS : stateAt ((s.mem.writeW (Proof.ChaCha20.X86_64.Xor.off st 48)
      ((stateAt s.mem st)[12]'(by decide) + 8)).writeW (slot buf) (BitVec.ofNat 64 (n - 512))) st =
      (stateAt s.mem st).set 12 ((stateAt s.mem st)[12]'(by decide) + 8) (by decide) := by
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (by simpa using dsl), Proof.ChaCha20.X86_64.Xor.stateAt_writeW_counter]
  have hv' : s.mem.readW (st + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (stateAt s.mem st)[12]'(by decide) := by
    simp [stateAt]
  have e : BitVec.ofNat 64 n - BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 (n - 512) := by
    rw [show BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 by decide,
      Offset.ofNat_sub_ofNat (by omega_arith)]
  simp only [Proof.ChaCha20.X86_64.Xor.off, slot, lenOff] at i₁ o₁ i₂ hsl hfs hv hr hS
  apply WP.of_runBlock
  simp only [next, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.load64, State.store32, State.store64, State.setReg, State.setReg32, State.setFlags,
    lenOff, hrdi, hrcx, i₁, o₁, i₂, hsl, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, reduceCtorEq, Nat.reduceLeDiff]
  rw [hv']
  rw [hr, e]
  refine ⟨rfl, Mem.readW_writeW_self64 _ _ _, hS, hfs, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial,
    trivial, trivial, ?_⟩
  rw [show BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 by decide,
    Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega_arith), Proof.Poly1305.X86_64.toNat_ofNat_lt (by decide)]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

end

end

/-!
# ChaCha20 and Poly1305 together (x86-64): the keystream stored

`Stitch.storeRow kOff` writes a row of the eight blocks out to
`buf + kOff` (`kA buf`) rather than XORing it into the data (`storeRow_out`,
an `OutOk` for `Avx2.finishWith_ok`), so that `finishWith (storeRow kOff)`
leaves the keystream of the eight blocks there (`finishK_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Impl.ChaCha20.X86_64.Avx2 (finishWith)
open VG.Proof.ChaCha20.X86_64.Avx2
open VG.Spec.ChaCha20 (stateAt serialize)
open VG.Proof.ChaCha20

/-- Where `tailK` stores the keystream: `buf + kOff`. -/
abbrev kA (buf : Addr) : Addr := buf + BitVec.ofNat 64 608

/-- The eight blocks' 512 bytes there. -/
abbrev kR (buf : Addr) : Region := ⟨kA buf, 512⟩

/-- The stores of row `row` of blocks `i` and `i + 4`, from the lanes of `x`. -/
def stP (row : Nat) (x : XReg) (i : Nat) : List Instr :=
  [.vmovdquStore .l128 (at_ .rcx (608 + 64 * i + 16 * row)) x, .vop (.vextracti128 .xmm13 x 1),
   .vmovdquStore .l128 (at_ .rcx (608 + 64 * (i + 4) + 16 * row)) .xmm13]

theorem storeRow_eq (row : Nat) (x0 x1 x2 x3 : XReg) : storeRow kOff row [x0, x1, x2, x3] =
    stP row x0 0 ++ (stP row x1 1 ++ (stP row x2 2 ++ stP row x3 3)) := rfl

theorem kR_contains (buf : Addr) {d n : Nat} (h : d + n ≤ 512) : (kR buf).Contains (kA buf + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by lit_omega)

theorem st16_ok (x : XReg) {off : Nat} (ho : off + 16 ≤ 512) {buf : Addr} {s : State}
    (hrcx : s.gpr .rcx = buf) (hk : kR buf ∈ s.wr) :
    WP isa (.block [.vmovdquStore .l128 (at_ .rcx (608 + off)) x]) s fun s' =>
      (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        byte (s.lane x 0) (k - off) else s.mem (kA buf + BitVec.ofNat 64 k)) ∧
      Frame [kR buf] s.mem s'.mem ∧
      (∀ r l, s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : buf + BitVec.ofNat 64 (608 + off) = kA buf + BitVec.ofNat 64 off := by rw [add_ofNat]
  have c := kR_contains buf ho
  have o1 : InRegions s.wr (kA buf + BitVec.ofNat 64 off) 16 := ⟨kR buf, hk, c⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, ea_at, hrcx, e, State.store128_eq, o1,
    ite_true, Option.some.injEq, exists_eq_left', State.setMem_gpr, State.setMem_mem, State.setMem_rd,
    State.setMem_wr, State.xmm_lane]
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c,
    fun r l => by simp only [State.setMem_lane], trivial, trivial, trivial⟩
  rw [byte_write16 _ _ _ ho hk]

theorem stP_ok {row i : Nat} (hrow : row < 4) (hi : i < 4) {x : XReg} (_hx13 : x ≠ .xmm13)
    {buf : Addr} {s : State} (hrcx : s.gpr .rcx = buf) (hk : kR buf ∈ s.wr) :
    WP isa (.block (stP row x i)) s fun s' =>
      (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) =
        if (k / 64 = i ∨ k / 64 = i + 4) ∧ k % 64 / 16 = row then byte (s.lane x (k / 64 / 4)) (k % 16)
        else s.mem (kA buf + BitVec.ofNat 64 k)) ∧
      Frame [kR buf] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [show stP row x i = [.vmovdquStore .l128 (at_ .rcx (608 + (64 * i + 16 * row))) x] ++
      ([.vop (.vextracti128 .xmm13 x 1)] ++
        [.vmovdquStore .l128 (at_ .rcx (608 + (64 * (i + 4) + 16 * row))) .xmm13]) by
    simp only [stP, Nat.add_assoc, List.cons_append, List.nil_append]]
  refine WP.block_append (WP.mono (st16_ok x (off := 64 * i + 16 * row) (by lit_omega) hrcx hk)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, Option.some.injEq, exists_eq_left']
  refine WP.mono (st16_ok .xmm13 (off := 64 * (i + 4) + 16 * row) (buf := buf) (by lit_omega)
    (by rw [VOp.exec_gpr, g₁, hrcx]) (by rw [VOp.exec_wr, w₁]; exact hk))
    fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_
  simp only [VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, lane_vextracti128_1, ite_true,
    l₁ x 1] at m₃ f₃ l₃ g₃ r₃ w₃
  refine ⟨fun k hk => ?_, f₁.trans f₃, fun r l h13 => ?_, g₃.trans g₁, r₃.trans r₁, w₃.trans w₁⟩
  · rw [m₃ k hk, m₁ k hk]
    by_cases h2 : 64 * (i + 4) + 16 * row ≤ k ∧ k < 64 * (i + 4) + 16 * row + 16
    · rw [ite_eq_left h2, ite_eq_left (by omega_using [hrow, h2]), show k / 64 / 4 = 1 by omega_using [hk, h2],
        show k - (64 * (i + 4) + 16 * row) = k % 16 by omega_using [h2]]
    · rw [ite_eq_right h2]
      by_cases h1 : 64 * i + 16 * row ≤ k ∧ k < 64 * i + 16 * row + 16
      · rw [ite_eq_left h1, ite_eq_left (by omega_using [hrow, h1]), show k / 64 / 4 = 0 by omega_using [hrow, hi, h1],
          show k - (64 * i + 16 * row) = k % 16 by omega_using [h1]]
      · rw [ite_eq_right h1, ite_eq_right (by omega_using [h2, h1])]
  · rw [l₃ r l, ite_eq_right h13, l₁ r l]

theorem storeRow_ok {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm13) (h1 : x1 ≠ .xmm13) (h2 : x2 ≠ .xmm13) (h3 : x3 ≠ .xmm13) {buf : Addr} {s : State}
    (hrcx : s.gpr .rcx = buf) (hk : kR buf ∈ s.wr) :
    WP isa (.block (storeRow kOff row [x0, x1, x2, x3])) s fun s' =>
      (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) =
        if k % 64 / 16 = row then byte (s.lane ([x0, x1, x2, x3].getD (k / 64 % 4) .xmm0) (k / 64 / 4)) (k % 16)
        else s.mem (kA buf + BitVec.ofNat 64 k)) ∧
      Frame [kR buf] s.mem s'.mem ∧
      (∀ r l, r ≠ .xmm13 → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [storeRow_eq]
  refine WP.block_append (WP.mono (stP_ok hrow (i := 0) (by decide) h0 hrcx hk)
    fun s₁ ⟨m₁, f₁, l₁, g₁, r₁, w₁⟩ => ?_)
  refine WP.block_append (WP.mono (stP_ok hrow (i := 1) (buf := buf) (by decide) h1 (by rw [g₁, hrcx]) (by rw [w₁]; exact hk))
    fun s₂ ⟨m₂, f₂, l₂, g₂, r₂, w₂⟩ => ?_)
  refine WP.block_append (WP.mono (stP_ok hrow (i := 2) (buf := buf) (by decide) h2 (by rw [g₂, g₁, hrcx])
    (by rw [w₂, w₁]; exact hk)) fun s₃ ⟨m₃, f₃, l₃, g₃, r₃, w₃⟩ => ?_)
  refine WP.mono (stP_ok hrow (i := 3) (buf := buf) (by decide) h3 (by rw [g₃, g₂, g₁, hrcx]) (by rw [w₃, w₂, w₁]; exact hk))
    fun s₄ ⟨m₄, f₄, l₄, g₄, r₄, w₄⟩ => ?_
  have e1 : ∀ l, s₁.lane x1 l = s.lane x1 l := fun l => l₁ _ l h1
  have e2 : ∀ l, s₂.lane x2 l = s.lane x2 l := fun l => (l₂ _ l h2).trans (l₁ _ l h2)
  have e3 : ∀ l, s₃.lane x3 l = s.lane x3 l := fun l => ((l₃ _ l h3).trans (l₂ _ l h3)).trans (l₁ _ l h3)
  refine ⟨fun k hk => ?_, (((f₁.trans f₂).trans f₃).trans f₄), fun r l n13 => ?_,
    by rw [g₄, g₃, g₂, g₁], by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · rw [m₄ k hk, m₃ k hk, m₂ k hk, m₁ k hk, e1, e2, e3]
    rcases (by omega_using [hk] : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3 ∨
      k / 64 = 4 ∨ k / 64 = 5 ∨ k / 64 = 6 ∨ k / 64 = 7) with h | h | h | h | h | h | h | h <;>
      by_cases hr : k % 64 / 16 = row <;>
      simp only [h, hr, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, or_true,
        or_false, and_true, and_false, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
  · rw [l₄ r l n13, l₃ r l n13, l₂ r l n13, l₁ r l n13]

/-- `storeRow`'s effect: row `row` of the blocks `B 0, …, B 7` stored to
`kA buf`. -/
def StoreEff (buf : Addr) (row : Nat) (B : Nat → CState) (m m' : Mem) : Prop :=
  ∀ k < 512, m' (kA buf + BitVec.ofNat 64 k) =
    if k % 64 / 16 = row then (serialize (B (k / 64))).getD (k % 64) 0 else m (kA buf + BitVec.ofNat 64 k)

theorem storeRow_out {buf : Addr} {g : Reg → BitVec 64} {rd w : List Region} (hrcx : g .rcx = buf)
    (hk : kR buf ∈ w) {row : Nat} (hrow : row < 4) {x0 x1 x2 x3 : XReg}
    (h0 : x0 ≠ .xmm12 ∧ x0 ≠ .xmm13 ∧ x0 ≠ .xmm14 ∧ x0 ≠ .xmm15)
    (h1 : x1 ≠ .xmm12 ∧ x1 ≠ .xmm13 ∧ x1 ≠ .xmm14 ∧ x1 ≠ .xmm15)
    (h2 : x2 ≠ .xmm12 ∧ x2 ≠ .xmm13 ∧ x2 ≠ .xmm14 ∧ x2 ≠ .xmm15)
    (h3 : x3 ≠ .xmm12 ∧ x3 ≠ .xmm13 ∧ x3 ≠ .xmm14 ∧ x3 ≠ .xmm15) :
    OutOk (storeRow kOff) (StoreEff buf) [kR buf] g rd w row x0 x1 x2 x3 := by
  intro B s hB hg _ hws
  refine WP.mono (storeRow_ok hrow h0.2.1 h1.2.1 h2.2.1 h3.2.1 (by rw [hg]; exact hrcx) (by rw [hws]; exact hk))
    fun s₂ ⟨d₂, f₂, l₂, g₂, r₂, w₂⟩ => ⟨fun k hk => ?_, f₂, fun r l _ _ _ _ _ n13 _ _ => l₂ r l n13, g₂, r₂, w₂⟩
  rw [d₂ k hk]
  by_cases hr : k % 64 / 16 = row
  · rw [ite_eq_left hr, ite_eq_left hr, serialize_row _ hrow hr]
    obtain ⟨b0, b1, b2, b3⟩ := hB (k / 64 / 4) (by omega_using [hk]) hrow
    have e : 4 * (k / 64 / 4) + k / 64 % 4 = k / 64 := by omega_using []
    rcases (by omega_using [] : k / 64 % 4 = 0 ∨ k / 64 % 4 = 1 ∨ k / 64 % 4 = 2 ∨ k / 64 % 4 = 3) with q | q | q | q <;>
      rw [q] at e ⊢
    · rw [List.getD_cons_zero, b0, e]
    · rw [List.getD_cons_succ, List.getD_cons_zero, b1, e]
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, b2, e]
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, b3, e]
  · rw [ite_eq_right hr, ite_eq_right hr]

/-- The eight blocks' keystream (the rounds' result `vs` plus the input
state) stored to `kA buf`. -/
theorem finishK_ok {st buf : Addr} {vs : Nat → CState} {s : State} (hh : Holds buf false vs s)
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf)
    (hwst : stR st ∈ s.wr) (hwb : bufR buf ∈ s.wr) (hk : kR buf ∈ s.wr) (hinc : Incs buf s.mem)
    (dsb : (stR st).Disjoint (bufR buf)) (dsk : (stR st).Disjoint (kR buf))
    (dbk : (bufR buf).Disjoint (kR buf)) :
    WP isa (.block (finishWith (storeRow kOff))) s fun s' =>
      (∀ k < 512, s'.mem (kA buf + BitVec.ofNat 64 k) =
        (serialize (plus vs (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
      Frame [slotsR buf, kR buf] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hR : ∀ r ∈ [kR buf], (stR st).Disjoint r ∧ (slotsR buf).Disjoint r ∧ (incR buf).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨dsk, dbk.sub_left (slotsR_sub buf), dbk.sub_left (Offset.sub_base buf (by lit_omega))⟩
  refine WP.mono (finishWith_ok (out := storeRow kOff) hh hrdi hrcx hwst hwb hinc dsb hR
    (storeRow_out hrcx hk (by decide) (by decide) (by decide) (by decide) (by decide))
    (storeRow_out hrcx hk (by decide) (by decide) (by decide) (by decide) (by decide))
    (storeRow_out hrcx hk (by decide) (by decide) (by decide) (by decide) (by decide))
    (storeRow_out hrcx hk (by decide) (by decide) (by decide) (by decide) (by decide)))
    fun s' ⟨m₀, m₁, m₂, m₃, _, d₀, d₁, d₃, d₂, F, g, rd, wr⟩ => ⟨fun k hk => ?_, F, g, rd, wr⟩
  rw [d₂ k hk, d₃ k hk, d₁ k hk, d₀ k hk]
  rcases (by omega_using [] : k % 64 / 16 = 0 ∨ k % 64 / 16 = 1 ∨ k % 64 / 16 = 2 ∨ k % 64 / 16 = 3)
    with h | h | h | h <;> simp only [h, Nat.reduceEqDiff, ite_true, ite_false]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

end

end

/-!
# ChaCha20 and Poly1305 together (x86-64): the whole chunks

`Stitch.bulk` proven with the permissions it needs (`bulkWr`): the ChaCha20
state at `c + 64`, the data, `buf` at `c + 128` and the Poly1305 state at
`c + 448`, of a context at `c` (`seal`'s), which `RegionModel.wp_narrow`
moves to `seal`'s permissions.

Before chunk `t` (`LI`), the first `512 t` bytes are encrypted, the counter
is advanced by `8 t`, the first `512 (t - 1)` bytes of ciphertext are
absorbed, and the bytes left are `L - 512 t`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR slotsR dR5 DWin hiR hiR_slots hiR_sub slotsR_sub
  plus_block ks_shift ctr_add)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact hf.bytes hd hn hi

section
variable (c : Addr)
/-- The ChaCha20 state, `buf` and the Poly1305 state, in the context at `c`. -/
abbrev stA : Addr := c + BitVec.ofNat 64 64
abbrev bfA : Addr := c + BitVec.ofNat 64 128
abbrev psA : Addr := c + BitVec.ofNat 64 448
abbrev psR : Region := ⟨psA c, 128⟩
end

/-- The permissions of the whole chunks: with `seal`'s `tailK`'s keystream
(`kR`) too. -/
abbrev bulkWr (c dp : Addr) (L : Nat) : List Region :=
  [stR (stA c), ⟨dp, L⟩, bufR (bfA c), psR c, kR (bfA c)]

/-- The context and the data: apart, and neither wrapping around. -/
structure Lay (c dp : Addr) (L : Nat) : Prop where
  L_lt : L < 2 ^ 64
  nowrap : dp.toNat + L ≤ 2 ^ 64
  dc : (⟨c, 1248⟩ : Region).Disjoint ⟨dp, L⟩

section
variable {c dp : Addr} {L : Nat}

theorem sub_c {d n : Nat} (h : d + n ≤ 1248) : Region.Sub ⟨c + BitVec.ofNat 64 d, n⟩ ⟨c, 1248⟩ :=
  Offset.sub_base c h

theorem st_bf : (stR (stA c)).Disjoint (bufR (bfA c)) := Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)

theorem slot_eq : slot (bfA c) = c + BitVec.ofNat 64 544 := by
  rw [slot, Proof.Poly1305.X86_64.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]; rfl

theorem st_slot : (stR (stA c)).Disjoint ⟨slot (bfA c), 8⟩ := by
  rw [slot_eq]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)

theorem slot_ps : Region.Sub ⟨slot (bfA c), 8⟩ (psR c) := by
  rw [slot_eq]; exact Offset.sub c (by decide) (by decide)

theorem slot_in : (psR c).Contains (slot (bfA c)) 8 := by
  rw [slot_eq]; exact Offset.contains c (by decide) (by decide) (by decide)

/-- The window of chunk `t` is in the data. -/
theorem win {t : Nat} (h : 512 * t + 512 ≤ L) :
    Region.Sub (dR5 (dp + BitVec.ofNat 64 (512 * t))) ⟨dp, L⟩ := Offset.sub_base dp h

variable (hl : Lay c dp L)
include hl

theorem Lay.cd {d n : Nat} (h : d + n ≤ 1248) : (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨dp, L⟩ :=
  hl.dc.sub_left (sub_c h)

theorem Lay.st_d : (stR (stA c)).Disjoint ⟨dp, L⟩ := hl.cd (by decide)
theorem Lay.bf_d : (bufR (bfA c)).Disjoint ⟨dp, L⟩ := hl.cd (by decide)
theorem Lay.ps_d : (psR c).Disjoint ⟨dp, L⟩ := hl.cd (by decide)

theorem Lay.win_cd {t : Nat} (h : 512 * t + 512 ≤ L) {d n : Nat} (hd : d + n ≤ 1248) :
    (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * t))) :=
  (hl.cd hd).sub_right (win h)

end

/-- Before chunk `t` (`t ≥ 1`) of the whole chunks, from the memory `m₀`
on entry, with the key `R0, R1` and the accumulator `A` on entry, and the
values `v₁₂`, `v₁₃`, `v₁₄` stashed. -/
structure LI (c dp : Addr) (L : Nat) (R0 R1 : BitVec 64) (A : Nat) (m₀ : Mem) (sp : Addr)
    (t : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = bulkWr c dp L
  rdi : s.gpr .rdi = stA c
  rcx : s.gpr .rcx = bfA c
  rsi : s.gpr .rsi = dp + BitVec.ofNat 64 (512 * (t - 1))
  rsp : s.gpr .rsp = sp
  t1 : 1 ≤ t
  le : 512 * t ≤ L
  left : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 512 * t)
  cnt : stateAt s.mem (stA c) = ctr (stateAt m₀ (stA c)) (8 * t)
  data : ∀ k < L, s.mem (dp + BitVec.ofNat 64 k) =
    if k < 512 * t then m₀ (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt m₀ (stA c)) L).getD k 0
    else m₀ (dp + BitVec.ofNat 64 k)
  consts : Consts s.mem (bfA c)
  acc : Acc R0 R1 (absorbAll (rN R0 R1) A (bytesAt s.mem dp (512 * (t - 1)))) s
  fr : Frame [stR (stA c), ⟨dp, L⟩, bufR (bfA c), ⟨slot (bfA c), 8⟩] m₀ s.mem

theorem window_eq (dp : Addr) {t : Nat} (ht : 1 ≤ t) :
    dp + BitVec.ofNat 64 (512 * (t - 1)) + 512 = dp + BitVec.ofNat 64 (512 * t) := by
  rw [show (512 : Addr) = BitVec.ofNat 64 512 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 512 * (t - 1) + 512 = 512 * t by omega_arith]

theorem tot_false : tot false = 512 := rfl
theorem total_false : 16 * total false = 512 := rfl

/-- A chunk: the loop invariant from `t` to `t + 1`. -/
theorem chunk_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {t : Nat} (hge : 512 ≤ L - 512 * t) {s : State}
    (h : LI c dp L R0 R1 A m₀ sp t s) :
    WP isa (chunk vl false) s fun s' => LI c dp L R0 R1 A m₀ sp (t + 1) s' ∧
      s'.cf = some (decide (L - 512 * (t + 1) < 512)) := by
  have hLe := hl.L_lt
  have ht := h.t1
  obtain hw : 512 * t + 512 ≤ L := by omega_arith
  obtain hq : dp + BitVec.ofNat 64 (512 * (t - 1)) + 512 = dp + BitVec.ofNat 64 (512 * t) := window_eq dp ht
  obtain wsub : Region.Sub (dR5 (dp + BitVec.ofNat 64 (512 * (t - 1)))) ⟨dp, L⟩ := win (t := t - 1) (by omega_arith)
  obtain mst : stR (stA c) ∈ s.wr := by rw [h.wr]; simp
  obtain mbf : bufR (bfA c) ∈ s.wr := by rw [h.wr]; simp
  obtain md : (⟨dp, L⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  obtain hwd : DWin s.wr (dp + BitVec.ofNat 64 (512 * (t - 1)) + 512) := by
    rw [hq]; intro off n hn
    exact ⟨_, md, by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hin : ∀ off n, off + n ≤ 512 →
      InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 (512 * (t - 1)) + BitVec.ofNat 64 off) n := by
    intro off n hn
    exact ⟨_, List.mem_append_right _ md, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain dsd : (stR (stA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * (t - 1)) + 512)) := by
    rw [hq]; exact hl.win_cd hw (by decide)
  obtain dbd : (bufR (bfA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * (t - 1)) + 512)) := by
    rw [hq]; exact hl.win_cd hw (by decide)
  obtain dqs : (dR5 (dp + BitVec.ofNat 64 (512 * (t - 1)))).Disjoint (slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right wsub).symm
  refine WP.seq (WP.mono (chunkMain_ok vl false hk h.rdi h.rcx h.rsi mst mbf (by rw [tot_false]; exact hwd) hin
    h.consts (by rw [tot_false]; exact dsd) st_bf (by rw [tot_false]; exact dbd) dqs h.acc)
    fun s₁ ⟨d₁, a₁, f₁, g₁, rsi₁, rd₁, wr₁⟩ => ?_)
  rw [tot_false, hq] at d₁ f₁ rsi₁
  rw [total_false] at a₁
  obtain dslot : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t))],
      (⟨slot (bfA c), 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_eq]
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · exact hl.win_cd hw (by decide)
  obtain sl₁ : s₁.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 512 * t) := by
    rw [f₁.readW (Region.contains_self _ _) dslot (by decide), h.left]
  refine WP.mono (next_ok (st := stA c) (buf := bfA c) (s := s₁) (by rw [g₁ _ (by decide) (by decide), h.rdi])
    (by rw [g₁ _ (by decide) (by decide), h.rcx]) (by rw [wr₁]; exact mst)
    ⟨psR c, by rw [wr₁, h.wr]; simp, slot_in⟩ st_slot
    (n := L - 512 * t) (by omega_arith) hge sl₁)
    fun s₂ ⟨_, sl₂, cnt₂, f₂, g₂, rd₂, wr₂, _, _, cf₂⟩ => ?_
  obtain dst : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t))], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf.sub_right (slotsR_sub _)
    · exact hl.win_cd hw (by decide)
  obtain S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame f₁ dst
  obtain FA : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
      s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
  refine ⟨⟨by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr], by rw [g₂ _ (by decide) (by decide),
    g₁ _ (by decide) (by decide), h.rdi], by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rcx],
    by rw [g₂ _ (by decide) (by decide), rsi₁, Nat.add_sub_cancel],
    by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rsp], by omega_arith, hw,
    by rw [sl₂, show L - 512 * t - 512 = L - 512 * (t + 1) by omega_arith], ?_, ?_, ?_, ?_, ?_⟩,
    by rw [cf₂, show L - 512 * t - 512 = L - 512 * (t + 1) by omega_arith]⟩
  · rw [cnt₂, S₁, h.cnt, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ctr_add,
      show 8 * t + 8 = 8 * (t + 1) by omega_arith]
  · intro k hk'
    obtain n_st : ¬ (stR (stA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.st_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    obtain n_sl : ¬ (⟨slot (bfA c), 8⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.ps_d _ (slot_ps _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    obtain n_sls : ¬ (slotsR (bfA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.bf_d _ (slotsR_sub _ _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    rw [f₂ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact n_st
      · exact n_sl)]
    by_cases hin' : 512 * t ≤ k ∧ k < 512 * t + 512
    · have ea : dp + BitVec.ofNat 64 k =
          dp + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) := by
        rw [Offset.add_add, Nat.add_sub_cancel' hin'.1]
      obtain x₁ := d₁ (k - 512 * t) (by omega_arith)
      rw [← ea] at x₁
      rw [x₁, h.data k hk', ite_eq_right (by omega_arith : ¬ k < 512 * t), ite_eq_left (by omega_arith : k < 512 * (t + 1)),
        plus_block, h.cnt, ks_shift _ hk' hin'.1]
    · have n_w : ¬ (dR5 (dp + BitVec.ofNat 64 (512 * t))).Contains (dp + BitVec.ofNat 64 k) 1 := by
        simp only [Region.Contains]
        rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)]
        split <;> omega_arith
      rw [f₁ _ (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact n_sls
          · exact n_w), h.data k hk']
      by_cases hlt : k < 512 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega_arith : k < 512 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_arith : ¬ k < 512 * (t + 1))]
  · have F : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
        s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
    refine h.consts.frame F ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hiR_slots _
    · exact (hl.bf_d.sub_left (hiR_sub _)).sub_right (win hw)
    · exact (st_bf.symm.sub_left (hiR_sub _))
    · exact ((Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide) :
        (bufR (bfA c)).Disjoint (psR c)).sub_left (hiR_sub _)).sub_right slot_ps
  · have F : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
        s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
    obtain hb : bytesAt s₂.mem dp (512 * t) = bytesAt s.mem dp (512 * t) := by
      refine bytesAt_frame F ?_ (by omega_arith)
      obtain dsub : Region.Sub ⟨dp, 512 * t⟩ ⟨dp, L⟩ := Region.sub_prefix (by omega_arith)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hl.bf_d.sub_left (slotsR_sub _)).symm.sub_left dsub
      · exact Offset.base_disjoint dp (Nat.le_refl _) (by omega_arith)
      · exact hl.st_d.symm.sub_left dsub
      · exact (hl.ps_d.sub_left slot_ps).symm.sub_left dsub
    rw [Nat.add_sub_cancel, hb, show 512 * t = 512 * (t - 1) + 512 by omega_arith, VG.Proof.Poly1305.bytesAt_add,
      VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega_arith)]
    exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact a₁.r8, by rw [g₂ _ (by decide) (by decide)]; exact a₁.r9,
      by rw [g₂ _ (by decide) (by decide)]; exact a₁.r10, by rw [g₂ _ (by decide) (by decide)]; exact a₁.h2,
      by simp only [hval, g₂ _ (show Reg.r11 ≠ .rax by decide) (by decide),
        g₂ _ (show Reg.rbx ≠ .rax by decide) (by decide), g₂ _ (show Reg.rbp ≠ .rax by decide) (by decide)]
         exact a₁.val⟩
  · refine h.fr.trans (FA.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨bufR (bfA c), by simp, slotsR_sub _⟩
    · exact ⟨⟨dp, L⟩, by simp, win hw⟩
    · exact ⟨stR (stA c), by simp, fun _ h => h⟩
    · exact ⟨⟨slot (bfA c), 8⟩, by simp, fun _ h => h⟩

/-- The first chunk, the kernel's: the loop invariant at 1. -/
theorem firstChunk_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} {A : Nat}
    {m₀ : Mem} {sp : Addr} (hge : 512 ≤ L) {s : State} (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L)
    (hrdi : s.gpr .rdi = stA c) (hrcx : s.gpr .rcx = bfA c) (hrsi : s.gpr .rsi = dp) (hrsp : s.gpr .rsp = sp)
    (hslot : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 L)
    (hm : s.mem = m₀)
    (hc : Consts s.mem (bfA c)) (hacc : Acc R0 R1 A s) :
    WP isa (firstChunk vl) s fun s' => LI c dp L R0 R1 A m₀ sp 1 s' ∧
      s'.cf = some (decide (L - 512 * 1 < 512)) := by
  have hLe := hl.L_lt
  obtain hcnt : stateAt s.mem (stA c) = stateAt m₀ (stA c) := by rw [hm]
  obtain hdata : ∀ k < L, s.mem (dp + BitVec.ofNat 64 k) = m₀ (dp + BitVec.ofNat 64 k) := fun _ _ => by rw [hm]
  obtain hw : 512 * 0 + 512 ≤ L := by omega_arith
  obtain mst : stR (stA c) ∈ s.wr := by rw [hwr]; simp
  obtain mbf : bufR (bfA c) ∈ s.wr := by rw [hwr]; simp
  obtain md : (⟨dp, L⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  obtain w0 : dp + BitVec.ofNat 64 (512 * 0) = dp := by simp
  unfold firstChunk firstMain
  refine WP.seq (WP.seq (WP.mono (Proof.ChaCha20.X86_64.Avx2.setup_ok hrdi hrcx mst mbf hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_))
  obtain c₁ : Consts s₁.mem (bfA c) := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  obtain F₁ : Frame [slotsR (bfA c)] s.mem s₁.mem := by
    rw [m₁]; exact Proof.ChaCha20.X86_64.Avx2.W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  refine WP.seq (WP.mono (Proof.ChaCha20.X86_64.Avx2.roundsFor_ok vl hh h15 (by rw [g₁, hrcx])
    (by rw [wr₁]; exact mbf) c₁.m8 ⟨c₁.lo16, c₁.hi16⟩) fun s₂ hr => ?_)
  obtain F₂ := F₁.trans hr.frame
  obtain g₂ : s₂.gpr = s.gpr := hr.gpr.trans g₁
  obtain wr₂ : s₂.wr = s.wr := hr.wr.trans wr₁
  obtain dsd : (stR (stA c)).Disjoint (dR5 dp) := by
    have := hl.win_cd (t := 0) hw (d := 64) (n := 64) (by decide); rwa [w0] at this
  obtain dbd : (bufR (bfA c)).Disjoint (dR5 dp) := by
    have := hl.win_cd (t := 0) hw (d := 128) (n := 320) (by decide); rwa [w0] at this
  refine WP.mono (Proof.ChaCha20.X86_64.Avx2.finish_ok hr.holds (st := stA c) (by rw [g₂, hrdi])
    (by rw [g₂, hrcx]) (by rw [g₂, hrsi]) (by rw [wr₂]; exact mst) (by rw [wr₂]; exact mbf)
    (by rw [wr₂]; intro off n hn; exact ⟨_, md, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (Proof.ChaCha20.X86_64.Avx2.incs_frame c₁.inc hr.frame (by
      intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hiR_slots _))
    dsd st_bf dbd) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  obtain F₃ : Frame [slotsR (bfA c), dR5 dp] s.mem s₃.mem := (F₂.mono (by simp)).trans f₃
  obtain dslot : ∀ r ∈ [slotsR (bfA c), dR5 dp], (⟨slot (bfA c), 8⟩ : Region).Disjoint r := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl <;> rw [slot_eq]
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · have := hl.win_cd (t := 0) hw (d := 544) (n := 8) (by decide); rwa [w0] at this
  obtain sl₃ : s₃.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 L := by
    rw [F₃.readW (Region.contains_self _ _) dslot (by decide), hslot]
  refine WP.mono (next_ok (st := stA c) (buf := bfA c) (s := s₃) (by rw [g₃', hrdi]) (by rw [g₃', hrcx])
    (by rw [wr₃, wr₂]; exact mst) ⟨psR c, by rw [wr₃, wr₂, hwr]; simp, slot_in⟩ st_slot (n := L) hLe hge sl₃)
    fun s₄ ⟨_, sl₄, cnt₄, f₄, g₄, rd₄, wr₄, _, _, cf₄⟩ => ?_
  obtain dst : ∀ r ∈ [slotsR (bfA c), dR5 dp], (stR (stA c)).Disjoint r := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact st_bf.sub_right (slotsR_sub _)
    · exact dsd
  obtain S₃ : stateAt s₃.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame F₃ dst
  obtain gk : ∀ r, r ≠ .rax → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b => by rw [g₄ r a b, g₃']
  refine ⟨⟨by rw [rd₄, rd₃, hr.rd, rd₁, hrd], by rw [wr₄, wr₃, wr₂, hwr], by rw [gk _ (by decide) (by decide), hrdi],
    by rw [gk _ (by decide) (by decide), hrcx], by rw [gk _ (by decide) (by decide), hrsi]; simp,
    by rw [gk _ (by decide) (by decide), hrsp], Nat.le_refl 1, by omega_arith, by rw [sl₄], ?_, ?_, ?_, ?_, ?_⟩, by rw [cf₄]⟩
  · rw [cnt₄, S₃, hcnt, ← VG.Proof.ChaCha20.ctr_zero (stateAt m₀ (stA c)),
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ctr_add]
    simp only [VG.Proof.ChaCha20.ctr_zero, Nat.zero_add, Nat.mul_one]
  · intro k hk'
    obtain n_st : ¬ (stR (stA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.st_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    obtain n_sl : ¬ (⟨slot (bfA c), 8⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.ps_d _ (slot_ps _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    obtain n_sls : ¬ (slotsR (bfA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.bf_d _ (slotsR_sub _ _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    rw [f₄ _ (by
      intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact n_st
      · exact n_sl)]
    obtain S₂ : stateAt s₂.mem (stA c) = stateAt s.mem (stA c) :=
      Proof.ChaCha20.X86_64.Xor.stateAt_frame F₂ (by simpa using st_bf.sub_right (slotsR_sub (bfA c)))
    by_cases hin' : k < 512
    · have x₃ := d₃ k hin'
      rw [x₃, S₂, F₂ _ (by simpa using n_sls), hdata k hk', ite_eq_left (by omega_arith : k < 512 * 1), plus_block,
        hcnt, VG.Proof.ChaCha20.keystream_getD _ hk']
    · have n_w : ¬ (dR5 dp).Contains (dp + BitVec.ofNat 64 k) 1 := by
        simp only [Region.Contains]
        rw [Mem.sub_ofNat_toNat dp (by omega_arith)]
        omega_arith
      rw [F₃ _ (by
          intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl
          · exact n_sls
          · exact n_w), hdata k hk', ite_eq_right (by omega_arith : ¬ k < 512 * 1)]
  · have F : Frame [slotsR (bfA c), dR5 dp, stR (stA c), ⟨slot (bfA c), 8⟩] s.mem s₄.mem :=
      (F₃.mono (by simp)).trans (f₄.mono (by simp))
    refine hc.frame F ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact hiR_slots _
    · exact dbd.sub_left (hiR_sub _)
    · exact (st_bf.symm.sub_left (hiR_sub _))
    · exact ((Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide) :
        (bufR (bfA c)).Disjoint (psR c)).sub_left (hiR_sub _)).sub_right slot_ps
  · rw [show 512 * (1 - 1) = 0 from rfl, show bytesAt s₄.mem dp 0 = [] from rfl,
      VG.Proof.Poly1305.absorbAll_nil]
    exact ⟨by rw [gk _ (by decide) (by decide)]; exact hacc.r8, by rw [gk _ (by decide) (by decide)]; exact hacc.r9,
      by rw [gk _ (by decide) (by decide)]; exact hacc.r10, by rw [gk _ (by decide) (by decide)]; exact hacc.h2,
      by simp only [hval, gk _ (show Reg.r11 ≠ .rax by decide) (by decide),
        gk _ (show Reg.rbx ≠ .rax by decide) (by decide), gk _ (show Reg.rbp ≠ .rax by decide) (by decide)]
         exact hacc.val⟩
  · rw [← hm]
    obtain FA : Frame [slotsR (bfA c), dR5 dp, stR (stA c), ⟨slot (bfA c), 8⟩] s.mem s₄.mem :=
      (F₃.mono (by simp)).trans (f₄.mono (by simp))
    refine FA.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨bufR (bfA c), by simp, slotsR_sub _⟩
    · exact ⟨⟨dp, L⟩, by simp, by have := win (dp := dp) (t := 0) hw; rwa [w0] at this⟩
    · exact ⟨stR (stA c), by simp, fun _ h => h⟩
    · exact ⟨⟨slot (bfA c), 8⟩, by simp, fun _ h => h⟩

/-- The later chunks, while at least 512 bytes remain. -/
theorem chunks_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {t : Nat} {s : State} (h : LI c dp L R0 R1 A m₀ sp t s)
    (hcf : s.cf = some (decide (L - 512 * t < 512))) :
    WP isa (.ite .b (.block []) (.loop (chunk vl false) .ae)) s fun s' =>
      ∃ T, LI c dp L R0 R1 A m₀ sp T s' ∧ L - 512 * T < 512 := by
  refine WP.ite (decide (L - 512 * t < 512)) (by simp only [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨t, h, by simpa using hb⟩
  · have hge : 512 ≤ L - 512 * t := by simp at hb; omega_arith
    let Inv : Nat → State → Prop := fun n s => ∃ u, n = L - 512 * u ∧ 512 ≤ L - 512 * u ∧
      LI c dp L R0 R1 A m₀ sp u s
    refine WP.loop (M := isa) Inv (fun n s ⟨u, hn, hu, hL⟩ => ?_) _ s ⟨t, rfl, hge, h⟩
    refine WP.mono (chunk_ok vl hl hk hu hL) fun s' ⟨hL', cf'⟩ => ?_
    by_cases hlt : L - 512 * (u + 1) < 512
    · exact .inl ⟨by simp [eval, cf', hlt], u + 1, hL', hlt⟩
    · exact .inr ⟨by simp [eval, cf', hlt], L - 512 * (u + 1), by omega_arith, u + 1, rfl, by omega_arith, hL'⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): entering and leaving the chunks

`Stitch.enter` stashes `r12`–`r14` and the length, stores the kernel's
constants (`Avx2.pairs_ok`) and loads the key and the accumulator from the
Poly1305 state (`Poly1305.X86_64.setup_ok`); `Stitch.leave` reduces the
accumulator (`reduce_ok`), stores it, and restores the stashed registers.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR)
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (hval Keeps)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (P bytesAt)

/-- The stash, in the Poly1305 state's working space. -/
abbrev stashR (c : Addr) : Region := ⟨c + BitVec.ofNat 64 520, 32⟩

theorem ofInt_bf (c : Addr) (d : Nat) :
    bfA c + BitVec.ofInt 64 ((d : Nat) : Int) = c + BitVec.ofNat 64 (128 + d) := by
  rw [Proof.Poly1305.X86_64.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem readW_writeW_ofNat (m : Mem) (c : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    (m.writeW (c + BitVec.ofNat 64 e) v).readW (c + BitVec.ofNat 64 d) 64 = m.readW (c + BitVec.ofNat 64 d) 64 := by
  have := Proof.Poly1305.X86_64.readW_writeW_off m c v hd he h
  simpa only [Proof.Poly1305.X86_64.off, Proof.Poly1305.X86_64.ofInt_natCast] using this

set_option simprocs false in
theorem stash_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) (hw : psR c ∈ s.wr) :
    WP isa (.block [.store (at_ .rcx r12Off) .r12, .store (at_ .rcx r13Off) .r13,
      .store (at_ .rcx r14Off) .r14, .store (at_ .rcx lenOff) .rdx]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [stashR c] s.mem s'.mem ∧
      s'.mem.readW (c + BitVec.ofNat 64 520) 64 = s.gpr .r12 ∧
      s'.mem.readW (c + BitVec.ofNat 64 528) 64 = s.gpr .r13 ∧
      s'.mem.readW (c + BitVec.ofNat 64 536) 64 = s.gpr .r14 ∧
      s'.mem.readW (c + BitVec.ofNat 64 544) 64 = s.gpr .rdx := by
  obtain o : ∀ d, 520 ≤ d → d + 8 ≤ 552 → InRegions s.wr (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
  obtain cs : ∀ d, 520 ≤ d → d + 8 ≤ 552 → (stashR c).Contains (c + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains c (by omega_arith) (by omega_arith) (by decide)
  obtain o0 := o 520 (by decide) (by decide); have o1 := o 528 (by decide) (by decide)
  obtain o2 := o 536 (by decide) (by decide); have o3 := o 544 (by decide) (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, State.store64,
    hrcx, r12Off, r13Off, r14Off, lenOff, ofInt_bf, o0, o1, o2, o3, ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 520 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 528 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cs 536 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (cs 544 (by decide) (by decide))
  all_goals simp (disch := decide) only [readW_writeW_ofNat, Mem.readW_writeW_self64]

set_option simprocs false in
/-- `rdi = rcx + d` (`d` 320) or `rcx - d` (`d` 64). -/
theorem rdiAdd_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) :
    WP isa (.block [.mov .rdi (.reg .rcx), .alu .add .rdi (.imm 320)]) s fun s' =>
      s'.gpr .rdi = psA c ∧ (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨?_, fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial⟩
  rw [hrcx, show BitVec.signExtend 64 (320 : BitVec 32) = BitVec.ofNat 64 320 by decide, BitVec.add_assoc,
    ← BitVec.ofNat_add]

set_option simprocs false in
theorem rdiSub_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) :
    WP isa (.block [.mov .rdi (.reg .rcx), .alu .sub .rdi (.imm 64)]) s fun s' =>
      s'.gpr .rdi = stA c ∧ (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨?_, fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial⟩
  rw [hrcx, show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide,
    BitVec.sub_eq_iff_eq_add, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A word of the Poly1305 state (`[0, 40)`: the accumulator and `r`) is
apart from the stash and `buf`. -/
theorem ps_word {c : Addr} {m m' : Mem} (hf : Frame [bufR (bfA c), stashR c] m m') {d : Nat} (hd : d + 8 ≤ 40) :
    m'.readW (Proof.Poly1305.X86_64.off (psA c) d) 64 = m.readW (Proof.Poly1305.X86_64.off (psA c) d) 64 := by
  obtain e : Proof.Poly1305.X86_64.off (psA c) d = c + BitVec.ofNat 64 (448 + d) := by
    rw [Proof.Poly1305.X86_64.off, Proof.Poly1305.X86_64.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  refine hf.readW (r := ⟨c + BitVec.ofNat 64 (448 + d), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact Offset.disjoint c (Or.inl (by omega_arith)) (by omega_arith) (by decide)

theorem enter_eq : enter = ([.store (at_ .rcx r12Off) .r12, .store (at_ .rcx r13Off) .r13,
    .store (at_ .rcx r14Off) .r14, .store (at_ .rcx lenOff) .rdx] : List Instr) ++
    (Impl.ChaCha20.X86_64.Avx2.consts ++ (([.mov .rdi (.reg .rcx), .alu .add .rdi (.imm 320)] : List Instr) ++
    (Impl.Poly1305.X86_64.setup ++ ([.mov .rdi (.reg .rcx), .alu .sub .rdi (.imm 64)] : List Instr)))) := by
  simp only [enter, List.append_assoc, List.cons_append, List.nil_append]

theorem enter_ok {c dp : Addr} {L : Nat} {s : State} (hwr : s.wr = bulkWr c dp L)
    (hrcx : s.gpr .rcx = bfA c) :
    WP isa (.block enter) s fun s' =>
      s'.gpr .rdi = stA c ∧ (∀ r, r ≠ .rdi → r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .rbx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [bufR (bfA c), stashR c] s.mem s'.mem ∧ Consts s'.mem (bfA c) ∧
      s'.mem.readW (slot (bfA c)) 64 = s.gpr .rdx ∧
      s'.mem.readW (c + BitVec.ofNat 64 520) 64 = s.gpr .r12 ∧
      s'.mem.readW (c + BitVec.ofNat 64 528) 64 = s.gpr .r13 ∧
      s'.mem.readW (c + BitVec.ofNat 64 536) 64 = s.gpr .r14 ∧
      s'.gpr .r8 = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 24) 64 &&& Proof.Poly1305.X86_64.M0 ∧
      s'.gpr .r9 = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 32) 64 &&& Proof.Poly1305.X86_64.M1 ∧
      (s'.gpr .r10).toNat = 5 * ((s'.gpr .r9).toNat / 4) ∧
      s'.gpr .r11 = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 0) 64 ∧
      s'.gpr .rbx = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 8) 64 ∧
      s'.gpr .rbp = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 16) 64 := by
  rw [enter_eq]
  refine WP.block_append (WP.mono (stash_ok hrcx (by rw [hwr]; simp))
    fun s₁ ⟨g₁, rd₁, wr₁, f₁, v12, v13, v14, vl⟩ => ?_)
  rw [Proof.ChaCha20.X86_64.Avx2.consts_eq]
  refine WP.block_append (WP.mono (Proof.ChaCha20.X86_64.Avx2.pairs_ok (buf := bfA c)
    Proof.ChaCha20.X86_64.Avx2.constPairs Proof.ChaCha20.X86_64.Avx2.constPairs_le (s := s₁)
    (by rw [g₁, hrcx]) (by rw [wr₁, hwr]; simp)) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (rdiAdd_ok (c := c) (by rw [g₂ _ (by decide), g₁, hrcx]))
    fun s₃ ⟨rdi₃, g₃, m₃, rd₃, wr₃, _, _⟩ => ?_)
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.setup_ok s₃ (by rw [rdi₃, wr₃, wr₂, wr₁, hwr, rd₃, rd₂, rd₁]; simp))
    fun s₄ ⟨r8, r9, r10, r11, rbx, rbp, k₄⟩ => ?_)
  refine WP.mono (rdiSub_ok (c := c) (by rw [k₄.gpr' (r := .rcx), g₃ _ (by decide), g₂ _ (by decide), g₁, hrcx]))
    fun s₅ ⟨rdi₅, g₅, m₅, rd₅, wr₅, _, _⟩ => ?_
  obtain F₂ : Frame [bufR (bfA c), stashR c] s.mem s₂.mem := by
    rw [m₂]
    exact (f₁.mono (by simp)).trans
      (Proof.ChaCha20.X86_64.Avx2.storeAll_frame (by simp) _ Proof.ChaCha20.X86_64.Avx2.constPairs_le _)
  obtain mm : s₅.mem = s₂.mem := by rw [m₅, k₄.2.1, m₃]
  obtain dsl : ∀ d, 520 ≤ d → d + 8 ≤ 552 → s₅.mem.readW (c + BitVec.ofNat 64 d) 64 = s₁.mem.readW (c + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    rw [mm, m₂]
    refine (Proof.ChaCha20.X86_64.Avx2.storeAll_frame (List.mem_singleton_self _) _
      Proof.ChaCha20.X86_64.Avx2.constPairs_le _).readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
  have g4 : ∀ r, r ∉ [Reg.rax, .r8, .r9, .r10, .r11, .rbx, .rbp] → s₄.gpr r = s₃.gpr r := k₄.1
  refine ⟨rdi₅, fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_, by rw [rd₅, k₄.2.2.1, rd₃, rd₂, rd₁],
    by rw [wr₅, k₄.2.2.2, wr₃, wr₂, wr₁], by rw [mm]; exact F₂,
    by rw [mm, m₂]; exact Proof.ChaCha20.X86_64.Avx2.consts_mem _ _,
    by rw [slot_eq, dsl 544 (by decide) (by decide), vl],
    by rw [dsl 520 (by decide) (by decide), v12], by rw [dsl 528 (by decide) (by decide), v13],
    by rw [dsl 536 (by decide) (by decide), v14], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₅ r h1, g4 r (by simp [h2, h3, h4, h5, h6, h7, h8]), g₃ r h1, g₂ r h2, g₁]
  · rw [g₅ _ (by decide), r8, rdi₃, m₃, ps_word F₂ (by decide)]
  · rw [g₅ _ (by decide), r9, rdi₃, m₃, ps_word F₂ (by decide)]
  · rw [g₅ _ (by decide), g₅ _ (by decide)]; exact r10
  · rw [g₅ _ (by decide), r11, rdi₃, m₃, ps_word F₂ (by decide)]
  · rw [g₅ _ (by decide), rbx, rdi₃, m₃, ps_word F₂ (by decide)]
  · rw [g₅ _ (by decide), rbp, rdi₃, m₃, ps_word F₂ (by decide)]

theorem leave_eq : leave = Impl.Poly1305.X86_64.reduce ++ ([.store (at_ .rcx accOff) .r11,
    .store (at_ .rcx (accOff + 8)) .rbx, .store (at_ .rcx (accOff + 16)) .rbp,
    .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .alu .add .rbp (.imm 512),
    .mov .rdx (.mem (at_ .rcx lenOff)), .alu .add .rsi (.imm 512),
    .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
    .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)] : List Instr) := rfl

/-- The accumulator stored, as `storeH` would at `psA c`. -/
abbrev accMem (m : Mem) (c : Addr) (h0 h1 h2 : BitVec 64) : Mem :=
  ((m.writeW (c + BitVec.ofNat 64 448) h0).writeW (c + BitVec.ofNat 64 456) h1).writeW
    (c + BitVec.ofNat 64 464) h2

theorem store_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) (hw : psR c ∈ s.wr) :
    WP isa (.block [.store (at_ .rcx accOff) .r11,
    .store (at_ .rcx (accOff + 8)) .rbx, .store (at_ .rcx (accOff + 16)) .rbp,
    .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .alu .add .rbp (.imm 512),
    .mov .rdx (.mem (at_ .rcx lenOff)), .alu .add .rsi (.imm 512),
    .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
    .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]) s fun s' =>
      s'.mem = accMem s.mem c (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp) ∧
      s'.gpr .rbx = s.gpr .rsi ∧ s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 + 512 ∧
      s'.gpr .rdx = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧ s'.gpr .rsi = s.gpr .rsi + 512 ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .rdx → r ≠ .rsi → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 →
        s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain o : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions s.wr (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
  obtain i : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions (s.rd ++ s.wr) (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, List.mem_append_right _ hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
  obtain o0 := o 448 (by decide) (by decide); have o1 := o 456 (by decide) (by decide)
  obtain o2 := o 464 (by decide) (by decide)
  obtain i0 := i 544 (by decide) (by decide); have i1 := i 520 (by decide) (by decide)
  obtain i2 := i 528 (by decide) (by decide); have i3 := i 536 (by decide) (by decide)
  apply WP.of_runBlock
  obtain se512 : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  obtain se128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, State.store64,
    State.load64, readSrc, execAlu, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, hrcx, accOff,
    r12Off, r13Off, r14Off, lenOff, ofInt_bf, Nat.reduceAdd, reduceCtorEq, o0, o1, o2, i0, i1, i2, i3,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, ite_false], trivial, trivial⟩
  all_goals simp (disch := decide) only [readW_writeW_ofNat, se512, se128, bfA, BitVec.add_sub_cancel]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-! The accumulator stored. -/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.Poly1305.X86_64 (hval Keeps off)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)
open VG.Proof.Poly1305 (absorbAll)

/-- The accumulator's region in the Poly1305 state. -/
abbrev accR (c : Addr) : Region := ⟨c + BitVec.ofNat 64 448, 24⟩

theorem accMem_frame (m : Mem) (c : Addr) (h0 h1 h2 : BitVec 64) :
    Frame [accR c] m (accMem m c h0 h1 h2) := by
  obtain ca : ∀ d, 448 ≤ d → d + 8 ≤ 472 → (accR c).Contains (c + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains c (by omega_arith) (by omega_arith) (by decide)
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ca 448 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (ca 456 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (ca 464 (by decide) (by decide))

theorem psA_24 (c : Addr) : psA c + 24 = c + BitVec.ofNat 64 472 := by
  rw [psA, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem off_ps (c : Addr) (d : Nat) : off (psA c) d = c + BitVec.ofNat 64 (448 + d) := by
  rw [Proof.Poly1305.X86_64.off_eq, psA, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem accMem_acc (m : Mem) (c : Addr) (h0 h1 h2 : BitVec 64) :
    leNum (bytesAt (accMem m c h0 h1 h2) (psA c) 24) = h0.toNat + 2 ^ 64 * h1.toNat + 2 ^ 128 * h2.toNat := by
  rw [Proof.Poly1305.X86_64.leNum_acc, off_ps, off_ps, off_ps]
  simp (disch := decide) only [accMem, Nat.reduceAdd, readW_writeW_ofNat, Mem.readW_writeW_self64]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
