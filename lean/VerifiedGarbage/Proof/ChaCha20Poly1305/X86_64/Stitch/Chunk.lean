module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
public import VerifiedGarbage.Proof.Poly1305.Spec
public import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL

/-!
# ChaCha20 and Poly1305 together (x86-64): the blocks of Poly1305

A chunk's double rounds absorb the blocks at `rsi + 16 j` with the scalar
Poly1305, as `vg_poly1305_blocks` does, into the accumulator in `r11`,
`rbx`, `rbp`, under the clamped key in `r8`–`r10` (`Acc`), each in two
pieces: `Stitch.addProd j` (`addProd_ok`, from `prods_ok`), which leaves the
products of the sum (`Half`), and the carry (`carry1_ok`, from `carryP_ok`).
The pieces read memory and write only Poly1305's registers (`absorbRegs`),
and no vector register (`WP.vecKeep`), so ChaCha20's quarter rounds, which
they run between, keep their state; `Acc` and `Half` read only registers,
which the quarter rounds keep.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.Poly1305.X86_64 (hval prods_ok carryP_ok Prods Keeps absorbRegs)
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
    Impl.Poly1305.X86_64.products, Impl.Poly1305.X86_64.mulTo, Impl.Poly1305.X86_64.mulAdd,
    List.cons_append, List.nil_append, List.all_cons, List.all_nil, scalarI, Bool.and_true]

theorem scal_carry : scalCode (.block Impl.Poly1305.X86_64.carry) = true := by
  simp only [scalCode, Impl.Poly1305.X86_64.carry, List.all_cons, List.all_nil, scalarI, Bool.and_true]

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
    Prods a0 a1 a2 R0.toNat (R1.toNat / 4) s

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
  have hq : R1.toNat / 4 < 2 ^ 58 := by have := hk.r1; omega
  have hr1 : (s.gpr .r9).toNat = 4 * (R1.toNat / 4) := by rw [h.r9]; have := hk.r1_mod; omega
  have i0 := hin 0 (by decide)
  have i8 := hin 8 (by decide)
  rw [Nat.add_zero] at i0
  refine WP.mono (WP.vecKeep (scal_addProd _) (prods_ok s (b := .rsi) (d := 16 * j) (by decide)
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
    WP isa (.block Impl.Poly1305.X86_64.carry) s fun s' =>
      Acc R0 R1 Y s' ∧ Keeps absorbRegs s s' ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  obtain ⟨a0, a1, a2, ea, hP⟩ := h.prods
  refine WP.mono (WP.vecKeep scal_carry (carryP_ok s a0 a1 a2 R0.toNat (R1.toNat / 4)))
    fun s' ⟨⟨hc, k⟩, vx, vy⟩ => ⟨?_, k, vx, vy⟩
  obtain ⟨m, hb⟩ := hc hP
  have hr : R0.toNat + 2 ^ 64 * (4 * (R1.toNat / 4)) = rN R0 R1 := by
    have := hk.r1_mod; simp only [rN]; omega
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
  · simp only [Bool.false_eq_true, ite_false]; split <;> split <;> omega
  · simp only [ite_true]
    by_cases h0 : n = 0
    · subst h0; rfl
    · simp only [show n + 1 ≠ 0 by omega, h0, ite_false]; split <;> omega

theorem firstBlock_ten (pre : Bool) : firstBlock pre 10 = total pre := by cases pre <;> rfl

theorem total_le (pre : Bool) : total pre ≤ 32 := by cases pre <;> decide

theorem firstBlock_le (pre : Bool) {n : Nat} (hn : n ≤ 10) : firstBlock pre n ≤ total pre := by
  unfold firstBlock total; cases pre <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> split <;> omega

theorem blocks_cases (pre : Bool) (n : Nat) : blocks pre n = 4 ∨ blocks pre n = 3 ∨ blocks pre n = 0 := by
  unfold blocks; cases pre <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> split <;>
    (try split) <;> simp

/-- A schedule of the blocks the ten double rounds absorb: `bl n` blocks
(0, 3 or 4) in round `n`, from block `fb n`, `tot` in all. -/
structure SchedOk (bl fb : Nat → Nat) (tot : Nat) : Prop where
  first0 : fb 0 = 0
  succ : ∀ n, n < 10 → fb (n + 1) = fb n + bl n
  le : ∀ n, n ≤ 10 → fb n ≤ tot
  cases : ∀ n, n < 10 → bl n = 4 ∨ bl n = 3 ∨ bl n = 0
  four : ∀ n, n < 10 → bl n ≠ 0 → 4 ≤ fb n + bl n

/-- A chunk's schedule. -/
theorem schedOk_pre (pre : Bool) : SchedOk (blocks pre) (firstBlock pre) (total pre) where
  first0 := by cases pre <;> rfl
  succ n _ := firstBlock_succ pre n
  le n hn := firstBlock_le pre hn
  cases n _ := blocks_cases pre n
  four n _ := by
    unfold firstBlock blocks; cases pre <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;>
      split <;> (try split) <;> omega

/-- The registers of the kernel and the reads of Poly1305 during the rounds
of a schedule (`fb`), relative to the state `s₁` after the kernel's setup. -/
structure SRS (fb : Nat → Nat) (buf q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n : Nat) (s : State) : Prop where
  holds : Holds buf false (fun j => Nat.repeat innerBlock n (V j)) s
  m16 : ∀ l, s.lane .xmm15 l = rot16Mask
  frame : Frame [slotsR buf] s₁.mem s.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * fb n))) s

/-- `SRS` during a chunk's rounds. -/
abbrev SR (pre : Bool) := SRS (firstBlock pre)

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
      show BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) by rw [BitVec.ofNat_add]; rfl, ih (by omega)]
    congr 1
    refine hf _ ?_
    simp only [List.mem_singleton, forall_eq]
    intro hc
    exact hd.symm _ hc (Offset.contains_base q (d := j) (n := 1) (k := B) (by omega) (by lit_omega))

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
    fun e he => by rw [h.rd, h.wr]; exact hin _ _ (by omega)) fun s' ⟨a, k, x, y⟩ => h.piece ?_ k x y
  show Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1)))) s'
  rw [Nat.mul_add, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega),
    ← bytes_frame h.frame hd (by omega) (j := 16 * j) (n := 16) (by omega)]
  exact a

theorem carry_si {R0 R1 : BitVec 64} {X : Nat} (hk : Key R0 R1) {j : Nat} {p : Bool}
    {vs : Nat → CState} {s : State} (h : SI buf s₁ p vs (HalfTo q R0 R1 X s₁ j) s) :
    WP isa (.block Impl.Poly1305.X86_64.carry) s (SI buf s₁ p vs (AccTo q R0 R1 X s₁ (j + 1))) :=
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
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega) h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (swap_si (p := false) acc_gpr hrcx hb h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega) h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega) h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (swap_si (p := true) acc_gpr hrcx hb h₁₃) fun t₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁₄) fun t₁₅ h₁₅ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega) h₁₅) fun t₁₆ h₁₆ => ?_)
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
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega) h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (swap_si (p := false) half_gpr hrcx hb h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega) h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (swap_si (p := true) acc_gpr hrcx hb h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hT hin (by omega) h₁₃) fun t₁₄ h₁₄ => ?_)
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

theorem sroundsS_ok {bl fb : Nat → Nat} {tot : Nat} (sc : SchedOk bl fb tot) (htot : tot ≤ T) :
    ∀ n, n ≤ 10 → SRS fb buf q R0 R1 X V s₁ 0 s₁ → WP isa (sroundsS bl fb n) s₁ (SRS fb buf q R0 R1 X V s₁ n)
  | 0, _, h => WP.block_nil h
  | n + 1, hn, h => by
    refine WP.seq (WP.mono (sroundsS_ok sc htot n (by omega) h) fun s hs => ?_)
    have hs' : SI buf s₁ false (fun j => Nat.repeat innerBlock n (V j))
        (AccTo q R0 R1 X s₁ (fb n)) s :=
      ⟨hs.holds, hs.m16, hs.frame, hs.gpr, hs.rd, hs.wr, hs.acc⟩
    have hb' : fb n + bl n ≤ T := by
      rw [← sc.succ n (by omega)]; exact Nat.le_trans (sc.le _ hn) htot
    have fin : ∀ {s'}, SI buf s₁ false (fun j => Nat.repeat innerBlock (n + 1) (V j))
        (AccTo q R0 R1 X s₁ (fb n + bl n)) s' → SRS fb buf q R0 R1 X V s₁ (n + 1) s' :=
      fun h' => ⟨h'.holds, h'.m16, h'.frame, h'.gpr, h'.rd, h'.wr, by rw [sc.succ n (by omega)]; exact h'.poly⟩
    show WP isa (sroundS bl fb n) s _
    unfold sroundS
    rcases sc.cases n (by omega) with e | e | e
    · rw [ite_eq_left e]
      rw [e] at hb' fin
      exact WP.mono (sround4_ok hk hrcx hrsi hb h8 hd hT hin hb' hs') fun _ h' => fin h'
    · rw [ite_eq_right (by omega), ite_eq_left e]
      rw [e] at hb' fin
      exact WP.mono (sround3_ok hk hrcx hrsi hb h8 hd hT hin hb' hs') fun _ h' => fin h'
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [e, Nat.add_zero] at fin
      exact WP.mono (sround0_ok hrcx hb h8 hs') fun _ h' => fin h'

theorem srounds_ok (pre : Bool) (htot : total pre ≤ T) (n : Nat) (hn : n ≤ 10) (h : SR pre buf q R0 R1 X V s₁ 0 s₁) :
    WP isa (srounds pre n) s₁ (SR pre buf q R0 R1 X V s₁ n) :=
  sroundsS_ok hk hrcx hrsi hb h8 hd hT hin (schedOk_pre pre) htot n hn h

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
    fun e he => by rw [h.rd, h.wr]; exact hin _ _ (by omega)) fun s' ⟨a, k, x, y⟩ => h.piece ?_ k x y
  show Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1)))) s'
  rw [Nat.mul_add, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega)]
  rw [h.mem] at a
  exact a

theorem carryV_si (hk : Key R0 R1) {j : Nat} {vs : Nat → CState} {s : State}
    (h : SIV s₁ vs (HalfTo q R0 R1 X s₁ j) s) :
    WP isa (.block Impl.Poly1305.X86_64.carry) s (SIV s₁ vs (AccTo q R0 R1 X s₁ (j + 1))) :=
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
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₄) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₁₃) fun t₁₅ h₁₅ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₁₅) fun t₁₆ h₁₆ => ?_)
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
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₃) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (carryV_si hk h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarterV_siv (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr h₁₁) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (addProdV_si hk hrsi hin (by omega) h₁₃) fun t₁₄ h₁₄ => ?_)
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

theorem sroundsVS_ok {bl fb : Nat → Nat} {tot : Nat} (sc : SchedOk bl fb tot) (htot : tot ≤ T)
    {V : Nat → CState} {s : State}
    (h : SIV s₁ V (AccTo q R0 R1 X s₁ (fb 0)) s) : ∀ n, n ≤ 10 →
    WP isa (sroundsVS bl fb n) s
      (SIV s₁ (fun j => Nat.repeat innerBlock n (V j)) (AccTo q R0 R1 X s₁ (fb n)))
  | 0, _ => WP.block_nil h
  | n + 1, hn => by
    refine WP.seq (WP.mono (sroundsVS_ok sc htot h n (by omega)) fun s hs => ?_)
    have hb' : fb n + bl n ≤ T := by
      rw [← sc.succ n (by omega)]; exact Nat.le_trans (sc.le _ hn) htot
    show WP isa (sroundVS bl fb n) s _
    rw [sc.succ n (by omega)]
    unfold sroundVS
    rcases sc.cases n (by omega) with e | e | e
    · rw [ite_eq_left e]
      rw [e] at hb' ⊢
      exact sround4V_ok hk hrsi hin hb' hs
    · rw [ite_eq_right (by omega), ite_eq_left e]
      rw [e] at hb' ⊢
      exact sround3V_ok hk hrsi hin hb' hs
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), e, Nat.add_zero]
      exact sround0V_ok hs

/-- A schedule's rounds with `vprold` end as `sroundsS` does. -/
theorem sroundsVLS_ok {bl fb : Nat → Nat} {tot : Nat} (sc : SchedOk bl fb tot) (htot : tot ≤ T)
    {V : Nat → CState} (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) (h16 : M16 s₁.mem buf) (n : Nat) (hn : n ≤ 10)
    (h : SRS fb buf q R0 R1 X V s₁ 0 s₁) :
    WP isa (sroundsVLS bl fb n) s₁ (SRS fb buf q R0 R1 X V s₁ n) := by
  unfold sroundsVLS
  refine WP.seq (WP.mono (loadV_ok h.holds hrcx hb) fun s₂ ⟨h₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have i₂ : SIV s₁ V (AccTo q R0 R1 X s₁ (fb 0)) s₂ :=
    ⟨h₂, m₂, fun r _ => by rw [g₂], rd₂, wr₂, acc_gpr s₁ s₂ g₂ h.acc⟩
  refine WP.seq (WP.mono (sroundsVS_ok hk hrsi hin sc htot i₂ n hn) fun s₃ h₃ => ?_)
  have r₃ : s₃.gpr .rcx = buf := by rw [h₃.gpr _ (by decide), hrcx]
  refine WP.mono (storeV_ok (s₀ := s₃) ⟨h₃.holds, rfl, rfl, rfl, rfl⟩ r₃ (by rw [h₃.wr]; exact hb)
    (by rw [h₃.mem]; exact h16)) fun s₄ h₄ => ?_
  exact ⟨h₄.holds, h₄.m16, by rw [← h₃.mem]; exact h₄.frame, fun r hr => by rw [h₄.gpr, h₃.gpr r hr],
    by rw [h₄.rd, h₃.rd], by rw [h₄.wr, h₃.wr], acc_gpr s₃ s₄ h₄.gpr h₃.poly⟩

/-- A schedule's rounds, with `vprold` or without. -/
theorem sroundsForS_ok (vl : Bool) {bl fb : Nat → Nat} {tot : Nat} (sc : SchedOk bl fb tot) (htot : tot ≤ T)
    (hT : T ≤ 32) {V : Nat → CState} (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) (h8 : Proof.ChaCha20.X86_64.Avx2.M8 s₁.mem buf) (h16 : M16 s₁.mem buf)
    (hd : (⟨q, 16 * T⟩ : Region).Disjoint (slotsR buf))
    (h : SRS fb buf q R0 R1 X V s₁ 0 s₁) :
    WP isa (sroundsForS vl bl fb) s₁ (SRS fb buf q R0 R1 X V s₁ 10) := by
  cases vl
  · exact sroundsS_ok hk hrcx hrsi hb h8 hd hT hin sc htot 10 (by decide) h
  · exact sroundsVLS_ok hk hrsi hin sc htot hrcx hb h16 10 (by decide) h

/-- A chunk's rounds, with `vprold` or without. -/
theorem sroundsFor_ok (vl pre : Bool) (htot : total pre ≤ T) (hT : T ≤ 32) {V : Nat → CState} (hrcx : s₁.gpr .rcx = buf)
    (hb : bufR buf ∈ s₁.wr) (h8 : Proof.ChaCha20.X86_64.Avx2.M8 s₁.mem buf) (h16 : M16 s₁.mem buf)
    (hd : (⟨q, 16 * T⟩ : Region).Disjoint (slotsR buf))
    (h : SR pre buf q R0 R1 X V s₁ 0 s₁) :
    WP isa (sroundsFor vl pre) s₁ (SR pre buf q R0 R1 X V s₁ 10) :=
  sroundsForS_ok hk hrsi hin vl (schedOk_pre pre) htot hT hrcx hb h8 h16 hd h

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
    have := bytes_frame F₁ dqs (by decide) (j := 0) (n := 16 * total pre) (by omega)
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
      (by omega) (by lit_omega))
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
      Offset.ofNat_sub_ofNat (by omega)]
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
    Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega), Proof.Poly1305.X86_64.toNat_ofNat_lt (by decide)]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
