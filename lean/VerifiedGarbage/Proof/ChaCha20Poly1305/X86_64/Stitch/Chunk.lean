import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor

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
theorem firstBlock_succ (n : Nat) : firstBlock (n + 1) = firstBlock n + blocks n := by
  unfold firstBlock blocks; split <;> split <;> omega

theorem firstBlock_ten : firstBlock 10 = 32 := rfl

/-- The registers of the kernel and the reads of Poly1305 during the rounds,
relative to the state `s₁` after the kernel's setup. -/
structure SR (buf q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n : Nat) (s : State) : Prop where
  holds : Holds buf false (fun j => Nat.repeat innerBlock n (V j)) s
  m16 : ∀ l, s.lane .xmm15 l = rot16Mask
  frame : Frame [slotsR buf] s₁.mem s.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * firstBlock n))) s

section
variable {buf q : Addr} {R0 R1 : BitVec 64} {X : Nat} {V : Nat → CState} {s₁ : State}

/-- The bytes Poly1305 reads are apart from the slots the rounds write. -/
theorem bytes_frame {m m' : Mem} (hf : Frame [slotsR buf] m m') (hd : (dR5 q).Disjoint (slotsR buf))
    {j n : Nat} (hjn : j + n ≤ 512) :
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
    exact hd.symm _ hc (Offset.contains_base q (d := j) (n := 1) (k := 512) (by omega) (by lit_omega))

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
    (hd : (dR5 q).Disjoint (slotsR buf))
    (hin : ∀ off n, off + n ≤ 512 → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
    {j : Nat} (hj : j < 32) {p : Bool} {vs : Nat → CState} {s : State}
    (h : SI buf s₁ p vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (.block (addProd j)) s (SI buf s₁ p vs (HalfTo q R0 R1 X s₁ j)) := by
  refine WP.mono (addProd_ok hk h.poly (p := q) (by rw [h.gpr _ (by decide), hrsi]) (j := j)
    fun e he => by rw [h.rd, h.wr]; exact hin _ _ (by omega)) fun s' ⟨a, k, x, y⟩ => h.piece ?_ k x y
  show Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1)))) s'
  rw [Nat.mul_add, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega),
    ← bytes_frame h.frame hd (j := 16 * j) (n := 16) (by omega)]
  exact a

theorem carry_si {R0 R1 : BitVec 64} {X : Nat} (hk : Key R0 R1) {j : Nat} {p : Bool}
    {vs : Nat → CState} {s : State} (h : SI buf s₁ p vs (HalfTo q R0 R1 X s₁ j) s) :
    WP isa (.block Impl.Poly1305.X86_64.carry) s (SI buf s₁ p vs (AccTo q R0 R1 X s₁ (j + 1))) :=
  WP.mono (carry1_ok hk h.poly) fun _ ⟨a, k, x, y⟩ => h.piece a k x y

section
variable (hk : Key R0 R1) (hrcx : s₁.gpr .rcx = buf)
  (hrsi : s₁.gpr .rsi = q) (hb : bufR buf ∈ s₁.wr) (h8 : M8 s₁.mem buf)
  (hd : (dR5 q).Disjoint (slotsR buf))
  (hin : ∀ off n, off + n ≤ 512 → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
include hk hrcx hrsi hb h8 hd hin

theorem sround4_ok {j : Nat} (hj : j + 4 ≤ 32) {vs : Nat → CState} {s : State}
    (h : SI buf s₁ false vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (sround4 j) s (SI buf s₁ false (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ (j + 4))) := by
  unfold sround4
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hin (by omega) h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (swap_si (p := false) acc_gpr hrcx hb h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hin (by omega) h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hin (by omega) h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (swap_si (p := true) acc_gpr hrcx hb h₁₃) fun t₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁₄) fun t₁₅ h₁₅ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hin (by omega) h₁₅) fun t₁₆ h₁₆ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₁₆) fun t₁₇ h₁₇ => ?_)
  exact carry_si hk h₁₇

theorem sround3_ok {j : Nat} (hj : j + 3 ≤ 32) {vs : Nat → CState} {s : State}
    (h : SI buf s₁ false vs (AccTo q R0 R1 X s₁ j) s) :
    WP isa (sround3 j) s (SI buf s₁ false (fun i => innerBlock (vs i)) (AccTo q R0 R1 X s₁ (j + 3))) := by
  unfold sround3
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hin (by omega) h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (swap_si (p := false) half_gpr hrcx hb h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hin (by omega) h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (carry_si hk h₁₀) fun t₁₁ h₁₁ => ?_)
  refine WP.seq (WP.mono (swap_si (p := true) acc_gpr hrcx hb h₁₁) fun t₁₂ h₁₂ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) acc_gpr hrcx hb h8 h₁₂) fun t₁₃ h₁₃ => ?_)
  refine WP.seq (WP.mono (addProd_si hk hrsi hd hin (by omega) h₁₃) fun t₁₄ h₁₄ => ?_)
  refine WP.seq (WP.mono (quarter_si (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) half_gpr hrcx hb h8 h₁₄) fun t₁₅ h₁₅ => ?_)
  exact carry_si hk h₁₅

theorem srounds_ok : ∀ n, n ≤ 10 → SR buf q R0 R1 X V s₁ 0 s₁ → WP isa (srounds n) s₁ (SR buf q R0 R1 X V s₁ n)
  | 0, _, h => WP.block_nil h
  | n + 1, hn, h => by
    refine WP.seq (WP.mono (srounds_ok n (by omega) h) fun s hs => ?_)
    have hs' : SI buf s₁ false (fun j => Nat.repeat innerBlock n (V j)) (AccTo q R0 R1 X s₁ (firstBlock n)) s :=
      ⟨hs.holds, hs.m16, hs.frame, hs.gpr, hs.rd, hs.wr, hs.acc⟩
    have hb' : firstBlock n + blocks n ≤ 32 := by
      rw [← firstBlock_succ]; unfold firstBlock; split <;> omega
    have fin : ∀ {s'}, SI buf s₁ false (fun j => Nat.repeat innerBlock (n + 1) (V j))
        (AccTo q R0 R1 X s₁ (firstBlock n + blocks n)) s' → SR buf q R0 R1 X V s₁ (n + 1) s' :=
      fun h' => ⟨h'.holds, h'.m16, h'.frame, h'.gpr, h'.rd, h'.wr, by rw [firstBlock_succ]; exact h'.poly⟩
    show WP isa (if n < 2 then sround4 (firstBlock n) else sround3 (firstBlock n)) s _
    split
    · rename_i hn2
      have e : blocks n = 4 := by unfold blocks; exact ite_eq_left_iff.mpr fun h => absurd hn2 h
      rw [e] at hb' fin
      exact WP.mono (sround4_ok hk hrcx hrsi hb h8 hd hin hb' hs') fun _ h' => fin h'
    · rename_i hn2
      have e : blocks n = 3 := by unfold blocks; exact ite_eq_right_iff.mpr fun h => absurd h hn2
      rw [e] at hb' fin
      exact WP.mono (sround3_ok hk hrcx hrsi hb h8 hd hin hb' hs') fun _ h' => fin h'

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

/-- The 512 bytes after `q` XORed with eight blocks of keystream from the
state at `st`, while the 512 bytes at `q` are absorbed. -/
theorem chunkMain_ok {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hwd : DWin s.wr (q + 512))
    (hin : ∀ off n, off + n ≤ 512 → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsd : (stR st).Disjoint (dR5 (q + 512))) (dsb : (stR st).Disjoint (bufR buf))
    (dbd : (bufR buf).Disjoint (dR5 (q + 512))) (dqs : (dR5 q).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa chunkMain s fun s' =>
        (∀ k < 512, s'.mem (q + 512 + BitVec.ofNat 64 k) = s.mem (q + 512 + BitVec.ofNat 64 k) ^^^
          (serialize (plus (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j))
            (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
        Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q 512)) s' ∧
        Frame [slotsR buf, dR5 (q + 512)] s.mem s'.mem ∧
        (∀ r, r ∉ absorbRegs → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.gpr .rsi = q + 512 ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold chunkMain
  refine WP.seq (WP.mono (setup_ok hrdi hrcx hst hb hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem buf := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR buf] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  have q₁ : bytesAt s₁.mem q 512 = bytesAt s.mem q 512 := by
    have := bytes_frame F₁ dqs (j := 0) (n := 512) (by decide)
    simpa using this
  have h0 : SR buf q R0 R1 X (fun j => ctr (stateAt s.mem st) j) s₁ 0 s₁ :=
    ⟨hh, h15, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      rw [show 16 * firstBlock 0 = 0 from rfl, show bytesAt s₁.mem q 0 = [] from rfl,
        VG.Proof.Poly1305.absorbAll_nil]
      exact ⟨by rw [g₁]; exact hacc.r8, by rw [g₁]; exact hacc.r9, by rw [g₁]; exact hacc.r10,
        by rw [g₁]; exact hacc.h2, by simp only [hval, g₁]; exact hacc.val⟩⟩
  refine WP.seq (WP.mono (srounds_ok hk (by rw [g₁, hrcx]) (by rw [g₁, hrsi]) (by rw [wr₁]; exact hb) c₁.m8 dqs
    (by rw [rd₁, wr₁]; exact hin) 10 (by decide) h0) fun s₂ h₂ => ?_)
  refine WP.block_append (WP.mono (addRsi_ok s₂) fun s₃ ⟨rsi₃, g₃, x₃, y₃, m₃, rd₃, wr₃⟩ => ?_)
  have gk : ∀ r, r ∉ absorbRegs → r ≠ .rsi → s₃.gpr r = s.gpr r := fun r hr hs => by
    rw [g₃ r hs, h₂.gpr r hr, g₁]
  have rsi₃' : s₃.gpr .rsi = q + 512 := by rw [rsi₃, h₂.gpr _ (by decide), g₁, hrsi]
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
  have hq₃ : ∀ k < 512, s₃.mem (q + 512 + BitVec.ofNat 64 k) = s.mem (q + 512 + BitVec.ofNat 64 k) := by
    intro k hk'
    refine F₃ _ ?_
    simp only [List.mem_singleton, forall_eq]
    intro hc'
    exact dbd _ ((slotsR_sub buf) _ hc') (Offset.contains_base (q + 512) (d := k) (n := 1) (k := 512) (by omega)
      (by lit_omega))
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
