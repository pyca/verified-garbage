module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming AES-CMAC on RISC-V: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`), as on PPC64LE
(`Proof/CmacAes/Stream/PPC64LE/AbsorbBlocks.lean`): the bytes held back
`h = held c`, the bytes copied after them `f = min L (16 - h)`, the data left
`L - f`, whether to chain the block held back (`b1`), the blocks chained
after it (`nb`), and the rest (`rest`); and the registers `absorb` saves at
`sv2 S`, where the functions it calls do not write.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.Stream.RISCV64
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 16 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 16 := by
  have := held_le c; unfold fOf; omega

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega

/-! ## Arithmetic on registers -/

/-- `sltu` of two numbers. -/
theorem sltu_ofNat {m k : Nat} (hm : m < 2 ^ 64) (hk : k < 2 ^ 64) :
    (if BitVec.ofNat 64 m < BitVec.ofNat 64 k then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if m < k then 1 else 0) := by
  have : (BitVec.ofNat 64 m < BitVec.ofNat 64 k) ↔ m < k := by
    rw [BitVec.lt_def, toNat_ofNat hm, toNat_ofNat hk]
  by_cases h : m < k
  · simp only [this.mpr h, h, ↓reduceIte]; rfl
  · simp only [show ¬ (BitVec.ofNat 64 m < BitVec.ofNat 64 k) from fun h' => h (this.mp h'), h, ↓reduceIte]; rfl

/-- `16 nb` for the data left `x > 0`, as `addi -1; andi 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 1 - ((BitVec.ofNat 64 x - BitVec.ofNat 64 1) &&& BitVec.ofInt 64 15) =
      BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega

/-! ## Saving the registers -/

/-- What `absorb` saves: the registers, with `t0` the slots' base. -/
abbrev absG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv2 S)).gpr

/-- The memory after saving the registers at `sv2 S`. -/
abbrev absMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem (sv2 S) (absG s₀ S) absSaved

theorem abs_bound : ∀ p ∈ absSaved, p.2 + 8 ≤ 56 := by decide

/-- Saving the registers changes only their slots. -/
theorem absMem_frame (s₀ : State) (S : Addr) : Frame [⟨sv2 S, 56⟩] s₀.mem (absMem s₀ S) :=
  Spill.saveMem_frame_base (n := 56) abs_bound (by decide) _ _ _

/-- What `save` leaves. -/
structure Saved₁ (s₀ : State) (S : Addr) (s : State) : Prop where
  s1 : s.gpr .s1 = s₀.gpr .a0
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = s₀.gpr .a3
  s4 : s.gpr .s4 = s₀.gpr .a4
  s6 : s.gpr .s6 = S
  other : ∀ r, r ≠ .t0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → r ≠ .s6 → s.gpr r = s₀.gpr r
  mem : s.mem = absMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem save_wp (s₀ : State) {S : Addr} (hS : s₀.gpr .a5 = S)
    (hw : ∀ d, d + 8 ≤ 56 → InRegions s₀.wr (sv2 S + BitVec.ofNat 64 d) 8) :
    WP isa (.block save) s₀ (Saved₁ s₀ S) := by
  rw [save, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .a5) fun s₁ e => ?_
  subst e
  rw [hS, show absSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 absSaved from rfl]
  have t₀ : (s₀.write .t0 (sv2 S)).gpr .t0 = sv2 S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv2 S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := absSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · rw [t₀]; exact hw _ (abs_bound p hp')
  generalize ht : ({ (s₀.write .t0 (sv2 S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv2 S)).mem ((s₀.write .t0 (sv2 S)).gpr .t0)
      (s₀.write .t0 (sv2 S)).gpr absSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have memt : t.mem = absMem s₀ S := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r a b c d e f => ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, gt]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, gt]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other, gt]
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other, gt]
  · simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.other, u₁.other, gt, hS]
  · rw [u₅.other _ f, u₄.other _ e, u₃.other _ d, u₂.other _ c, u₁.other _ b, gt _ a]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, memt]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .a2 = BitVec.ofNat 64 c) :
    WP isa held s fun s' => s'.gpr .t1 = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ev := eval_zero_ofNat s .a2 hc hd
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => ?_) (fun h => by cases h)
    exact wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr]; rfl,
      fun r h => u₁.other r h, u₁.mem, u₁.rd, u₁.wr⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine wp_subi (imm := 1) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ =>
      wp_addi (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, fun r a => ?_, ?_, ?_, ?_⟩
    · rw [u₃.gpr, u₂.gpr, u₁.gpr, hd, held_bv _ hne, toNat_ofNat hc]
    · rw [u₃.other _ a, u₂.other _ a, u₁.other _ a]
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]

/-! ## `fill`: how many bytes to copy, and where -/

theorem clamp_wp {s : State} {L : Nat} (hL : L < 2 ^ 64) (h4 : s.gpr .s4 = BitVec.ofNat 64 L) :
    WP isa clamp s fun s' => s'.gpr .t2 = BitVec.ofNat 64 (min L 16) ∧
      (∀ r, r ≠ .t2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have x2 : s₁.gpr .t2 = BitVec.ofNat 64 (L / 16) := by
    rw [u₁.gpr, h4, shr_ofNat hL]
  have ev := eval_zero_ofNat s₁ .t2 (by omega) x2
  by_cases hl : L < 16
  · have e : L / 16 = 0 := by omega
    refine WP.ite true (by rw [ev, e]; rfl) (fun _ => ?_) (fun h => by cases h)
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_mv fun s₂ u₂ => WP.block_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, u₁.other _ (by decide), h4, Nat.min_eq_left (Nat.le_of_lt hl)]
  · have e : L / 16 ≠ 0 := by omega
    refine WP.ite false (by rw [ev]; simp [e]) (fun h => by cases h) fun _ => ?_
    refine wp_li (imm := 16) (by decide) fun s₂ u₂ => WP.block_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, Nat.min_eq_right (Nat.le_of_not_lt hl)]

theorem fill_wp {s : State} {St D : Addr} {c L : Nat} (hL : L < 2 ^ 64)
    (h1 : s.gpr .t1 = BitVec.ofNat 64 (held c)) (h4 : s.gpr .s4 = BitVec.ofNat 64 L)
    (hs1 : s.gpr .s1 = St) (hs3 : s.gpr .s3 = D) :
    WP isa fill s fun s' => s'.gpr .t2 = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .a7 = BitVec.ofNat 64 (fOf c L) ∧ s'.gpr .t5 = St + BitVec.ofNat 64 (288 + held c) ∧
      s'.gpr .t6 = D ∧
      (∀ r, r ≠ .a7 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hh := held_le c
  refine WP.seq (WP.mono (clamp_wp hL h4) fun s₁ ⟨x2₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (wp_li (imm := 16) (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ => wp_sltu fun s₄ u₄ =>
    WP.block_nil ?_)
  have x1₁ : s₁.gpr .t1 = BitVec.ofNat 64 (held c) := by rw [g₁ _ (by decide), h1]
  have x3₄ : s₄.gpr .t3 = BitVec.ofNat 64 (16 - held c) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), x1₁, Offset.ofNat_sub_ofNat hh]
  have x2₄ : s₄.gpr .t2 = BitVec.ofNat 64 (min L 16) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), x2₁]
  have x4₄ : s₄.gpr .t4 = BitVec.ofNat 64 (if min L 16 < 16 - held c then 1 else 0) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), x2₁, u₃.gpr, u₂.gpr, u₂.other _ (by decide),
      x1₁, Offset.ofNat_sub_ofNat hh]
    exact sltu_ofNat (by omega) (by omega)
  have g₄ (r : Reg) (a : r ≠ .t3) (b : r ≠ .t4) : s₄.gpr r = s₁.gpr r := by
    rw [u₄.other _ b, u₃.other _ a, u₂.other _ a]
  have hf : fOf c L = min (min L 16) (16 - held c) := by unfold fOf; omega
  have ev := eval_zero_ofNat s₄ .t4 (k := if min L 16 < 16 - held c then 1 else 0) (by split <;> omega) x4₄
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .t2 = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .t2 → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr) ?_
    fun s₅ h₅ => ?_)
  · by_cases hl : min L 16 < 16 - held c
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => WP.block_nil ?_
      exact ⟨by rw [x2₄, hf, Nat.min_eq_left (Nat.le_of_lt hl)], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      unfold Impl.AesCbc.RISCV64.mov
      refine wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, fun r h => u₅.other r h, u₅.mem, u₅.rd, u₅.wr⟩
      rw [u₅.gpr, x3₄, hf, Nat.min_eq_right (Nat.le_of_not_lt hl)]
  · obtain ⟨x2₅, g₅, m₅, rd₅, wr₅⟩ := h₅
    have g (r : Reg) (a : r ≠ .t2) (b : r ≠ .t3) (d : r ≠ .t4) : s₅.gpr r = s.gpr r := by
      rw [g₅ r a, g₄ r b d, g₁ r a]
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_mv fun s₆ u₆ => wp_add fun s₇ u₇ => wp_addi (imm := 288) (by decide) fun s₈ u₈ =>
      wp_mv fun s₉ u₉ => WP.block_nil ⟨?_, ?_, ?_, ?_, fun r a b d e f h => ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), x2₅]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, x2₅]
    · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₆.other _ (by decide),
        g .s1 (by decide) (by decide) (by decide), g .t1 (by decide) (by decide) (by decide), hs1, h1,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
    · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        g .s3 (by decide) (by decide) (by decide), hs3]
    · rw [u₉.other _ h, u₈.other _ f, u₇.other _ f, u₆.other _ a, g r b d e]
    · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, u₄.mem, u₃.mem, u₂.mem, m₁]
    · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅, u₄.wr, u₃.wr, u₂.wr, wr₁]

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h3 : s.gpr .s3 = D) (ha7 : s.gpr .a7 = BitVec.ofNat 64 f) (h4 : s.gpr .s4 = BitVec.ofNat 64 L)
    (hs1 : s.gpr .s1 = St) (hs6 : s.gpr .s6 = S) :
    WP isa chain1 s fun s' => s'.gpr .s3 = D + BitVec.ofNat 64 f ∧ s'.gpr .s4 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .a4 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .a0 = St ∧
      s'.gpr .a1 = s.gpr .s2 ∧ s'.gpr .a2 = St + BitVec.ofNat 64 272 ∧
      s'.gpr .a3 = St + BitVec.ofNat 64 288 ∧ s'.gpr .a5 = S ∧
      (∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_li (imm := 0) (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have x4₃ : s₃.gpr .s4 = BitVec.ofNat 64 (L - f) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4, u₁.other _ (by decide), ha7,
      Offset.ofNat_sub_ofNat hf]
  have g₃ (r : Reg) (a : r ≠ .s3) (b : r ≠ .s4) (c : r ≠ .a4) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ c, u₂.other _ b, u₁.other _ a]
  have ev := eval_zero_ofNat s₃ .s4 (k := L - f) (by omega) x4₃
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .a4 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .a4 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr) ?_
    fun s₄ h₄ => ?_)
  · by_cases h0 : L - f = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [u₃.gpr]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_li (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ⟨?_, fun r h => u₄.other r h, u₄.mem, u₄.rd, u₄.wr⟩
      rw [u₄.gpr]; simp [h0]
  · obtain ⟨x4₄, g₄, m₄, rd₄, wr₄⟩ := h₄
    have g (r : Reg) (a : r ≠ .s3) (b : r ≠ .s4) (c : r ≠ .a4) : s₄.gpr r = s.gpr r := by
      rw [g₄ r c, g₃ r a b c]
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_addi (imm := 272) (by decide) fun s₇ u₇ =>
      wp_addi (imm := 288) (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h3, ha7]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide), x4₃]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), x4₄]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr, g .s1 (by decide) (by decide) (by decide), hs1]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
        u₅.other _ (by decide), g .s2 (by decide) (by decide) (by decide)]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
        u₅.other _ (by decide), g .s1 (by decide) (by decide) (by decide), hs1]
    · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g .s1 (by decide) (by decide) (by decide), hs1]
    · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g .s6 (by decide) (by decide) (by decide), hs6]
    · obtain ⟨-, -, -, -, -, -, -, -, n0, n1, n2, n3, n4, n5, -⟩ := preserved_ne r hr
      rw [u₉.other _ n5, u₈.other _ n3, u₇.other _ n2, u₆.other _ n1, u₅.other _ n0, g r a b n4]
    · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr]

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h4 : s.gpr .s4 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .s5 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .a4 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .a0 = s.gpr .s1 ∧
      s'.gpr .a1 = s.gpr .s2 ∧ s'.gpr .a2 = s.gpr .s1 + BitVec.ofNat 64 272 ∧
      s'.gpr .a3 = s.gpr .s3 ∧ s'.gpr .a5 = s.gpr .s6 ∧
      (∀ r ∈ preserved, r ≠ .s5 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have ev := eval_zero_ofNat s₁ .s4 hx (by rw [u₁.other _ (by decide), h4])
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .s5 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .s5 → r ≠ .t1 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [u₁.gpr]; simp [h0], fun _ _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_subi (imm := 1) (by decide) fun s₂ u₂ => wp_andi (by decide) fun s₃ u₃ =>
        wp_sub fun s₄ u₄ => WP.block_nil ⟨?_, fun r a b => ?_, ?_, ?_, ?_⟩
      · rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4]
        simp only [h0, ↓reduceIte]
        exact nb16_bv (by omega) hx
      · rw [u₄.other _ a, u₃.other _ b, u₂.other _ a]
      · rw [u₄.mem, u₃.mem, u₂.mem]
      · rw [u₄.rd, u₃.rd, u₂.rd]
      · rw [u₄.wr, u₃.wr, u₂.wr]
  · obtain ⟨x5₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .s5) (b : r ≠ .t1) : s₂.gpr r = s.gpr r := by rw [g₂ r a b, u₁.other _ a]
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_srl (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
      wp_addi (imm := 272) (by decide) fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a => ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, x5₂]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, x5₂]
      exact (shr_ofNat (by split <;> omega)).trans (by congr 1; omega)
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g]
    · obtain ⟨-, n1, -, -, -, -, -, -, n0, na1, na2, na3, na4, na5, -⟩ := preserved_ne r hr
      rw [u₈.other _ na5, u₇.other _ na3, u₆.other _ na2, u₅.other _ na1, u₄.other _ n0, u₃.other _ na4, g r a n1]
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]
    · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
    · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## `rest`: the arguments of the last copy -/

theorem rest_wp {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h3 : s.gpr .s3 = D + BitVec.ofNat 64 a) (h5 : s.gpr .s5 = BitVec.ofNat 64 (16 * n))
    (h4 : s.gpr .s4 = BitVec.ofNat 64 x) :
    WP isa (.block rest) s fun s' => s'.gpr .s3 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .s4 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .t5 = s.gpr .s1 + BitVec.ofNat 64 288 ∧
      s'.gpr .t6 = D + BitVec.ofNat 64 (a + 16 * n) ∧ s'.gpr .t2 = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : D + BitVec.ofNat 64 a + BitVec.ofNat 64 (16 * n) = D + BitVec.ofNat 64 (a + 16 * n) :=
    Offset.add_add _ _ _
  unfold rest Impl.AesCbc.RISCV64.mov
  refine wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_addi (imm := 288) (by decide) fun s₃ u₃ =>
    wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h3, h5, e]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, h4, h5]
    exact Offset.ofNat_sub_ofNat hn
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other]
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.gpr, h3, h5, e]
  · simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.gpr, u₁.other, h4, h5]
    exact Offset.ofNat_sub_ofNat hn
  · obtain ⟨-, -, n2, -, -, n5, n6, -⟩ := preserved_ne r hr
    rw [u₅.other _ n2, u₄.other _ n6, u₃.other _ n5, u₂.other _ b, u₁.other _ a]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.CmacAes.Stream.RISCV64
