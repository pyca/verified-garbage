module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `CmacAes.Stream.RISCV64.AbsorbBlocks`, which only this module used -/

section

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
  have := held_le c; unfold fOf; omega_using [this]

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega_using [this]

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
  obtain e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hx, hx']
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega_using []

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
  obtain t₀ : (s₀.write .t0 (sv2 S)).gpr .t0 = sv2 S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv2 S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := absSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · rw [t₀]; exact hw _ (abs_bound p hp')
  generalize ht : ({ (s₀.write .t0 (sv2 S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv2 S)).mem ((s₀.write .t0 (sv2 S)).gpr .t0)
      (s₀.write .t0 (sv2 S)).gpr absSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  obtain memt : t.mem = absMem s₀ S := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
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
  obtain ev := eval_zero_ofNat s .a2 hc hd
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
  obtain x2 : s₁.gpr .t2 = BitVec.ofNat 64 (L / 16) := by
    rw [u₁.gpr, h4, shr_ofNat hL]
  obtain ev := eval_zero_ofNat s₁ .t2 (by omega_using [hL]) x2
  by_cases hl : L < 16
  · have e : L / 16 = 0 := by omega_using [hl]
    refine WP.ite true (by rw [ev, e]; rfl) (fun _ => ?_) (fun h => by cases h)
    unfold Impl.AesCbc.RISCV64.mov
    refine wp_mv fun s₂ u₂ => WP.block_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, u₁.other _ (by decide), h4, Nat.min_eq_left (Nat.le_of_lt hl)]
  · have e : L / 16 ≠ 0 := by omega_using [hl]
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
  obtain hh := held_le c
  refine WP.seq (WP.mono (clamp_wp hL h4) fun s₁ ⟨x2₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (wp_li (imm := 16) (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ => wp_sltu fun s₄ u₄ =>
    WP.block_nil ?_)
  obtain x1₁ : s₁.gpr .t1 = BitVec.ofNat 64 (held c) := by rw [g₁ _ (by decide), h1]
  obtain x3₄ : s₄.gpr .t3 = BitVec.ofNat 64 (16 - held c) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), x1₁, Offset.ofNat_sub_ofNat hh]
  obtain x2₄ : s₄.gpr .t2 = BitVec.ofNat 64 (min L 16) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), x2₁]
  obtain x4₄ : s₄.gpr .t4 = BitVec.ofNat 64 (if min L 16 < 16 - held c then 1 else 0) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), x2₁, u₃.gpr, u₂.gpr, u₂.other _ (by decide),
      x1₁, Offset.ofNat_sub_ofNat hh]
    exact sltu_ofNat (by omega_using []) (by omega_using [])
  have g₄ (r : Reg) (a : r ≠ .t3) (b : r ≠ .t4) : s₄.gpr r = s₁.gpr r := by
    rw [u₄.other _ b, u₃.other _ a, u₂.other _ a]
  obtain hf : fOf c L = min (min L 16) (16 - held c) := by unfold fOf; omega_using []
  obtain ev := eval_zero_ofNat s₄ .t4 (k := if min L 16 < 16 - held c then 1 else 0) (by split <;> omega_using []) x4₄
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
  obtain x4₃ : s₃.gpr .s4 = BitVec.ofNat 64 (L - f) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h4, u₁.other _ (by decide), ha7,
      Offset.ofNat_sub_ofNat hf]
  have g₃ (r : Reg) (a : r ≠ .s3) (b : r ≠ .s4) (c : r ≠ .a4) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ c, u₂.other _ b, u₁.other _ a]
  obtain ev := eval_zero_ofNat s₃ .s4 (k := L - f) (by omega_using [hL]) x4₃
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
  obtain ev := eval_zero_ofNat s₁ .s4 hx (by rw [u₁.other _ (by decide), h4])
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
        exact nb16_bv (by omega_using [h0]) hx
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
      exact (shr_ofNat (by split <;> omega_arith)).trans (by congr 1; omega_using [])
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
  obtain e : D + BitVec.ofNat 64 a + BitVec.ofNat 64 (16 * n) = D + BitVec.ofNat 64 (a + 16 * n) :=
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

end

end


/-!
# Streaming AES-CMAC on RISCV64: `vg_cmac_aes_absorb` is correct

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`, `absorbPre_wp`). The second call chains the whole blocks of the
data left but its last 1 to 16 bytes (`nb`), and the last copy holds those
back. If no data is left (`len ≤ 16 - h`), the calls chain nothing and the
copy copies nothing, and the data is appended to the bytes held back
(`repr_fill`); otherwise `repr_chain`. As on PPC64LE (`Proof/CmacAes/Stream/PPC64LE/AbsorbCorrect.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacAes.Stream.RISCV64 VG.WriteBytes
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.AesCbc.RISCV64 (wp_sp)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a3 : s₀.gpr .a3 = D
  a4 : (s₀.gpr .a4).toNat = L
  a5 : s₀.gpr .a5 = S
  a1 : (s₀.gpr .a1).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbRISCV64.pre s₀) :
    APre s₀ (s₀.gpr .a0) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.a4]; exact BitVec.isLt _

theorem APre.a4' : s₀.gpr .a4 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.a4

theorem APre.a1' : s₀.gpr .a1 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.a1

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_using [h])⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_using [h, this])⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (h3 : s.gpr .a0 = St)
    (h4 : s.gpr .a1 = s₀.gpr .a1) (h5 : s.gpr .a2 = St + BitVec.ofNat 64 272) (h6 : s.gpr .a3 = Dd)
    (h7 : s.gpr .a4 = BitVec.ofNat 64 n) (h8 : s.gpr .a5 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { a0 := h3, a2 := h5, a3 := h6, a4 := h7, a5 := h8, rounds := hp.rounds, hn := hn
    a1 := by rw [h4]; exact hp.a1'
    wc := Offset.base_disjoint St (by decide) (by omega_using [])
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_using [hw]
    wrapD := hwrap
    wrapS := by have := hp.wS; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact hcov
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 272, rfl, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

end

/-! ## Up to the first call -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : Addr) (c L : Nat) : Mem :=
  writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 (288 + held c))
    (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L))

/-- What the code before the first call leaves. -/
structure AMid₁ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .a2).toNat L)
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (fOf (s₀.gpr .a2).toNat L)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (leftOf (s₀.gpr .a2).toNat L)
  s6 : s.gpr .s6 = S
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → r ≠ .s6 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (s₀.gpr .a2).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .a2).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  obtain hdx : s₀.gpr .a2 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (save_wp s₀ hp.a5 fun d h => by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega_using [h])⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp hcl (by
    rw [h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hdx]))
    fun s₂ ⟨x1₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x1₂
    (by rw [g₂ _ (by decide), h₁.s4, hp.a4'])
    (by rw [g₂ _ (by decide), h₁.s1, hp.a0]) (by rw [g₂ _ (by decide), h₁.s3, hp.a3]))
    fun s₃ ⟨x2₃, x7₃, x5₃, x6₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  obtain dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ :=
    Offset.sub_base St (by omega_using [hfh])
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega_using [hfh]) x6₃ x5₃ x2₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, h₁.rd, h₁.wr]; exact hp.inD (by omega_using [hfL, hi]))
    (fun i hi => by rw [wr₃, wr₂, h₁.wr, Offset.add_add]; exact hp.inSt (by omega_using [hfh, hi]))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .a7) (b : r ≠ .t1) (c : r ≠ .t2) (d : r ≠ .t3) (e : r ≠ .t4) (f : r ≠ .t5)
      (h : r ≠ .t6) : s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r c d f h, g₃ r a c d e f h, g₂ r b]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s3,
      hp.a3])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x7₃])
    (by rw [g .s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s4,
      hp.a4'])
    (by rw [g .s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s1,
      hp.a0])
    (by rw [g .s6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.s6]))
    fun s₅ h₅ => ?_
  obtain ⟨x3₅, x4₅, xa4₅, xa0₅, xa1₅, xa2₅, xa3₅, xa5₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .s3) (b : r ≠ .s4) : s₅.gpr r = s₁.gpr r := by
    obtain ⟨-, n1, n2, n3, n4, n5, n6, -, -, -, -, -, -, -, -, n7⟩ := preserved_ne r hr
    rw [sv₅ r hr a b, g r n7 n1 n2 n3 n4 n5 n6]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, h₁.rd]
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, h₁.wr]
  obtain hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_using []
  obtain c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hb1])
  obtain m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]
  subst hc
  refine ⟨hp.uargs xa0₅
      (by rw [xa1₅, g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        h₁.s2]) xa2₅ xa3₅
      (by rw [xa4₅, b1Of, leftOf]) xa5₅ hrd hwr (by omega_using [hb1])
      (Offset.disjoint St (by omega_using []) (by omega_using [hb1]) (by omega_using []))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_using [hw, hb1])
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_using [hb1]⟩,
    by rw [k .s1 (by decide) (by decide) (by decide), h₁.s1, hp.a0],
    by rw [k .s2 (by decide) (by decide) (by decide), h₁.s2],
    x3₅, by rw [x4₅]; rfl, by rw [k .s6 (by decide) (by decide) (by decide), h₁.s6],
    fun r hr a b c d e => by
      rw [k r hr c d, h₁.other r (preserved_ne r hr).1 a b c d e],
    m₀, hrd, hwr⟩

/-! ## The whole function -/

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

/-- The slots, within the scratch buffer. -/
theorem slots_sub (S : Addr) : Region.Sub ⟨sv2 S, 56⟩ ⟨S, 2304⟩ := by
  have := sv2_sub S (d := 0) (n := 56) (by decide); rwa [BitVec.add_zero] at this

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp {s₀ : State} (h0 : absorbRISCV64.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ absorbRISCV64.post s₀ s' := by
  obtain hp := APre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a3 = D at hp
  generalize s₀.gpr .a5 = S at hp
  generalize (s₀.gpr .a4).toNat = L at hp
  generalize (s₀.gpr .a1).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .a2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hsum := nb_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (wp_sp (absorbPre_wp hp)) fun s₅ ⟨h₅, sp₅⟩ => ?_)
  obtain ⟨args₅, x1₅, x2₅, x3₅, x4₅, x6₅, o₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x3₅ x4₅ m₅
  refine WP.seq (WP.mono (upd_call args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (wp_sp (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_using [hL])
    (by rw [k₆ .s4 (by decide), x4₅]))) fun s₇ ⟨h₇, sp₇⟩ => ?_)
  obtain ⟨x5₇, xa4₇, xa0₇, xa1₇, xa2₇, xa3₇, xa5₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x5₇ xa4₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .s5) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr]
  obtain dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_using [hsum])
  obtain c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  obtain args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [xa0₇, k₆ .s1 (by decide), x1₅])
    (by rw [xa1₇, k₆ .s2 (by decide), x2₅])
    (by rw [xa2₇, k₆ .s1 (by decide), x1₅])
    (by rw [xa3₇, k₆ .s3 (by decide), x3₅]) xa4₇
    (by rw [xa5₇, k₆ .s6 (by decide), x6₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_using [hL, hsum]) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_using []
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_using [hsum, h0])]; omega_using [hsum, this])
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_using [hsum]⟩
  refine WP.seq (WP.mono (upd_call args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  refine WP.seq (WP.mono (wp_sp (rest_wp (s := s₈) (D := D) (a := fOf c L) (x := leftOf c L) (n := nbOf c L)
    (by unfold leftOf; omega_using [hsum])
    (by rw [k₈ .s3 (by decide), k₇ .s3 (by decide) (by decide), x3₅])
    (by rw [k₈ .s5 (by decide), x5₇])
    (by rw [k₈ .s4 (by decide), k₇ .s4 (by decide) (by decide), x4₅]))) fun s₉ ⟨h₉, sp₉⟩ => ?_)
  obtain ⟨x3₉, x4₉, x5₉, x6₉, x2₉, sv₉, m₉, rd₉, wr₉⟩ := h₉
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  obtain dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_using [hsum])
  obtain hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega_arith
  obtain sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_using [hrr])
  refine WP.seq (WP.mono (wp_sp (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega_using [hrr]) x6₉
    (by rw [x5₉, k₈ .s1 (by decide), k₇ .s1 (by decide) (by decide), x1₅]) x2₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_using [hsum, hi]))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_using [hrr, hi]))
    ((hp.st_d.sub_left sR).symm.sub_left dR))) fun s₁₀ ⟨h₁₀, sp₁₀⟩ => ?_)
  obtain x6₁₀ : s₁₀.gpr .s6 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide), sv₉ _ (by decide) (by decide) (by decide),
      k₈ .s6 (by decide), k₇ .s6 (by decide) (by decide), x6₅]
  -- The frames.
  obtain hlf : (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain fS : Frame [⟨sv2 S, 56⟩] s₀.mem (absMem s₀ S) := absMem_frame _ _
  obtain fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₅.mem s₆.mem := h₆.frame
  obtain f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  obtain fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨sv2 S, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  -- The slots, which only the saves write.
  obtain Fp : Frame K.tail (absMem s₀ S) s₁₀.mem :=
    ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
      ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
  obtain sv₁₀ : Spill.Saved (sv2 S) (absG s₀ S) absSaved s₁₀.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (sv2 S) _).frame Fp fun p hp' r hr => by
      obtain hb := abs_bound p hp'
      obtain sub : Region.Sub ⟨sv2 S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2304⟩ := sv2_sub S (by omega_using [hb])
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact sv2_ws S (by omega_using [hb])
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hrr]))).symm.sub_left sub
  rw [restore, WP.block_append_iff]
  refine WP.mono (savePtr2_ok .s6) fun s₁₁ e => ?_
  subst e
  rw [x6₁₀, show absSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 absSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := absSaved) (B := sv2 S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₁₀) fun s₁₂ r₁₂ => ?_
  · have := abs_bound p hp'
    show InRegions (s₁₀.rd ++ s₁₀.wr) _ 8
    rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉', hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, sv2_contains S (by omega_using [this])⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : absG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · -- The registers, restored from their slots or never written.
    obtain h0 := (preserved_ne r hr).1
    rw [r₁₂.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r ∈ absSaved.map Prod.fst
    · left; exact hv
    · right
      obtain n1 : r ≠ .s1 := fun e => hv (by subst e; decide)
      obtain n2 : r ≠ .s2 := fun e => hv (by subst e; decide)
      obtain n3 : r ≠ .s3 := fun e => hv (by subst e; decide)
      obtain n4 : r ≠ .s4 := fun e => hv (by subst e; decide)
      obtain n5 : r ≠ .s5 := fun e => hv (by subst e; decide)
      obtain n6 : r ≠ .s6 := fun e => hv (by subst e; decide)
      obtain ⟨-, -, t2, t3, -, t5, t6, -⟩ := preserved_ne r hr
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₁₀.other r t2 t3 t5 t6, sv₉ r hr n3 n4, k₈ r hr, k₇ r hr n5,
        o₅ r hr n1 n2 n3 n4 n6, g₀ r h0]
  · rw [r₁₂.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₁₂.sp, RegUpd.sp_write, sp₁₀, sp₉, h₈.sp, sp₇, h₆.sp, sp₅]
  · intro key msg hr hR hcnt hlen
    rw [hp.a0] at hr
    show Spec.Cmac.Repr s₁₂.mem (s₀.gpr .a0) key (msg ++ Spec.Aes.bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat)
    rw [hp.a0, hp.a3, hp.a4, r₁₂.mem, RegUpd.mem_write]
    rw [hp.a4] at hlen
    obtain hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_using [hlen])]
    subst hcm
    obtain hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.a1]; exact hR
    obtain hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_using [h]
    obtain hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    -- The key and the data are in none of the regions written.
    obtain dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (slots_sub S)
      · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hfh])
      · exact Offset.base_disjoint St (by omega_using []) (by omega_using [])
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint St (by omega_using []) (by omega_using [hrr])
    obtain dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.d_s.sub_right (slots_sub S)
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hfh]))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
      · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_using [hrr]))
    obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb]), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_using [hL])]
    obtain fS' : Frame K s₀.mem (absMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    obtain cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hfh]))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (slots_sub S))
          (by decide)]
    obtain cv10 : Spec.Aes.bytesAt s₁₀.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_using []) (by omega_using []) (by omega_using [hrr]))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    obtain hk : ∀ i < 272, s₁₀.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F10 dK (by omega_using [hw]) hi
    obtain hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    obtain hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      obtain e := bytesAt_writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_using [hfh])
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_using [hfh]))).sub_right (slots_sub S))
          (by omega_using [hfh])]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_using [hfL])
      rwa [BitVec.add_zero, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      obtain hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_using [hfL, hx]
      obtain hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      obtain hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      obtain m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega_using [hfh, hfL']) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv10, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        obtain sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega_using [hfh, hfL'])
        obtain dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m108, hdl, bytesAt_frame f8 dj (by omega_using [hfh, hfL']), bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
    · -- The block held back is complete, and more blocks may follow.
      obtain hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega_using [hx]
      obtain hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega_using [hlt]
      obtain hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
        simp only [nbOf, hx, ↓reduceIte]
        unfold leftOf Proof.Cmac.Stream.nblocks
        rw [hf']
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' hh] at hb5'
      refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _)
            ([Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _] ++ _)
        rw [cv10, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, Proof.Cmac.Stream.blocksAt_eq,
          dat _ F6 _ _ (by omega_using [hsum]), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        obtain e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_using [hrr])
        rw [Proof.Cmac.bytesAt_length] at e
        obtain hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_using [hsum]),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.RISCV64
