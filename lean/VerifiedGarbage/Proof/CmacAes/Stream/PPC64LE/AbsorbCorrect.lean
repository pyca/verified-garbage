module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `CmacAes.Stream.PPC64LE.AbsorbBlocks`, which only this module used -/

section

/-!
# Streaming AES-CMAC on PPC64LE: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`), as on AArch64: the bytes held back
`h = held c`, the bytes copied after them `f = min L (16 - h)`, the data left
`L - f`, whether to chain the block held back (`b1`), the blocks chained
after it (`nb`), and the rest (`rest`); and the registers `absorb` saves at
`scratch + 2176`, where the functions it calls do not write.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE
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

/-- The sign of `m - k`, for `m` and `k` of at most 16. -/
theorem lsr63 {m k : Nat} (hm : m ≤ 16) (hk : k ≤ 16) :
    (BitVec.ofNat 64 m - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if m < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega_arith

/-- `16 nb` for the data left `x > 0`, as `subi 1; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 1 - ((BitVec.ofNat 64 x - BitVec.ofNat 64 1) &&& BitVec.ofNat 64 15) =
      BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hx, hx']
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega_using []

/-! ## Saving the registers -/

/-- The memory after saving the registers at `S + 2176`. -/
abbrev absMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem S (saveG s₀) saved

theorem abs_bound : ∀ p ∈ saved, 2176 ≤ p.2 ∧ p.2 + 8 ≤ 2232 := by decide

/-- Saving the registers changes only their slots. -/
theorem absMem_frame (s₀ : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s₀.mem (absMem s₀ S) :=
  Spill.saveMem_frame (lo := 2176) (n := 56) abs_bound (by omega_using []) _ _ _

/-- What `save` leaves. -/
structure Saved₁ (s₀ : State) (S : Addr) (s : State) : Prop where
  r14 : s.gpr .r14 = s₀.gpr .r3
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = s₀.gpr .r6
  r17 : s.gpr .r17 = s₀.gpr .r7
  r19 : s.gpr .r19 = S
  other : ∀ r, r ≠ .r0 → r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → r ≠ .r19 → s.gpr r = s₀.gpr r
  mem : s.mem = absMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem save_wp (s₀ : State) {S : Addr} (hS : s₀.gpr .r8 = S)
    (hw : ∀ d, 2176 ≤ d → d + 8 ≤ 2232 → InRegions s₀.wr (S + BitVec.ofNat 64 d) 8) :
    WP isa (.block save) s₀ (Saved₁ s₀ S) := by
  rw [save, show saved.map (fun (r, d) => Instr.store .d r .r8 d) = Spill.saveCode .r8 saved from rfl]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r8) (l := saved) (by decide) (by decide)
    (fun p hp' => ?_) ?_)
  · have := abs_bound p hp'
    show InRegions s₀.wr (s₀.gpr .r8 + BitVec.ofNat 64 p.2) 8
    rw [hS]; exact hw _ this.1 this.2
  generalize ht : ({ (s₀.write .r0 s₀.lr) with
    mem := (Spill.saveMem (s₀.write .r0 s₀.lr).mem ((s₀.write .r0 s₀.lr).gpr .r8) (s₀.write .r0 s₀.lr).gpr
      saved) } : State) = t
  have gt (r : Reg) (hr : r ≠ .r0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact saveG_ne hr
  have memt : t.mem = absMem s₀ S := by
    have e : (s₀.write .r0 s₀.lr).gpr .r8 = S := by rw [← hS]; exact saveG_ne (by decide)
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [e]; rfl
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, fun r a b c d e f => ?_, ?_, ?_, ?_⟩
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

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .r5 = BitVec.ofNat 64 c) :
    WP isa held s fun s' => s'.gpr .r9 = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ev := eval_zero_ofNat s .r5 hc hd
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => ?_) (fun h => by cases h)
    exact wp_li (by decide) fun s₁ u₁ => wp_nil ⟨by rw [u₁.gpr]; rfl, fun r h _ => u₁.other r h, u₁.mem,
      u₁.rd, u₁.wr⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine wp_subi (by decide) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
      wp_and fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => wp_nil ⟨?_, fun r a b => ?_, ?_, ?_, ?_⟩
    · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, hd, held_bv _ hne, toNat_ofNat hc]
    · rw [u₄.other _ a, u₃.other _ a, u₂.other _ b, u₁.other _ a]
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## `fill`: how many bytes to copy, and where -/

theorem clamp_wp {s : State} {L : Nat} (hL : L < 2 ^ 64) (h17 : s.gpr .r17 = BitVec.ofNat 64 L) :
    WP isa clamp s fun s' => s'.gpr .r10 = BitVec.ofNat 64 (min L 16) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => wp_nil ?_)
  have x10 : s₁.gpr .r10 = BitVec.ofNat 64 (L / 16) := by
    rw [u₁.gpr, h17, shr_ofNat hL]
  have ev := eval_zero_ofNat s₁ .r10 (by omega_using [hL]) x10
  by_cases hl : L < 16
  · have e : L / 16 = 0 := by omega_using [hl]
    refine WP.ite true (by rw [ev, e]; rfl) (fun _ => ?_) (fun h => by cases h)
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_mr fun s₂ u₂ => wp_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, u₁.other _ (by decide), h17, Nat.min_eq_left (Nat.le_of_lt hl)]
  · have e : L / 16 ≠ 0 := by omega_using [hl]
    refine WP.ite false (by rw [ev]; simp [e]) (fun h => by cases h) fun _ => ?_
    refine wp_li (by decide) fun s₂ u₂ => wp_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, Nat.min_eq_right (Nat.le_of_not_lt hl)]

theorem fill_wp {s : State} {St D : Addr} {c L : Nat} (hL : L < 2 ^ 64)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (held c)) (h17 : s.gpr .r17 = BitVec.ofNat 64 L)
    (h14 : s.gpr .r14 = St) (h16 : s.gpr .r16 = D) :
    WP isa fill s fun s' => s'.gpr .r12 = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .r8 = BitVec.ofNat 64 (fOf c L) ∧ s'.gpr .r10 = St + BitVec.ofNat 64 (288 + held c) ∧
      s'.gpr .r11 = D ∧
      (∀ r, r ≠ .r8 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hh := held_le c
  refine WP.seq (WP.mono (clamp_wp hL h17) fun s₁ ⟨x10₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (wp_li (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ => wp_sub fun s₄ u₄ =>
    wp_lsr (by decide) fun s₅ u₅ => wp_nil ?_)
  have x9₁ : s₁.gpr .r9 = BitVec.ofNat 64 (held c) := by rw [g₁ _ (by decide), h9]
  have x12₅ : s₅.gpr .r12 = BitVec.ofNat 64 (16 - held c) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), x9₁,
      Offset.ofNat_sub_ofNat hh]
  have x10₅ : s₅.gpr .r10 = BitVec.ofNat 64 (min L 16) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), x10₁]
  have x11₅ : s₅.gpr .r11 = BitVec.ofNat 64 (if min L 16 < 16 - held c then 1 else 0) := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), x10₁, u₃.gpr, u₂.gpr,
      u₂.other _ (by decide), x9₁, Offset.ofNat_sub_ofNat hh]
    exact lsr63 (by omega_using []) (by omega_using [])
  have g₅ (r : Reg) (a : r ≠ .r11) (b : r ≠ .r12) : s₅.gpr r = s₁.gpr r := by
    rw [u₅.other _ a, u₄.other _ a, u₃.other _ b, u₂.other _ b]
  have hf : fOf c L = min (min L 16) (16 - held c) := by unfold fOf; omega_using []
  have ev := eval_zero_ofNat s₅ .r11 (k := if min L 16 < 16 - held c then 1 else 0) (by split <;> omega_using []) x11₅
  refine WP.seq (WP.mono (Q := fun (s₆ : State) => s₆.gpr .r12 = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .r12 → s₆.gpr r = s₅.gpr r) ∧ s₆.mem = s₅.mem ∧ s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr) ?_
    fun s₆ h₆ => ?_)
  · by_cases hl : min L 16 < 16 - held c
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => ?_
      unfold Impl.AesCbc.PPC64LE.mov
      refine wp_mr fun s₆ u₆ => wp_nil ⟨?_, fun r h => u₆.other r h, u₆.mem, u₆.rd, u₆.wr⟩
      rw [u₆.gpr, x10₅, hf, Nat.min_eq_left (Nat.le_of_lt hl)]
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x12₅, hf, Nat.min_eq_right (Nat.le_of_not_lt hl)], fun _ _ => rfl, rfl, rfl, rfl⟩
  · obtain ⟨x12₆, g₆, m₆, rd₆, wr₆⟩ := h₆
    have g (r : Reg) (a : r ≠ .r12) (b : r ≠ .r11) (d : r ≠ .r10) : s₆.gpr r = s.gpr r := by
      rw [g₆ r a, g₅ r b a, g₁ r d]
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_mr fun s₇ u₇ => wp_add fun s₈ u₈ => wp_addi (by decide) (by decide) fun s₉ u₉ =>
      wp_mr fun s₁₀ u₁₀ => wp_nil ⟨?_, ?_, ?_, ?_, fun r a b d e => ?_, ?_, ?_, ?_⟩
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), x12₆]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, x12₆]
    · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₇.other _ (by decide),
        g .r14 (by decide) (by decide) (by decide), g .r9 (by decide) (by decide) (by decide), h14, h9,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
    · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        g .r16 (by decide) (by decide) (by decide), h16]
    · rw [u₁₀.other _ d, u₉.other _ b, u₈.other _ b, u₇.other _ a, g r e d b]
    · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
    · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h16 : s.gpr .r16 = D) (h8 : s.gpr .r8 = BitVec.ofNat 64 f) (h17 : s.gpr .r17 = BitVec.ofNat 64 L)
    (h14 : s.gpr .r14 = St) (h19 : s.gpr .r19 = S) :
    WP isa chain1 s fun s' => s'.gpr .r16 = D + BitVec.ofNat 64 f ∧ s'.gpr .r17 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .r7 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .r3 = St ∧
      s'.gpr .r4 = s.gpr .r15 ∧ s'.gpr .r5 = St + BitVec.ofNat 64 272 ∧
      s'.gpr .r6 = St + BitVec.ofNat 64 288 ∧ s'.gpr .r8 = S ∧
      (∀ r ∈ preserved, r ≠ .r16 → r ≠ .r17 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => wp_nil ?_)
  have x17₃ : s₃.gpr .r17 = BitVec.ofNat 64 (L - f) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h17, u₁.other _ (by decide), h8,
      Offset.ofNat_sub_ofNat hf]
  have g₃ (r : Reg) (a : r ≠ .r16) (b : r ≠ .r17) (c : r ≠ .r7) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ c, u₂.other _ b, u₁.other _ a]
  have ev := eval_zero_ofNat s₃ .r17 (k := L - f) (by omega_using [hL]) x17₃
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .r7 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .r7 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr) ?_
    fun s₄ h₄ => ?_)
  · by_cases h0 : L - f = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [u₃.gpr]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_li (by decide) fun s₄ u₄ => wp_nil ⟨?_, fun r h => u₄.other r h, u₄.mem, u₄.rd, u₄.wr⟩
      rw [u₄.gpr]; simp [h0]
  · obtain ⟨x7₄, g₄, m₄, rd₄, wr₄⟩ := h₄
    have g (r : Reg) (a : r ≠ .r16) (b : r ≠ .r17) (c : r ≠ .r7) : s₄.gpr r = s.gpr r := by
      rw [g₄ r c, g₃ r a b c]
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_mr fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_addi (by decide) (by decide) fun s₇ u₇ =>
      wp_addi (by decide) (by decide) fun s₈ u₈ => wp_mr fun s₉ u₉ =>
      wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h16, h8]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g₄ _ (by decide), x17₃]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), x7₄]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr, g .r14 (by decide) (by decide) (by decide), h14]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
        u₅.other _ (by decide), g .r15 (by decide) (by decide) (by decide)]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
        u₅.other _ (by decide), g .r14 (by decide) (by decide) (by decide), h14]
    · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g .r14 (by decide) (by decide) (by decide), h14]
    · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), g .r19 (by decide) (by decide) (by decide), h19]
    · obtain ⟨-, n3, n4, n5, n6, n7, n8, -⟩ := preserved_ne r hr
      rw [u₉.other _ n8, u₈.other _ n6, u₇.other _ n5, u₆.other _ n4, u₅.other _ n3, g r a b n7]
    · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄, u₃.mem, u₂.mem, u₁.mem]
    · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr]

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h17 : s.gpr .r17 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .r18 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .r7 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .r3 = s.gpr .r14 ∧
      s'.gpr .r4 = s.gpr .r15 ∧ s'.gpr .r5 = s.gpr .r14 + BitVec.ofNat 64 272 ∧
      s'.gpr .r6 = s.gpr .r16 ∧ s'.gpr .r8 = s.gpr .r19 ∧
      (∀ r ∈ preserved, r ≠ .r18 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_nil ?_)
  have ev := eval_zero_ofNat s₁ .r17 hx (by rw [u₁.other _ (by decide), h17])
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .r18 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .r18 → r ≠ .r9 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [u₁.gpr]; simp [h0], fun _ _ _ => rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_subi (by decide) (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
        wp_and fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_nil ⟨?_, fun r a b => ?_, ?_, ?_, ?_⟩
      · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr,
          u₁.other _ (by decide), h17]
        simp only [h0, ↓reduceIte]
        exact nb16_bv (by omega_using [h0]) hx
      · rw [u₅.other _ a, u₄.other _ b, u₃.other _ b, u₂.other _ a]
      · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
      · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd]
      · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  · obtain ⟨x18₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .r18) (b : r ≠ .r9) : s₂.gpr r = s.gpr r := by rw [g₂ r a b, u₁.other _ a]
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_lsr (by decide) fun s₃ u₃ => wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ =>
      wp_addi (by decide) (by decide) fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_mr fun s₈ u₈ =>
      wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a => ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, x18₂]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, x18₂]
      exact (shr_ofNat (by split <;> omega_arith)).trans (by congr 1; omega_using [])
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g]
    · simp (disch := decide) only [u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g]
    · obtain ⟨-, n3, n4, n5, n6, n7, n8, n9, -⟩ := preserved_ne r hr
      rw [u₈.other _ n8, u₇.other _ n6, u₆.other _ n5, u₅.other _ n4, u₄.other _ n3, u₃.other _ n7, g r a n9]
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]
    · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
    · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## `rest`: the arguments of the last copy -/

theorem rest_wp {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h16 : s.gpr .r16 = D + BitVec.ofNat 64 a) (h18 : s.gpr .r18 = BitVec.ofNat 64 (16 * n))
    (h17 : s.gpr .r17 = BitVec.ofNat 64 x) :
    WP isa (.block rest) s fun s' => s'.gpr .r16 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .r17 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .r10 = s.gpr .r14 + BitVec.ofNat 64 288 ∧
      s'.gpr .r11 = D + BitVec.ofNat 64 (a + 16 * n) ∧ s'.gpr .r12 = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ preserved, r ≠ .r16 → r ≠ .r17 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : D + BitVec.ofNat 64 a + BitVec.ofNat 64 (16 * n) = D + BitVec.ofNat 64 (a + 16 * n) :=
    Offset.add_add _ _ _
  unfold rest Impl.AesCbc.PPC64LE.mov
  refine wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ =>
    wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ => wp_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr, h16, h18, e]
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other, h17, h18]
    exact Offset.ofNat_sub_ofNat hn
  · simp (disch := decide) only [u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other]
  · simp (disch := decide) only [u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.gpr, h16, h18, e]
  · simp (disch := decide) only [u₅.gpr, u₄.other, u₃.other, u₂.gpr, u₁.other, h17, h18]
    exact Offset.ofNat_sub_ofNat hn
  · obtain ⟨-, -, -, -, -, -, -, -, n10, n11, n12⟩ := preserved_ne r hr
    rw [u₅.other _ n12, u₄.other _ n11, u₃.other _ n10, u₂.other _ b, u₁.other _ a]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.CmacAes.Stream.PPC64LE

end

end


/-!
# Streaming AES-CMAC on PPC64LE: `vg_cmac_aes_absorb` is correct

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 16 - h)` bytes after them, and sets up the first call of
`vg_cmac_aes_update`, which chains the block held back if data is left
(`AMid₁`, `absorbPre_wp`). The second call chains the whole blocks of the
data left but its last 1 to 16 bytes (`nb`), and the last copy holds those
back. If no data is left (`len ≤ 16 - h`), the calls chain nothing and the
copy copies nothing, and the data is appended to the bytes held back
(`repr_fill`); otherwise `repr_chain`. As on AArch64.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.Stream.PPC64LE VG.WriteBytes
open VG.Proof.Cmac (bytesAt_frame)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`,
the scratch buffer `S` and the rounds `R`. -/
structure APre (s₀ : State) (St D S : Addr) (L R : Nat) : Prop where
  r3 : s₀.gpr .r3 = St
  r6 : s₀.gpr .r6 = D
  r7 : (s₀.gpr .r7).toNat = L
  r8 : s₀.gpr .r8 = S
  r4 : (s₀.gpr .r4).toNat = R
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 304⟩, ⟨S, 2304⟩]
  st_d : (⟨St, 304⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem APre.of {s₀ : State} (h : absorbPPC64LE.pre s₀) :
    APre s₀ (s₀.gpr .r3) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

section
variable {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
include hp

theorem APre.lt : L < 2 ^ 64 := by rw [← hp.r7]; exact BitVec.isLt _

theorem APre.r7' : s₀.gpr .r7 = BitVec.ofNat 64 L := ofNat_toNat_eq hp.r7

theorem APre.r4' : s₀.gpr .r4 = BitVec.ofNat 64 R := ofNat_toNat_eq hp.r4

theorem APre.inSt {d n : Nat} (h : d + n ≤ 304) : InRegions s₀.wr (St + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ h (by have := hp.wSt; omega_arith)⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ h (by have := hp.wS; omega_arith)⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (D + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact ⟨⟨D, L⟩, by simp, Offset.contains_base _ h (by have := hp.lt; omega_arith)⟩

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the permissions of `s₀`. -/
theorem APre.uargs {s : State} {Dd : Addr} {n : Nat} (h3 : s.gpr .r3 = St)
    (h4 : s.gpr .r4 = s₀.gpr .r4) (h5 : s.gpr .r5 = St + BitVec.ofNat 64 272) (h6 : s.gpr .r6 = Dd)
    (h7 : s.gpr .r7 = BitVec.ofNat 64 n) (h8 : s.gpr .r8 = S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 64)
    (hdc : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd, 16 * n⟩ : Region).Disjoint ⟨S, 2176⟩) (hwrap : Dd.toNat + 16 * n ≤ 2 ^ 64)
    (hcov : ∃ r' ∈ ([⟨D, L⟩, ⟨St, 304⟩, ⟨S, 2304⟩] : List Region), ∃ off, Dd = r'.base + BitVec.ofNat 64 off ∧
      off + 16 * n ≤ r'.len) :
    UArgs s St (St + BitVec.ofNat 64 272) Dd S R n := by
  have hw := hp.wSt
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  exact
  { r3 := h3, r5 := h5, r6 := h6, r7 := h7, r8 := h8, rounds := hp.rounds, hn := hn
    r4 := by rw [h4]; exact hp.r4'
    wc := Offset.base_disjoint St (by decide) (by omega_arith)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := hdc, ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    wrapC := by rw [toNat_add_lt St hw (by decide)]; omega_arith
    wrapD := hwrap
    wrapS := by have := hp.wS; omega_arith
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
  args : UArgs s St (St + BitVec.ofNat 64 272) (St + BitVec.ofNat 64 288) S R (b1Of (s₀.gpr .r5).toNat L)
  r14 : s.gpr .r14 = St
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = D + BitVec.ofNat 64 (fOf (s₀.gpr .r5).toNat L)
  r17 : s.gpr .r17 = BitVec.ofNat 64 (leftOf (s₀.gpr .r5).toNat L)
  r19 : s.gpr .r19 = S
  other : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r17 → r ≠ .r19 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (s₀.gpr .r5).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L R) := by
  generalize hc : (s₀.gpr .r5).toNat = c
  have hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hdx : s₀.gpr .r5 = BitVec.ofNat 64 c := ofNat_toNat_eq hc
  have hL := hp.lt
  have hw := hp.wSt
  have ⟨hfL, hfh⟩ := f_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (save_wp s₀ hp.r8 fun d _ h => hp.inS (by omega_arith)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp hcl (by
    rw [h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hdx]))
    fun s₂ ⟨x9₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (D := D) hL x9₂
    (by rw [g₂ _ (by decide) (by decide), h₁.r17, hp.r7'])
    (by rw [g₂ _ (by decide) (by decide), h₁.r14, hp.r3]) (by rw [g₂ _ (by decide) (by decide), h₁.r16, hp.r6]))
    fun s₃ ⟨x12₃, x8₃, x10₃, x11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have dCp : Region.Sub ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩ ⟨St, 304⟩ :=
    Offset.sub_base St (by omega_arith)
  refine WP.seq (WP.mono (copy_ok s₃ (P := D) (C := St + BitVec.ofNat 64 (288 + held c)) (L := fOf c L)
    (by omega_arith) x11₃ x10₃ x12₃
    (fun i hi => by rw [rd₃, wr₃, rd₂, wr₂, h₁.rd, h₁.wr]; exact hp.inD (by omega_arith))
    (fun i hi => by rw [wr₃, wr₂, h₁.wr, Offset.add_add]; exact hp.inSt (by omega_arith))
    ((hp.st_d.sub_left dCp).symm.sub_left (Region.sub_prefix hfL))) fun s₄ h₄ => ?_)
  -- The registers `chain1` reads, unchanged since `save`.
  have g (r : Reg) (a : r ≠ .r8) (b : r ≠ .r9) (c : r ≠ .r10) (d : r ≠ .r11) (e : r ≠ .r12) :
      s₄.gpr r = s₁.gpr r := by
    rw [h₄.other r b c d e, g₃ r a c d e, g₂ r b c]
  refine WP.mono (chain1_wp (St := St) (S := S) hfL hL
    (by rw [g .r16 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r16, hp.r6])
    (by rw [h₄.other _ (by decide) (by decide) (by decide) (by decide), x8₃])
    (by rw [g .r17 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r17, hp.r7'])
    (by rw [g .r14 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r14, hp.r3])
    (by rw [g .r19 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r19]))
    fun s₅ h₅ => ?_
  obtain ⟨x16₅, x17₅, x7₅, x3₅, x4₅, x5₅, x6₅, x8₅, sv₅, m₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (hr : r ∈ preserved) (a : r ≠ .r16) (b : r ≠ .r17) : s₅.gpr r = s₁.gpr r := by
    obtain ⟨-, -, -, -, -, -, n8, n9, n10, n11, n12⟩ := preserved_ne r hr
    rw [sv₅ r hr a b, g r n8 n9 n10 n11 n12]
  have hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃, rd₂, h₁.rd]
  have hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃, wr₂, h₁.wr]
  have hb1 : 16 * b1Of c L ≤ 16 := by unfold b1Of; split <;> omega_arith
  have c288 : Region.Sub ⟨St + BitVec.ofNat 64 288, 16 * b1Of c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  have m₀ : s₅.mem = m4 s₀ St D S c L := by rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]
  subst hc
  refine ⟨hp.uargs x3₅
      (by rw [x4₅, g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r15]) x5₅ x6₅
      (by rw [x7₅, b1Of, leftOf]) x8₅ hrd hwr (by omega_arith)
      (Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide)))
      (by rw [toNat_add_lt St hw (by decide)]; omega_arith)
      ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega_arith⟩,
    by rw [k .r14 (by decide) (by decide) (by decide), h₁.r14, hp.r3],
    by rw [k .r15 (by decide) (by decide) (by decide), h₁.r15],
    x16₅, by rw [x17₅]; rfl, by rw [k .r19 (by decide) (by decide) (by decide), h₁.r19],
    fun r hr a b c d e => by
      rw [k r hr c d, h₁.other r (preserved_ne r hr).1 a b c d e],
    m₀, hrd, hwr⟩

/-! ## The whole function -/

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_arith) (by omega_arith)) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt]

theorem absorb_wp {s₀ : State} (h0 : absorbPPC64LE.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      absorbPPC64LE.post s₀ s' := by
  have hp := APre.of h0
  generalize s₀.gpr .r3 = St at hp
  generalize s₀.gpr .r6 = D at hp
  generalize s₀.gpr .r8 = S at hp
  generalize (s₀.gpr .r7).toNat = L at hp
  generalize (s₀.gpr .r4).toNat = R at hp
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .r5).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have hw := hp.wSt
  have hsw := hp.wS
  have ⟨hfL, hfh⟩ := f_le c L
  have hsum := nb_le c L
  have hh := held_le c
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  obtain ⟨args₅, x14₅, x15₅, x16₅, x17₅, x19₅, o₅, m₅, rd₅, wr₅⟩ := h₅
  rw [hc] at args₅ x16₅ x17₅ m₅
  refine WP.seq (WP.mono (upd_call args₅) fun s₆ h₆ => ?_)
  have k₆ (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s₅.gpr r := h₆.saved r hr
  refine WP.seq (WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega_arith)
    (by rw [k₆ .r17 (by decide), x17₅])) fun s₇ h₇ => ?_)
  obtain ⟨x18₇, x7₇, x3₇, x4₇, x5₇, x6₇, x8₇, sv₇, m₇, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x18₇ x7₇
  have k₇ (r : Reg) (hr : r ∈ preserved) (a : r ≠ .r18) : s₇.gpr r = s₅.gpr r := by
    rw [sv₇ r hr a, k₆ r hr]
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L), 16 * nbOf c L⟩ ⟨D, L⟩ := Offset.sub_base D (by omega_arith)
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  have args₇ := hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf c L)) (n := nbOf c L)
    (by rw [x3₇, k₆ .r14 (by decide), x14₅])
    (by rw [x4₇, k₆ .r15 (by decide), x15₅])
    (by rw [x5₇, k₆ .r14 (by decide), x14₅])
    (by rw [x6₇, k₆ .r16 (by decide), x16₅]) x7₇
    (by rw [x8₇, k₆ .r19 (by decide), x19₅]) (by rw [rd₇, h₆.rd, rd₅])
    (by rw [wr₇, h₆.wr, wr₅]) (by omega_arith) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf c L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf c L)).isLt; omega_arith
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega_arith)]; omega_arith)
    ⟨⟨D, L⟩, by simp, fOf c L, rfl, by simp; omega_arith⟩
  refine WP.seq (WP.mono (upd_call args₇) fun s₈ h₈ => ?_)
  have k₈ (r : Reg) (hr : r ∈ preserved) : s₈.gpr r = s₇.gpr r := h₈.saved r hr
  refine WP.seq (WP.mono (rest_wp (s := s₈) (D := D) (a := fOf c L) (x := leftOf c L) (n := nbOf c L)
    (by unfold leftOf; omega_arith)
    (by rw [k₈ .r16 (by decide), k₇ .r16 (by decide) (by decide), x16₅])
    (by rw [k₈ .r18 (by decide), x18₇])
    (by rw [k₈ .r17 (by decide), k₇ .r17 (by decide) (by decide), x17₅])) fun s₉ h₉ => ?_)
  obtain ⟨x16₉, x17₉, x10₉, x11₉, x12₉, sv₉, m₉, rd₉, wr₉⟩ := h₉
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, h₈.rd, rd₇, h₆.rd, rd₅]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, h₈.wr, wr₇, h₆.wr, wr₅]
  have dR : Region.Sub ⟨D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L), restOf c L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega_arith)
  have hrr : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega_arith
  have sR : Region.Sub ⟨St + BitVec.ofNat 64 288, restOf c L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega_arith)
  refine WP.seq (WP.mono (copy_ok s₉ (P := D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L))
    (C := St + BitVec.ofNat 64 288) (L := restOf c L) (by omega_arith) x11₉
    (by rw [x10₉, k₈ .r14 (by decide), k₇ .r14 (by decide) (by decide), x14₅]) x12₉
    (fun i hi => by rw [rd₉', wr₉', Offset.add_add]; exact hp.inD (by omega_arith))
    (fun i hi => by rw [wr₉', Offset.add_add]; exact hp.inSt (by omega_arith))
    ((hp.st_d.sub_left sR).symm.sub_left dR)) fun s₁₀ h₁₀ => ?_)
  have x19₁₀ : s₁₀.gpr .r19 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide), sv₉ _ (by decide) (by decide) (by decide),
      k₈ .r19 (by decide), k₇ .r19 (by decide) (by decide), x19₅]
  -- The frames.
  have hlf : (Spec.Aes.bytesAt (absMem s₀ S) D (fOf c L)).length = fOf c L := Proof.Cmac.bytesAt_length _ _ _
  have hlr : (Spec.Aes.bytesAt s₉.mem (D + BitVec.ofNat 64 (fOf c L + 16 * nbOf c L)) (restOf c L)).length =
    restOf c L := Proof.Cmac.bytesAt_length _ _ _
  have fS : Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s₀.mem (absMem s₀ S) := absMem_frame _ _
  have fC1 : Frame [⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩] (absMem s₀ S) s₅.mem := by
    rw [m₅, m4]; exact writeBytes_frame _ _ _ (by rw [hlf]; exact Region.contains_self _ _)
  have f6 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₅.mem s₆.mem := h₆.frame
  have f8 : Frame [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩] s₆.mem s₈.mem := by
    rw [← m₇]; exact h₈.frame
  have fC2 : Frame [⟨St + BitVec.ofNat 64 288, restOf c L⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    exact writeBytes_frame _ _ _ (by rw [← m₉, hlr]; exact Region.contains_self _ _)
  let K : List Region := [⟨S + BitVec.ofNat 64 2176, 56⟩, ⟨St + BitVec.ofNat 64 (288 + held c), fOf c L⟩,
    ⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩, ⟨St + BitVec.ofNat 64 288, restOf c L⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  -- The slots, which only the saves write.
  have Fp : Frame K.tail (absMem s₀ S) s₁₀.mem :=
    ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
      ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
  have sv₁₀ : Spill.Saved S (saveG s₀) saved s₁₀.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem S _).frame Fp fun p hp' r hr => by
      have hb := abs_bound p hp'
      have sub : Region.Sub ⟨S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2304⟩ := Offset.sub_base S (by omega_arith)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).symm.sub_left sub
      · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base S (by omega_arith) (by omega_arith)
      · exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).symm.sub_left sub
  rw [restore, show saved.map (fun (r, d) => Instr.load .d r .r19 d) = Spill.restoreCode .r19 saved from rfl]
  refine Spill.restore_ok (b := .r19) (l := saved) (by decide) x19₁₀ (by decide) (by decide)
    (fun p hp' => ?_) sv₁₀ fun s₁₁ r₁₁ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := abs_bound p hp'
    rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']; exact in_wr (hp.inS (by omega_arith))
  · -- The registers, restored from their slots or never written.
    show s₁₁.gpr r = _
    rw [r₁₁.gpr_of (r := r) ?_, saveG_ne (preserved_ne r hr).1]
    by_cases hv : r ∈ saved.map Prod.fst
    · left; exact hv
    · right
      have n14 : r ≠ .r14 := fun e => hv (by subst e; decide)
      have n15 : r ≠ .r15 := fun e => hv (by subst e; decide)
      have n16 : r ≠ .r16 := fun e => hv (by subst e; decide)
      have n17 : r ≠ .r17 := fun e => hv (by subst e; decide)
      have n18 : r ≠ .r18 := fun e => hv (by subst e; decide)
      have n19 : r ≠ .r19 := fun e => hv (by subst e; decide)
      obtain ⟨h0, -, -, -, -, -, -, n9, n10, n11, n12⟩ := preserved_ne r hr
      rw [h₁₀.other r n9 n10 n11 n12, sv₉ r hr n16 n17, k₈ r hr, k₇ r hr n18, o₅ r hr n14 n15 n16 n17 n19,
        saveG_ne h0]
  · show s₁₁.gpr .r0 = _
    rw [r₁₁.gpr (.r0, 2176) (by decide)]; exact saveG_r0 s₀
  · intro key msg hr hR hcnt hlen
    rw [hp.r3] at hr
    show Spec.Cmac.Repr s₁₁.mem (s₀.gpr .r3) key (msg ++ Spec.Aes.bytesAt s₀.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat)
    rw [hp.r3, hp.r6, hp.r7, r₁₁.mem]
    rw [hp.r7] at hlen
    have hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat (by omega_arith)]
    subst hcm
    have hRk : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.r4]; exact hR
    have hRb : 16 * (R + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_arith
    have hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    rw [← hRk] at hsch
    -- The key and the data are in none of the regions written.
    have dK : ∀ r ∈ K, (⟨St, 272⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
      · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
      · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint St (by omega_arith) (by omega_arith)
    have dDat : ∀ r ∈ K, (⟨D, L⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.d_s.sub_right (Offset.sub_base S (by decide))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_arith))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by decide))
      · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
      · exact hp.st_d.symm.sub_right (Offset.sub_base St (by omega_arith))
    have ciph : ∀ m : Mem, Frame K s₀.mem m →
        Spec.Cmac.aesWith R (Spec.Aes.bytesAt m St (16 * (R + 1))) = Spec.Cmac.aes key := fun m hf => by
      rw [bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_arith), hsch,
        Spec.Cmac.aes, ← hRk]
    -- The data, wherever it is read.
    have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem D L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m D hab, bytesAt_frame hf dDat (by omega_arith)]
    have fS' : Frame K s₀.mem (absMem s₀ S) := fS.mono (by simp [K])
    -- The chaining value.
    have cv5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 272) 16 := by
      rw [bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
          (by decide),
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base S (by decide)))
          (by decide)]
    have cv10 : Spec.Aes.bytesAt s₁₀.mem (St + BitVec.ofNat 64 272) 16 =
        Spec.Aes.bytesAt s₈.mem (St + BitVec.ofNat 64 272) 16 :=
      bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide)
    have out6 := h₆.out
    rw [ciph _ F5] at out6
    have out8 := h₈.out
    rw [m₇, ciph _ F6] at out8
    have hk : ∀ i < 272, s₁₀.mem (St + BitVec.ofNat 64 i) = s₀.mem (St + BitVec.ofNat 64 i) :=
      fun i hi => frame_at F10 dK (by omega_arith) hi
    have hdl : (Spec.Aes.bytesAt s₀.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    have hb5 : Spec.Aes.bytesAt s₅.mem (St + BitVec.ofNat 64 288) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 288) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem D L).take (fOf msg.length L) := by
      have e := bytesAt_writeBytes (absMem s₀ S) (St + BitVec.ofNat 64 288) (held msg.length)
        (Spec.Aes.bytesAt (absMem s₀ S) D (fOf msg.length L)) (by rw [hlf]; omega_arith)
      rw [hlf] at e
      rw [m₅, m4, ← Offset.add_add, e,
        bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.st_s.sub_left (Offset.sub_base St (by omega_arith))).sub_right (Offset.sub_base S (by decide)))
          (by omega_arith)]
      refine congrArg (_ ++ ·) ?_
      have := dat _ fS' 0 (fOf msg.length L) (by omega_arith)
      rwa [BitVec.add_zero, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem D L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      have hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_arith
      have hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = 0 := by simp [nbOf, hx]
      have hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      have m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem
          (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L)) 0 = [] from rfl, writeBytes_nil]
      refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl]; have := (f_le msg.length L).2; omega_arith) ?_ ?_
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 272) _
        rw [cv10, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ ++ _
        have sub : Region.Sub ⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ ⟨St, 304⟩ :=
          Offset.sub_base St (by omega_arith)
        have dj : ∀ r ∈ [⟨St + BitVec.ofNat 64 272, 16⟩, ⟨S, 2176⟩],
            (⟨St + BitVec.ofNat 64 288, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint St (by omega_arith) (by omega_arith) (by omega_arith)
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m108, hdl, bytesAt_frame f8 dj (by omega_arith), bytesAt_frame f6 dj (by omega_arith), hb5']
    · -- The block held back is complete, and more blocks may follow.
      have hlt : 16 - held msg.length < L := by unfold leftOf fOf at hx; omega_arith
      have hf' : fOf msg.length L = 16 - held msg.length := by unfold fOf; omega_arith
      have hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      have hn : nbOf msg.length L = Proof.Cmac.Stream.nblocks msg.length L := by
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
          dat _ F6 _ _ (by omega_arith), hb5', hdl, hf', hn]
      · show Spec.Aes.bytesAt _ (St + BitVec.ofNat 64 288) _ = _
        have e := bytesAt_writeBytes_self s₈.mem (St + BitVec.ofNat 64 288)
          (xs := Spec.Aes.bytesAt s₈.mem (D + BitVec.ofNat 64 (fOf msg.length L + 16 * nbOf msg.length L))
            (restOf msg.length L)) (by rw [Proof.Cmac.bytesAt_length]; omega_arith)
        rw [Proof.Cmac.bytesAt_length] at e
        have hr' : d.length - (16 - held msg.length) - 16 * Proof.Cmac.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        rw [hr', h₁₀.mem, m₉, e, dat _ F8 _ _ (by omega_arith),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_arith),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacAes.Stream.PPC64LE
