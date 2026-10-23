module

public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  have := held_le c; unfold fOf; omega

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega

/-! ## Arithmetic on registers -/

/-- The sign of `m - k`, for `m` and `k` of at most 16. -/
theorem lsr63 {m k : Nat} (hm : m ≤ 16) (hk : k ≤ 16) :
    (BitVec.ofNat 64 m - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if m < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- `16 nb` for the data left `x > 0`, as `subi 1; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 1 - ((BitVec.ofNat 64 x - BitVec.ofNat 64 1) &&& BitVec.ofNat 64 15) =
      BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega

/-! ## Saving the registers -/

/-- The memory after saving the registers at `S + 2176`. -/
abbrev absMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem S (saveG s₀) saved

theorem abs_bound : ∀ p ∈ saved, 2176 ≤ p.2 ∧ p.2 + 8 ≤ 2232 := by decide

/-- Saving the registers changes only their slots. -/
theorem absMem_frame (s₀ : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s₀.mem (absMem s₀ S) :=
  Spill.saveMem_frame (lo := 2176) (n := 56) abs_bound (by omega) _ _ _

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
  have ev := eval_zero_ofNat s₁ .r10 (by omega) x10
  by_cases hl : L < 16
  · have e : L / 16 = 0 := by omega
    refine WP.ite true (by rw [ev, e]; rfl) (fun _ => ?_) (fun h => by cases h)
    unfold Impl.AesCbc.PPC64LE.mov
    refine wp_mr fun s₂ u₂ => wp_nil ⟨?_, fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, u₁.other _ (by decide), h17, Nat.min_eq_left (Nat.le_of_lt hl)]
  · have e : L / 16 ≠ 0 := by omega
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
    exact lsr63 (by omega) (by omega)
  have g₅ (r : Reg) (a : r ≠ .r11) (b : r ≠ .r12) : s₅.gpr r = s₁.gpr r := by
    rw [u₅.other _ a, u₄.other _ a, u₃.other _ b, u₂.other _ b]
  have hf : fOf c L = min (min L 16) (16 - held c) := by unfold fOf; omega
  have ev := eval_zero_ofNat s₅ .r11 (k := if min L 16 < 16 - held c then 1 else 0) (by split <;> omega) x11₅
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
  have ev := eval_zero_ofNat s₃ .r17 (k := L - f) (by omega) x17₃
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
        exact nb16_bv (by omega) hx
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
      exact (shr_ofNat (by split <;> omega)).trans (by congr 1; omega)
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
