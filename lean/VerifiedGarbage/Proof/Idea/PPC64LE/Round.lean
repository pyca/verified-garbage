module

public import VerifiedGarbage.Proof.Idea.PPC64LE.Mul
import VerifiedGarbage.Proof.Idea.Arith

/-!
# IDEA on PPC64LE: a round

`round_ok`: round `j` of the code (`Impl.Idea.PPC64LE.round j`) maps the
state words in `r6`–`r9` (`Holds`) to `Spec.Idea.round` of them under
subkeys `6j … 6j + 5`, read from the schedule at `r3` (`KeyOk`). It is
composed of its pieces: ⊙ and ⊞ with a subkey (`mulKey_ok`, `addKey_ok`),
and the multiplication–addition structure.
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp

theorem read_four (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_eight (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

/-- Steps a block of the IDEA code, keeping 32-bit loads and 64-bit stores as
`Mem.readW` and `Mem.writeW`, and byte loads as the byte. -/
syntax "irun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| irun) => `(tactic| irun [])
  | `(tactic| irun [$ls,*]) => `(tactic|
      crun [List.cons_append, List.nil_append, ↓read_one, ↓read_four, write_eight, false_implies,
        $ls,*])

/-- The state words are in `r6`–`r9`, zero-extended. -/
structure Holds (x : Spec.Idea.State) (s : State) : Prop where
  r6 : s.gpr .r6 = (x.getD 0 0).setWidth 64
  r7 : s.gpr .r7 = (x.getD 1 0).setWidth 64
  r8 : s.gpr .r8 = (x.getD 2 0).setWidth 64
  r9 : s.gpr .r9 = (x.getD 3 0).setWidth 64

/-- Subkey `k` of `z` (`k ≤ 50`) is the low 16 bits of the word at
`r3 + 2k`, which can be loaded, and subkey 51 the high 16 bits of the word
at `r3 + 100`; and `r0` holds the mask. -/
structure KeyOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  low : ∀ k ≤ 50, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (2 * k)) 4 ∧
    (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (2 * k)) 32).setWidth 16 = z.getD k 0
  last : ((s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 100) 32) >>> 16).setWidth 16 = z.getD 51 0
  mask : s.gpr .r0 = 65535

theorem KeyOk.keep {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : KeyOk z s)
    (hk : Keep rs s s') (hm : s'.mem = s.mem) (h3 : .r3 ∉ rs) (h0 : .r0 ∉ rs) : KeyOk z s' := by
  refine ⟨fun k hk' => ?_, ?_, ?_⟩
  · rw [hk.gpr h3, hk.2.1, hk.2.2, hm]
    exact h.low k hk'
  · rw [hk.gpr h3, hm]
    exact h.last
  · rw [hk.gpr h0]
    exact h.mask

theorem lo16 (x : BitVec 32) : (x.setWidth 64).setWidth 16 = x.setWidth 16 :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

/-- `writesOnly` of a block, by evaluation with the destination registers
of its instructions as variables. -/
macro "writes_only" : term => `(by simp [writesOnly, Code.allInstrs_eq, instrs, mulKey, addKey,
  mulCode, mov, dstOf])

/-- `r := r ⊙ [r3 + d]`. -/
theorem mulKey_ok (r : Reg) (d : Nat) (hd : d < 2 ^ 15) (s : State)
    (h0 : s.gpr .r0 = 65535) (hk : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 d) 4) :
    WP isa (.block (mulKey r d)) s fun t =>
      t.gpr r = (Spec.Idea.mul ((s.gpr r).setWidth 16)
        ((s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 d) 32).setWidth 16)).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.r11, .r12, r] s t := by
  refine WP.mono (WP.keep (c := .block (mulKey r d)) [.r11, .r12, r] (Q := fun t =>
      t.gpr r = (Spec.Idea.mul ((s.gpr r).setWidth 16)
        ((s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 d) 32).setWidth 16)).setWidth 64 ∧
      t.mem = s.mem) ?_ writes_only rfl) fun t ⟨⟨h1, h2⟩, hk⟩ => ⟨h1, h2, hk⟩
  simp only [mulKey, List.append_assoc]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [mov .r11 r, .load .w .r12 .r3 d]) s fun u =>
      u.gpr .r11 = s.gpr r ∧
      u.gpr .r12 = (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 d) 32).setWidth 64 ∧
      u.gpr .r0 = 65535 ∧ u.mem = s.mem := by
    unfold mov
    irun [hk, hd, h0, BitVec.or_self]
  refine WP.mono h1 fun u ⟨u11, u12, u0, um⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_ok u u0) fun v ⟨v12, vm⟩ => ?_
  unfold mov
  irun [v12, vm, um, u11, u12, BitVec.or_self, lo16]

/-- `r := r ⊞ [r3 + d]`, zero-extended. -/
theorem addKey_ok {r : Reg} (hr : r ≠ .r12 ∧ r ≠ .r0) (d : Nat) (hd : d < 2 ^ 15) (s : State)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 64) (h0 : s.gpr .r0 = 65535)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 d) 4) :
    WP isa (.block (addKey r d)) s fun t =>
      t.gpr r = (x + (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 d) 32).setWidth 16).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.r12, r] s t := by
  refine WP.mono (WP.keep (c := .block (addKey r d)) [.r12, r] (Q := fun t =>
      t.gpr r = (x + (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 d) 32).setWidth 16).setWidth 64 ∧
      t.mem = s.mem) ?_ writes_only rfl) fun t ⟨⟨h1, h2⟩, hk⟩ => ⟨h1, h2, hk⟩
  unfold addKey
  irun [hk, hd, h0, hx, hr.1, hr.2, Ne.symm hr.2]
  exact (add_mask x _).trans (by rw [lo16])

/-- The registers a round writes. -/
abbrev roundWrites : List Reg := [.r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem keep_weaken {rs : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : (rs.all fun r => roundWrites.contains r) = true) : Keep roundWrites s s' :=
  h.mono fun r hr => by
    have := List.all_eq_true.mp hs r hr
    simpa using this

/-- Subkey `6j + i` of a round, at its offset. -/
theorem key_at {z : Spec.Idea.Schedule} {s : State} (hk : KeyOk z s) (j i : Nat) (h : 6 * j + i ≤ 50) :
    InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (12 * j + 2 * i)) 4 ∧
      (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (12 * j + 2 * i)) 32).setWidth 16 = z.getD (6 * j + i) 0 := by
  have := hk.low (6 * j + i) h
  rwa [show 2 * (6 * j + i) = 12 * j + 2 * i by omega] at this

theorem mul_keep (s : State) (h0 : s.gpr .r0 = 65535) :
    WP isa (.block mulCode) s fun t =>
      t.gpr .r12 = (Spec.Idea.mul ((s.gpr .r11).setWidth 16) ((s.gpr .r12).setWidth 16)).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.r11, .r12] s t :=
  WP.mono (WP.keep [.r11, .r12] (mul_ok s h0) (by decide)) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

theorem p6_ok (s : State) (d : Nat) (hd : d < 2 ^ 15)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 d) 4) :
    WP isa (.block [mov .r10 .r12, .logic .xor .r11 .r7 .r9, .add .r11 .r11 .r10,
        .load .w .r12 .r3 d]) s fun t =>
      t.gpr .r10 = s.gpr .r12 ∧ t.gpr .r11 = (s.gpr .r7 ^^^ s.gpr .r9) + s.gpr .r12 ∧
      t.gpr .r12 = (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 d) 32).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.r10, .r11, .r12] s t := by
  refine WP.mono (WP.keep (c := .block [mov .r10 .r12, .logic .xor .r11 .r7 .r9,
      .add .r11 .r11 .r10, .load .w .r12 .r3 d]) [.r10, .r11, .r12] (Q := fun t =>
      t.gpr .r10 = s.gpr .r12 ∧ t.gpr .r11 = (s.gpr .r7 ^^^ s.gpr .r9) + s.gpr .r12 ∧
      t.gpr .r12 = (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 d) 32).setWidth 64 ∧
      t.mem = s.mem) ?_ writes_only rfl) fun t ⟨⟨a, b, c, d⟩, e⟩ => ⟨a, b, c, d, e⟩
  unfold mov
  irun [hk, hd, BitVec.or_self]

theorem p7_ok (s : State) (h0 : s.gpr .r0 = 65535) :
    WP isa (.block [.add .r10 .r10 .r12, .logic .and .r10 .r10 .r0,
        .logic .xor .r6 .r6 .r12, .logic .xor .r8 .r8 .r12,
        .logic .xor .r7 .r7 .r10, .logic .xor .r9 .r9 .r10,
        mov .r11 .r7, mov .r7 .r8, mov .r8 .r11]) s fun t =>
      t.gpr .r6 = s.gpr .r6 ^^^ s.gpr .r12 ∧
      t.gpr .r7 = s.gpr .r8 ^^^ s.gpr .r12 ∧
      t.gpr .r8 = s.gpr .r7 ^^^ ((s.gpr .r10 + s.gpr .r12) &&& 65535) ∧
      t.gpr .r9 = s.gpr .r9 ^^^ ((s.gpr .r10 + s.gpr .r12) &&& 65535) ∧
      t.mem = s.mem ∧ Keep roundWrites s t := by
  refine WP.mono (WP.keep [.r6, .r7, .r8, .r9, .r10, .r11, .r12] (Q := fun t =>
      t.gpr .r6 = s.gpr .r6 ^^^ s.gpr .r12 ∧
      t.gpr .r7 = s.gpr .r8 ^^^ s.gpr .r12 ∧
      t.gpr .r8 = s.gpr .r7 ^^^ ((s.gpr .r10 + s.gpr .r12) &&& 65535) ∧
      t.gpr .r9 = s.gpr .r9 ^^^ ((s.gpr .r10 + s.gpr .r12) &&& 65535) ∧
      t.mem = s.mem) ?_ (by decide) rfl) fun t ⟨⟨a, b, c, d, e⟩, f⟩ => ⟨a, b, c, d, e, f⟩
  unfold mov
  irun [h0, BitVec.or_self]

theorem round_ok (j : Nat) (hj : j < 8) (z : Spec.Idea.Schedule) (x : Spec.Idea.State)
    (s : State) (hx : Holds x s) (hk : KeyOk z s) :
    WP isa (.block (round j)) s fun t =>
      Holds (Spec.Idea.round (z.getD (6 * j) 0) (z.getD (6 * j + 1) 0) (z.getD (6 * j + 2) 0)
        (z.getD (6 * j + 3) 0) (z.getD (6 * j + 4) 0) (z.getD (6 * j + 5) 0) x) t ∧
      t.mem = s.mem ∧ Keep roundWrites s t := by
  simp only [round, List.append_assoc]
  have k0 := key_at hk j 0 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at k0
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok .r6 (12 * j) (by omega) s hk.mask k0.1) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [hx.r6, setWidth_setWidth16, k0.2] at v₁
  have hk₁ := hk.keep e₁ m₁ (by decide) (by decide)
  have k3 := key_at hk₁ j 3 (by omega)
  simp only [Nat.reduceMul] at k3
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok .r9 (12 * j + 6) (by omega) s₁ hk₁.mask k3.1) fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [e₁.gpr (by decide), hx.r9, setWidth_setWidth16, k3.2] at v₂
  have hk₂ := hk₁.keep e₂ m₂ (by decide) (by decide)
  have k1 := key_at hk₂ j 1 (by omega)
  simp only [Nat.mul_one] at k1
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok (r := .r7) (by decide) (12 * j + 2) (by omega) s₂ (x.getD 1 0)
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.r7)) hk₂.mask k1.1)
    fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  rw [k1.2] at v₃
  have hk₃ := hk₂.keep e₃ m₃ (by decide) (by decide)
  have k2 := key_at hk₃ j 2 (by omega)
  simp only [Nat.reduceMul] at k2
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok (r := .r8) (by decide) (12 * j + 4) (by omega) s₃ (x.getD 2 0)
    ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.r8)))
    hk₃.mask k2.1) fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  rw [k2.2] at v₄
  have hk₄ := hk₃.keep e₄ m₄ (by decide) (by decide)
  have k4 := key_at hk₄ j 4 (by omega)
  have k5 := key_at hk₄ j 5 (by omega)
  simp only [Nat.reduceMul] at k4 k5
  -- The words through the pieces.
  have r6₄ : s₄.gpr .r6 = (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0)).setWidth 64 :=
    (e₄.gpr (by decide)).trans ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans v₁))
  have r9₄ : s₄.gpr .r9 = (Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)).setWidth 64 :=
    (e₄.gpr (by decide)).trans ((e₃.gpr (by decide)).trans v₂)
  have r7₄ : s₄.gpr .r7 = (x.getD 1 0 + z.getD (6 * j + 1) 0).setWidth 64 :=
    (e₄.gpr (by decide)).trans v₃
  have r8₄ : s₄.gpr .r8 = (x.getD 2 0 + z.getD (6 * j + 2) 0).setWidth 64 := v₄
  rw [WP.block_append_iff]
  have h5 : WP isa (.block [.logic .xor .r11 .r6 .r8, .load .w .r12 .r3 (12 * j + 8)]) s₄ fun u =>
      u.gpr .r11 = s₄.gpr .r6 ^^^ s₄.gpr .r8 ∧
      u.gpr .r12 = (s₄.mem.readW (s₄.gpr .r3 + BitVec.ofNat 64 (12 * j + 8)) 32).setWidth 64 ∧
      u.mem = s₄.mem ∧ Keep [.r11, .r12] s₄ u := by
    refine WP.mono (WP.keep (c := .block [.logic .xor .r11 .r6 .r8, .load .w .r12 .r3 (12 * j + 8)])
      [.r11, .r12] (Q := fun u => u.gpr .r11 = s₄.gpr .r6 ^^^ s₄.gpr .r8 ∧
      u.gpr .r12 = (s₄.mem.readW (s₄.gpr .r3 + BitVec.ofNat 64 (12 * j + 8)) 32).setWidth 64 ∧
      u.mem = s₄.mem) ?_ writes_only rfl) fun u ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    irun [k4.1, show 12 * j + 8 < 2 ^ 15 by omega]
  refine WP.mono h5 fun s₅ ⟨a₅, d₅, m₅, e₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep s₅ ((e₅.gpr (by decide)).trans hk₄.mask)) fun s₆ ⟨v₆, m₆, e₆⟩ => ?_
  have hm₆ : s₆.mem = s₄.mem := m₆.trans m₅
  have t₀ : s₆.gpr .r12 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
      (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
    rw [v₆, a₅, d₅, r6₄, r8₄, xor_setWidth, setWidth_setWidth16, lo16, k4.2]
  have e₄₆ : Keep [.r11, .r12] s₄ s₆ := (e₅.trans e₆).mono (by decide)
  have hk₆ : KeyOk z s₆ := hk₄.keep e₄₆ hm₆ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (p6_ok s₆ (12 * j + 10) (by omega) (by
    rw [e₄₆.2.1, e₄₆.2.2, e₄₆.gpr (by decide)]; exact k5.1)) fun s₇ ⟨b₇, a₇, d₇, m₇, e₇⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep s₇ ((e₇.gpr (by decide)).trans hk₆.mask)) fun s₈ ⟨v₈, m₈, e₈⟩ => ?_
  have t₁ : s₈.gpr .r12 = (Spec.Idea.mul (((x.getD 1 0 + z.getD (6 * j + 1) 0) ^^^
      Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)) +
      Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
        (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0))
      (z.getD (6 * j + 5) 0)).setWidth 64 := by
    rw [v₈, a₇, d₇, e₄₆.gpr (by decide), e₄₆.gpr (by decide), r7₄, r9₄, t₀, xor_setWidth,
      add_setWidth, lo16, e₄₆.gpr (by decide), hm₆, k5.2]
  have e₆₈ : Keep [.r10, .r11, .r12] s₆ s₈ := (e₇.trans e₈).mono (by decide)
  have r10₈ : s₈.gpr .r10 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
      (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
    rw [e₈.gpr (by decide), b₇, t₀]
  have g₈ : ∀ r ∈ [Reg.r6, .r7, .r8, .r9], s₈.gpr r = s₄.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (e₆₈.gpr (by decide)).trans (e₄₆.gpr (by decide))
  refine WP.mono (p7_ok s₈ ((e₆₈.gpr (by decide)).trans hk₆.mask)) fun s₉ ⟨r6₉, r7₉, r8₉, r9₉, m₉, e₉⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [r6₉, g₈ .r6 (by simp), r6₄, t₁, xor_setWidth]; rfl
  · rw [r7₉, g₈ .r8 (by simp), r8₄, t₁, xor_setWidth]; rfl
  · rw [r8₉, g₈ .r7 (by simp), r7₄, r10₈, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
  · rw [r9₉, g₈ .r9 (by simp), r9₄, r10₈, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
  · rw [m₉, m₈, m₇, hm₆, m₄, m₃, m₂, m₁]
  · exact (((((e₁.trans e₂).trans e₃).trans e₄).trans e₄₆).trans e₆₈ |>.trans e₉).mono (by decide)

end VG.Proof.Idea.PPC64LE
