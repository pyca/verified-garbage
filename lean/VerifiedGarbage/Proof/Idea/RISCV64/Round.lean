module

import VerifiedGarbage.Proof.Idea.RISCV64.Mul
import VerifiedGarbage.Proof.Idea.Arith
public import VerifiedGarbage.Impl.Idea.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Spec.Idea
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun

/-!
# IDEA on RISC-V: a round

`round_ok`: round `j` of the code (`Impl.Idea.RISCV64.round j`) maps the
state words in `a3`–`a6` (`Holds`) to `Spec.Idea.round` of them under
subkeys `6j … 6j + 5`, read from the schedule at `a0` (`KeyOk`), as on
PPC64LE. It is composed of its pieces: a subkey (`loadKey_ok`), ⊙ and ⊞
with one (`mulKey_ok`, `addKey_ok`), and the multiplication–addition
structure.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64

/-- The state words are in `a3`–`a6`, zero-extended. -/
structure Holds (x : Spec.Idea.State) (s : State) : Prop where
  a3 : s.gpr .a3 = (x.getD 0 0).setWidth 64
  a4 : s.gpr .a4 = (x.getD 1 0).setWidth 64
  a5 : s.gpr .a5 = (x.getD 2 0).setWidth 64
  a6 : s.gpr .a6 = (x.getD 3 0).setWidth 64

/-- The 104 bytes at `a0` can be read and hold the subkeys `z`, and `t2`
holds the mask. -/
structure KeyOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  rd : ∀ i < 104, InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 i) 1
  val : ∀ k < 52, s.mem (s.gpr .a0 + BitVec.ofNat 64 (2 * k + 1)) ++
    s.mem (s.gpr .a0 + BitVec.ofNat 64 (2 * k)) = z.getD k 0
  mask : s.gpr .t2 = 65535

theorem KeyOk.keep {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : KeyOk z s)
    (hk : Keep rs s s') (hm : s'.mem = s.mem) (h0 : .a0 ∉ rs) (h2 : .t2 ∉ rs) : KeyOk z s' := by
  refine ⟨fun i hi => ?_, fun k hk' => ?_, ?_⟩
  · rw [hk.gpr h0, hk.2.1, hk.2.2]
    exact h.rd i hi
  · rw [hk.gpr h0, hm]
    exact h.val k hk'
  · rw [hk.gpr h2]
    exact h.mask

/-- Two bytes, little-endian, as `loadKey` assembles them. -/
theorem bytes16_le (hi lo : BitVec 8) :
    (lo.setWidth 64 ||| hi.setWidth 64 <<< 8) = (hi ++ lo).setWidth 64 := by
  rw [BitVec.or_comm]
  exact Proof.Idea.bytes16 hi lo

/-- `writesOnly` of a block, by evaluation with the destination registers
of its instructions as variables. -/
macro "writes_only" : term => `(by simp [writesOnly, Code.allInstrs_eq, instrs, mulKey, addKey,
  loadKey, mulCode, mov, dstOf])

/-- `r := subkey k` (through `t3`). -/
theorem loadKey_ok {z : Spec.Idea.Schedule} {s : State} (hk : KeyOk z s) {r : Reg}
    (hr : r ≠ .t3 ∧ r ≠ .a0) {k : Nat} (hk' : k < 52) :
    WP isa (.block (loadKey r k)) s fun t =>
      t.gpr r = (z.getD k 0).setWidth 64 ∧ t.mem = s.mem ∧ Keep [r, .t3] s t := by
  refine WP.mono (WP.keep (c := .block (loadKey r k)) [r, .t3] (Q := fun t =>
      t.gpr r = (z.getD k 0).setWidth 64 ∧ t.mem = s.mem) ?_ writes_only rfl)
    fun t ⟨⟨h1, h2⟩, hk⟩ => ⟨h1, h2, hk⟩
  have h0 := hk.rd (2 * k) (by omega)
  have h1 := hk.rd (2 * k + 1) (by omega)
  unfold loadKey
  mrun [h0, h1, show 2 * k < 2048 by omega, show 2 * k + 1 < 2048 by omega, hr.1, hr.2,
    Ne.symm hr.1, Ne.symm hr.2]
  rw [bytes16_le, hk.val k hk']

/-- `t1 := t0 ⊙ t1`, keeping all but `t0` and `t1`. -/
theorem mul_keep (s : State) (h2 : s.gpr .t2 = 65535) :
    WP isa (.block mulCode) s fun t =>
      t.gpr .t1 = (Spec.Idea.mul ((s.gpr .t0).setWidth 16) ((s.gpr .t1).setWidth 16)).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.t0, .t1] s t :=
  WP.mono (WP.keep [.t0, .t1] (mul_ok s h2) (by decide)) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

/-- `r := r ⊙ subkey k`. -/
theorem mulKey_ok {z : Spec.Idea.Schedule} {s : State} (hk : KeyOk z s) {r : Reg}
    (hr : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .a0) {k : Nat} (hk' : k < 52) :
    WP isa (.block (mulKey r k)) s fun t =>
      t.gpr r = (Spec.Idea.mul ((s.gpr r).setWidth 16) (z.getD k 0)).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.t0, .t1, .t3, r] s t := by
  obtain ⟨h0, h1, h2, h3, ha⟩ := hr
  simp only [mulKey, List.append_assoc]
  rw [WP.block_append_iff]
  have hm : WP isa (.block [mov .t0 r]) s fun u => u.gpr .t0 = s.gpr r ∧ u.mem = s.mem ∧
      Keep [.t0] s u := by
    refine WP.mono (WP.keep (c := .block [mov .t0 r]) [.t0] (Q := fun u =>
      u.gpr .t0 = s.gpr r ∧ u.mem = s.mem) ?_ writes_only rfl) fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    unfold mov
    mrun
  refine WP.mono hm fun u ⟨u0, um, ue⟩ => ?_
  have hku := hk.keep ue um (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadKey_ok hku (r := .t1) (by decide) hk') fun v ⟨v1, vm, ve⟩ => ?_
  have v0 : v.gpr .t0 = s.gpr r := (ve.gpr (by decide)).trans u0
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep v ((ve.gpr (by decide)).trans hku.mask)) fun w ⟨w1, wm, we⟩ => ?_
  have hw : WP isa (.block [mov r .t1]) w fun t => t.gpr r = w.gpr .t1 ∧ t.mem = w.mem ∧
      Keep [r] w t := by
    refine WP.mono (WP.keep (c := .block [mov r .t1]) [r] (Q := fun t =>
      t.gpr r = w.gpr .t1 ∧ t.mem = w.mem) ?_ writes_only rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    unfold mov
    mrun
  refine WP.mono hw fun t ⟨t1, tm, te⟩ => ⟨?_, ?_, ?_⟩
  · rw [t1, w1, v0, v1, setWidth_setWidth16]
  · rw [tm, wm, vm, um]
  · exact (((ue.trans ve).trans we).trans te).mono (by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx ⊢
      rcases hx with h | h | h | h | h | h <;> simp only [h, true_or, or_true])

/-- `r := r ⊞ subkey k`, zero-extended. -/
theorem addKey_ok {z : Spec.Idea.Schedule} {s : State} (hk : KeyOk z s) {r : Reg}
    (hr : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .a0) {k : Nat} (hk' : k < 52)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 64) :
    WP isa (.block (addKey r k)) s fun t =>
      t.gpr r = (x + z.getD k 0).setWidth 64 ∧ t.mem = s.mem ∧ Keep [.t1, .t3, r] s t := by
  obtain ⟨h1, h2, h3, ha⟩ := hr
  simp only [addKey]
  rw [WP.block_append_iff]
  refine WP.mono (loadKey_ok hk (r := .t1) (by decide) hk') fun v ⟨v1, vm, ve⟩ => ?_
  have vr : v.gpr r = x.setWidth 64 := (ve.gpr (by simp [h1, h3])).trans hx
  have v2 : v.gpr .t2 = 65535 := (ve.gpr (by decide)).trans hk.mask
  have hw : WP isa (.block [.add r r .t1, .logic .and r r .t2]) v fun t =>
      t.gpr r = (v.gpr r + v.gpr .t1) &&& v.gpr .t2 ∧ t.mem = v.mem ∧ Keep [r] v t := by
    refine WP.mono (WP.keep (c := .block [.add r r .t1, .logic .and r r .t2]) [r] (Q := fun t =>
      t.gpr r = (v.gpr r + v.gpr .t1) &&& v.gpr .t2 ∧ t.mem = v.mem) ?_ writes_only rfl)
      fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    mrun [h2, Ne.symm h2]
  refine WP.mono hw fun t ⟨t1, tm, te⟩ => ⟨?_, ?_, ?_⟩
  · rw [t1, vr, v1, v2, add_mask, setWidth_setWidth16]
  · rw [tm, vm]
  · exact (ve.trans te).mono (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hy ⊢
      rcases hy with h | h | h <;> simp only [h, true_or, or_true])

/-- The registers a round writes. -/
abbrev roundWrites : List Reg := [.a3, .a4, .a5, .a6, .a7, .t0, .t1, .t3]

theorem p7_ok (s : State) (h2 : s.gpr .t2 = 65535) :
    WP isa (.block [.add .a7 .a7 .t1, .logic .and .a7 .a7 .t2,
        .logic .xor .a3 .a3 .t1, .logic .xor .a5 .a5 .t1,
        .logic .xor .a4 .a4 .a7, .logic .xor .a6 .a6 .a7,
        mov .t0 .a4, mov .a4 .a5, mov .a5 .t0]) s fun t =>
      t.gpr .a3 = s.gpr .a3 ^^^ s.gpr .t1 ∧
      t.gpr .a4 = s.gpr .a5 ^^^ s.gpr .t1 ∧
      t.gpr .a5 = s.gpr .a4 ^^^ ((s.gpr .a7 + s.gpr .t1) &&& 65535) ∧
      t.gpr .a6 = s.gpr .a6 ^^^ ((s.gpr .a7 + s.gpr .t1) &&& 65535) ∧
      t.mem = s.mem ∧ Keep roundWrites s t := by
  refine WP.mono (WP.keep [.a3, .a4, .a5, .a6, .a7, .t0] (Q := fun t =>
      t.gpr .a3 = s.gpr .a3 ^^^ s.gpr .t1 ∧
      t.gpr .a4 = s.gpr .a5 ^^^ s.gpr .t1 ∧
      t.gpr .a5 = s.gpr .a4 ^^^ ((s.gpr .a7 + s.gpr .t1) &&& 65535) ∧
      t.gpr .a6 = s.gpr .a6 ^^^ ((s.gpr .a7 + s.gpr .t1) &&& 65535) ∧
      t.mem = s.mem) ?_ (by decide) rfl) fun t ⟨⟨a, b, c, d, e⟩, f⟩ =>
    ⟨a, b, c, d, e, f.mono (by decide)⟩
  unfold mov
  mrun [h2]

theorem round_ok (j : Nat) (hj : j < 8) (z : Spec.Idea.Schedule) (x : Spec.Idea.State)
    (s : State) (hx : Holds x s) (hk : KeyOk z s) :
    WP isa (.block (round j)) s fun t =>
      Holds (Spec.Idea.round (z.getD (6 * j) 0) (z.getD (6 * j + 1) 0) (z.getD (6 * j + 2) 0)
        (z.getD (6 * j + 3) 0) (z.getD (6 * j + 4) 0) (z.getD (6 * j + 5) 0) x) t ∧
      t.mem = s.mem ∧ Keep roundWrites s t := by
  simp only [round, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok hk (r := .a3) (by decide) (k := 6 * j) (by omega)) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [hx.a3, setWidth_setWidth16] at v₁
  have hk₁ := hk.keep e₁ m₁ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok hk₁ (r := .a6) (by decide) (k := 6 * j + 3) (by omega))
    fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [e₁.gpr (by decide), hx.a6, setWidth_setWidth16] at v₂
  have hk₂ := hk₁.keep e₂ m₂ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok hk₂ (r := .a4) (by decide) (k := 6 * j + 1) (by omega) (x.getD 1 0)
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.a4))) fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  have hk₃ := hk₂.keep e₃ m₃ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok hk₃ (r := .a5) (by decide) (k := 6 * j + 2) (by omega) (x.getD 2 0)
    ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.a5))))
    fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  have hk₄ := hk₃.keep e₄ m₄ (by decide) (by decide)
  -- The words through the pieces.
  have a3₄ : s₄.gpr .a3 = (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0)).setWidth 64 :=
    (e₄.gpr (by decide)).trans ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans v₁))
  have a6₄ : s₄.gpr .a6 = (Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)).setWidth 64 :=
    (e₄.gpr (by decide)).trans ((e₃.gpr (by decide)).trans v₂)
  have a4₄ : s₄.gpr .a4 = (x.getD 1 0 + z.getD (6 * j + 1) 0).setWidth 64 :=
    (e₄.gpr (by decide)).trans v₃
  have a5₄ : s₄.gpr .a5 = (x.getD 2 0 + z.getD (6 * j + 2) 0).setWidth 64 := v₄
  -- t₀ = (x₁ ⊙ z₁ ^ x₃ ⊞ z₃) ⊙ z₅
  rw [WP.block_append_iff]
  have h5 : WP isa (.block [.logic .xor .t0 .a3 .a5]) s₄ fun u =>
      u.gpr .t0 = s₄.gpr .a3 ^^^ s₄.gpr .a5 ∧ u.mem = s₄.mem ∧ Keep [.t0] s₄ u := by
    refine WP.mono (WP.keep (c := .block [.logic .xor .t0 .a3 .a5]) [.t0] (Q := fun u =>
      u.gpr .t0 = s₄.gpr .a3 ^^^ s₄.gpr .a5 ∧ u.mem = s₄.mem) ?_ writes_only rfl)
      fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    mrun
  refine WP.mono h5 fun s₅ ⟨a₅, m₅, e₅⟩ => ?_
  have hk₅ := hk₄.keep e₅ m₅ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadKey_ok hk₅ (r := .t1) (by decide) (k := 6 * j + 4) (by omega))
    fun s₅' ⟨d₅, m₅', e₅'⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep s₅' ((e₅'.gpr (by decide)).trans hk₅.mask)) fun s₆ ⟨v₆, m₆, e₆⟩ => ?_
  have e₄₆ : Keep [.t0, .t1, .t3] s₄ s₆ := ((e₅.trans e₅').trans e₆).mono (by decide)
  have hm₆ : s₆.mem = s₄.mem := m₆.trans (m₅'.trans m₅)
  have t₀ : s₆.gpr .t1 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
      (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
    rw [v₆, e₅'.gpr (by decide), a₅, d₅, a3₄, a5₄, xor_setWidth, setWidth_setWidth16,
      setWidth_setWidth16]
  have hk₆ : KeyOk z s₆ := hk₄.keep e₄₆ hm₆ (by decide) (by decide)
  -- t₁ = ((x₂ ⊞ z₂ ^ x₄ ⊙ z₄) ⊞ t₀) ⊙ z₆
  rw [WP.block_append_iff]
  have h6 : WP isa (.block [mov .a7 .t1, .logic .xor .t0 .a4 .a6, .add .t0 .t0 .a7]) s₆ fun u =>
      u.gpr .a7 = s₆.gpr .t1 ∧ u.gpr .t0 = (s₆.gpr .a4 ^^^ s₆.gpr .a6) + s₆.gpr .t1 ∧
      u.mem = s₆.mem ∧ Keep [.a7, .t0] s₆ u := by
    refine WP.mono (WP.keep (c := .block [mov .a7 .t1, .logic .xor .t0 .a4 .a6,
      .add .t0 .t0 .a7]) [.a7, .t0] (Q := fun u =>
      u.gpr .a7 = s₆.gpr .t1 ∧ u.gpr .t0 = (s₆.gpr .a4 ^^^ s₆.gpr .a6) + s₆.gpr .t1 ∧
      u.mem = s₆.mem) ?_ writes_only rfl) fun u ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold mov
    mrun
  refine WP.mono h6 fun s₇ ⟨b₇, a₇, m₇, e₇⟩ => ?_
  have hk₇ := hk₆.keep e₇ m₇ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadKey_ok hk₇ (r := .t1) (by decide) (k := 6 * j + 5) (by omega))
    fun s₇' ⟨d₇, m₇', e₇'⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep s₇' ((e₇'.gpr (by decide)).trans hk₇.mask)) fun s₈ ⟨v₈, m₈, e₈⟩ => ?_
  have e₆₈ : Keep [.a7, .t0, .t1, .t3] s₆ s₈ := ((e₇.trans e₇').trans e₈).mono (by decide)
  have t₁ : s₈.gpr .t1 = (Spec.Idea.mul (((x.getD 1 0 + z.getD (6 * j + 1) 0) ^^^
      Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)) +
      Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
        (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0))
      (z.getD (6 * j + 5) 0)).setWidth 64 := by
    rw [v₈, e₇'.gpr (by decide), a₇, d₇, e₄₆.gpr (by decide), e₄₆.gpr (by decide), a4₄, a6₄, t₀,
      xor_setWidth, add_setWidth, setWidth_setWidth16]
  have a7₈ : s₈.gpr .a7 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
      (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
    rw [e₈.gpr (by decide), e₇'.gpr (by decide), b₇, t₀]
  have g₈ : ∀ r ∈ [Reg.a3, .a4, .a5, .a6], s₈.gpr r = s₄.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (e₆₈.gpr (by decide)).trans (e₄₆.gpr (by decide))
  refine WP.mono (p7_ok s₈ ((e₆₈.gpr (by decide)).trans hk₆.mask))
    fun s₉ ⟨a3₉, a4₉, a5₉, a6₉, m₉, e₉⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [a3₉, g₈ .a3 (by simp), a3₄, t₁, xor_setWidth]; rfl
  · rw [a4₉, g₈ .a5 (by simp), a5₄, t₁, xor_setWidth]; rfl
  · rw [a5₉, g₈ .a4 (by simp), a4₄, a7₈, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
  · rw [a6₉, g₈ .a6 (by simp), a6₄, a7₈, t₁, add_mask, setWidth_setWidth16, xor_setWidth]; rfl
  · rw [m₉, m₈, m₇', m₇, hm₆, m₄, m₃, m₂, m₁]
  · exact (((((e₁.trans e₂).trans e₃).trans e₄).trans e₄₆).trans e₆₈ |>.trans e₉).mono (by decide)

end VG.Proof.Idea.RISCV64
