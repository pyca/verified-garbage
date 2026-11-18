module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Idea.RISCV64.Lit
public import VerifiedGarbage.Proof.Idea.Arith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Idea.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Spec.Idea
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Idea.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Spec.Idea
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.RISCV64.Isa

/-! ### `Idea.RISCV64.Block`, which this module and modules that import it used -/

section

/-! ### `Idea.RISCV64.Round`, which this module and modules that import it used -/

section

/-! ### `Idea.RISCV64.Mul`, which this module and modules that import it used -/

section

/-!
# IDEA on RISC-V: ⊙ without branches

`mul_ok`: `mulCode` leaves `t0 ⊙ t1` (of their low 16 bits) in `t1`, with
the mask `0xffff` in `t2`, and changes nothing but `t0` and `t1`; the
arithmetic is the shared `prep_toNat` and `reduce`, as on PPC64LE.
`setMask_ok`: `setMask` puts the mask in `t2`.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64

/-- A product of 64-bit values that does not wrap around. -/
theorem mul_ofNat (a b : BitVec 64) (_h : a.toNat * b.toNat < 2 ^ 64) :
    a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

theorem mul_ok (s : State) (h2 : s.gpr .t2 = 65535) :
    WP isa (.block mulCode) s fun t =>
      t.gpr .t1 = (Spec.Idea.mul ((s.gpr .t0).setWidth 16) ((s.gpr .t1).setWidth 16)).setWidth 64 ∧
      t.mem = s.mem := by
  unfold mulCode
  crun [h2]
  have hA : ((s.gpr .t0 - 1#64 &&& 65535#64) + 1#64).toNat =
      Spec.Idea.residue ((s.gpr .t0).setWidth 16) := prep_toNat _ 65535#64 rfl
  have hB : ((s.gpr .t1 - 1#64 &&& 65535#64) + 1#64).toNat =
      Spec.Idea.residue ((s.gpr .t1).setWidth 16) := prep_toNat _ 65535#64 rfl
  have hp := Nat.mul_le_mul (residue_le ((s.gpr .t0).setWidth 16)) (residue_le ((s.gpr .t1).setWidth 16))
  rw [mul_ofNat _ _ (by rw [hA, hB]; exact Nat.lt_of_le_of_lt hp (by decide)), hA, hB, mul_toNat]
  exact reduce _ (Nat.le_trans hp (by decide)) 65535#64 rfl

theorem setMask_ok (s : State) :
    WP isa (.block setMask) s fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem := by
  unfold setMask
  crun
  decide

end VG.Proof.Idea.RISCV64

end

end

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
  have h0 := hk.rd (2 * k) (by omega_using [hk'])
  have h1 := hk.rd (2 * k + 1) (by omega_using [hk'])
  unfold loadKey
  mrun [h0, h1, show 2 * k < 2048 by omega_using [hk'], show 2 * k + 1 < 2048 by omega_using [hk'], hr.1, hr.2,
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
  refine WP.mono (mulKey_ok hk (r := .a3) (by decide) (k := 6 * j) (by omega_using [hj])) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [hx.a3, setWidth_setWidth16] at v₁
  have hk₁ := hk.keep e₁ m₁ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok hk₁ (r := .a6) (by decide) (k := 6 * j + 3) (by omega_using [hj]))
    fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [e₁.gpr (by decide), hx.a6, setWidth_setWidth16] at v₂
  have hk₂ := hk₁.keep e₂ m₂ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok hk₂ (r := .a4) (by decide) (k := 6 * j + 1) (by omega_using [hj]) (x.getD 1 0)
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.a4))) fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  have hk₃ := hk₂.keep e₃ m₃ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok hk₃ (r := .a5) (by decide) (k := 6 * j + 2) (by omega_using [hj]) (x.getD 2 0)
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
  refine WP.mono (loadKey_ok hk₅ (r := .t1) (by decide) (k := 6 * j + 4) (by omega_using [hj]))
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
  refine WP.mono (loadKey_ok hk₇ (r := .t1) (by decide) (k := 6 * j + 5) (by omega_using [hj]))
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

end

end

/-!
# IDEA on RISC-V: a block

`cryptBlock_ok`: `Impl.Idea.RISCV64.cryptBlock` replaces the block at `a1`
with `Spec.Idea.cryptBlock` of it under the subkeys at `a0`: the block's
words are loaded a byte at a time (`load_ok`), run through the rounds
(`rounds_ok`) and the output transformation (`output_ok`), and stored a
byte at a time (`store_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64

/-! ## Loading -/

theorem loadWord_ok {r : Reg} (hr : r ≠ .t3 ∧ r ≠ .a1) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .a1 = a)
    (h0 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k)) 1)
    (h1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k + 1)) 1) :
    WP isa (.block (loadWord r k)) s fun t =>
      t.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++ s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.t3, r] s t := by
  refine WP.mono (WP.keep (c := .block (loadWord r k)) [.t3, r] (Q := fun t =>
      t.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++
        s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      t.mem = s.mem) ?_ (by simp [writesOnly, Code.allInstrs_eq, instrs, loadWord, dstOf]) rfl)
    fun t ⟨⟨h₁, h₂⟩, hk⟩ => ⟨h₁, h₂, hk⟩
  unfold loadWord
  mrun [ha, h0, h1, hr.1, Ne.symm hr.1, hr.2, Ne.symm hr.2, show 2 * k < 2048 by omega_using [hk], show 2 * k + 1 < 2048 by omega_using [hk]]
  exact bytes16 _ _

/-- The bytes of the block at `a` can be read. -/
def BlockRead (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1

theorem BlockRead.keep {rs : List Reg} {s s' : State} {a : Addr} (h : BlockRead s a)
    (hk : Keep rs s s') : BlockRead s' a := by
  intro i hi; rw [hk.2.1, hk.2.2]; exact h i hi

theorem load_ok (s : State) {a : Addr} (ha : s.gpr .a1 = a) (hb : BlockRead s a) :
    WP isa (.block load) s fun t =>
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem a)) t ∧ t.mem = s.mem ∧
      Keep [.t3, .a3, .a4, .a5, .a6] s t := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem a hk
  simp only [load, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .a3) (by decide) 0 (by decide) s ha (hb _ (by decide))
    (hb _ (by decide))) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .a4) (by decide) 1 (by decide) s₁ ((e₁.gpr (by decide)).trans ha)
    ((hb.keep e₁) _ (by decide)) ((hb.keep e₁) _ (by decide))) fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .a5) (by decide) 2 (by decide) s₂
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans ha))
    ((hb.keep e₁ |>.keep e₂) _ (by decide)) ((hb.keep e₁ |>.keep e₂) _ (by decide)))
    fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  refine WP.mono (loadWord_ok (r := .a6) (by decide) 3 (by decide) s₃
    ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans ha)))
    ((hb.keep e₁ |>.keep e₂ |>.keep e₃) _ (by decide)) ((hb.keep e₁ |>.keep e₂ |>.keep e₃) _ (by decide)))
    fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by rw [m₄, m₃, m₂, m₁], (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)⟩
  · rw [e₄.gpr (by decide), e₃.gpr (by decide), e₂.gpr (by decide), v₁, w 0 (by decide)]
  · rw [e₄.gpr (by decide), e₃.gpr (by decide), v₂, m₁, w 1 (by decide)]
  · rw [e₄.gpr (by decide), v₃, m₂, m₁, w 2 (by decide)]
  · rw [v₄, m₃, m₂, m₁, w 3 (by decide)]

/-! ## The rounds -/

theorem rounds_ok (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x s → KeyOk z s →
      WP isa (.block ((List.range n).flatMap round)) s fun t =>
        Holds (roundsSpec z n x) t ∧ t.mem = s.mem ∧ Keep roundWrites s t
  | 0, _, s, hx, _ => WP.block_nil ⟨hx, rfl, Keep.refl _ _⟩
  | n + 1, hn, s, hx, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (rounds_ok z x n (by omega_using [hn]) s hx hk) fun s₁ ⟨x₁, m₁, e₁⟩ => ?_
    refine WP.mono (round_ok n (by omega_using [hn]) z _ s₁ x₁ (hk.keep e₁ m₁ (by decide) (by decide)))
      fun s₂ ⟨x₂, m₂, e₂⟩ => ⟨?_, m₂.trans m₁, (e₁.trans e₂).mono (by decide)⟩
    simp only [roundsSpec, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact x₂

/-! ## The output transformation -/

/-- The output words: `Y₁` in `a3`, `Y₂` in `a5`, `Y₃` in `a4`, `Y₄` in `a6`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  a3 : s.gpr .a3 = (y.getD 0 0).setWidth 64
  a5 : s.gpr .a5 = (y.getD 1 0).setWidth 64
  a4 : s.gpr .a4 = (y.getD 2 0).setWidth 64
  a6 : s.gpr .a6 = (y.getD 3 0).setWidth 64

theorem output_ok (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x s)
    (hk : KeyOk z s) :
    WP isa (.block output) s fun t =>
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) t ∧
      t.mem = s.mem ∧ Keep roundWrites s t := by
  simp only [output, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok hk (r := .a3) (by decide) (k := 48) (by decide)) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [hx.a3, setWidth_setWidth16] at v₁
  have hk₁ := hk.keep e₁ m₁ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok hk₁ (r := .a6) (by decide) (k := 51) (by decide)) fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [e₁.gpr (by decide), hx.a6, setWidth_setWidth16] at v₂
  have hk₂ := hk₁.keep e₂ m₂ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok hk₂ (r := .a5) (by decide) (k := 49) (by decide) (x.getD 2 0)
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.a5))) fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  have hk₃ := hk₂.keep e₃ m₃ (by decide) (by decide)
  refine WP.mono (addKey_ok hk₃ (r := .a4) (by decide) (k := 50) (by decide) (x.getD 1 0)
    ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.a4))))
    fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by rw [m₄, m₃, m₂, m₁],
    (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)⟩
  · rw [e₄.gpr (by decide), e₃.gpr (by decide), e₂.gpr (by decide), v₁, output_getD0]
  · rw [e₄.gpr (by decide), v₃, output_getD1]
  · rw [v₄, output_getD2]
  · rw [e₄.gpr (by decide), e₃.gpr (by decide), v₂, output_getD3]

/-! ## Storing -/

theorem storeWord_ok (r : Reg) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .a1 = a)
    (h1 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k + 1)) 1)
    (h0 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k)) 1) :
    WP isa (.block (storeWord r k)) s fun t =>
      t.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8) ∧
      Keep [.t3] s t := by
  refine WP.mono (WP.keep (c := .block (storeWord r k)) [.t3] (Q := fun t =>
      t.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8)) ?_
      (by rfl) rfl)
    fun t ⟨h, hk⟩ => ⟨h, hk⟩
  unfold storeWord
  mrun [ha, h0, h1, show 2 * k < 2048 by omega_using [hk],
    show 2 * k + 1 < 2048 by omega_using [hk]]

/-- The bytes of the block at `a` can be written. -/
def BlockWrite (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 i) 1

theorem frame_write1 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.write (a + BitVec.ofNat 64 j) 1 v) :=
  h.write (List.mem_singleton_self _) (n := 1) v (Offset.contains_base a (by omega_using [hj]) (by omega_using [hj]))

theorem store_ok (y : Spec.Idea.State) (s : State) {a : Addr} (ha : s.gpr .a1 = a)
    (hw : BlockWrite s a) (hy : OutHolds y s) :
    WP isa (.block store) s fun t =>
      Spec.Idea.blockAt t.mem a = Spec.Idea.encodeBlock y ∧
      Frame [⟨a, 8⟩] s.mem t.mem ∧ Keep [.t3] s t := by
  simp only [store, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .a3 0 (by decide) s ha (hw _ (by decide))
    (hw _ (by decide))) fun s₁ ⟨m₁, e₁⟩ => ?_
  have ha₁ : s₁.gpr .a1 = a := (e₁.gpr (by decide)).trans ha
  have hw₁ : BlockWrite s₁ a := fun i hi => e₁.2.2 ▸ hw i hi
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .a5 1 (by decide) s₁ ha₁ (hw₁ _ (by decide))
    (hw₁ _ (by decide))) fun s₂ ⟨m₂, e₂⟩ => ?_
  have ha₂ : s₂.gpr .a1 = a := (e₂.gpr (by decide)).trans ha₁
  have hw₂ : BlockWrite s₂ a := fun i hi => e₂.2.2 ▸ hw₁ i hi
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .a4 2 (by decide) s₂ ha₂ (hw₂ _ (by decide))
    (hw₂ _ (by decide))) fun s₃ ⟨m₃, e₃⟩ => ?_
  have ha₃ : s₃.gpr .a1 = a := (e₃.gpr (by decide)).trans ha₂
  have hw₃ : BlockWrite s₃ a := fun i hi => e₃.2.2 ▸ hw₂ i hi
  refine WP.mono (storeWord_ok .a6 3 (by decide) s₃ ha₃ (hw₃ _ (by decide))
    (hw₃ _ (by decide))) fun s₄ ⟨m₄, e₄⟩ => ?_
  have v8 : s₁.gpr .a5 = (y.getD 1 0).setWidth 64 := (e₁.gpr (by decide)).trans hy.a5
  have v7 : s₂.gpr .a4 = (y.getD 2 0).setWidth 64 :=
    (e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hy.a4)
  have v9 : s₃.gpr .a6 = (y.getD 3 0).setWidth 64 :=
    (e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hy.a6))
  rw [v9] at m₄
  rw [v7] at m₃
  rw [v8] at m₂
  rw [hy.a3] at m₁
  rw [m₃, m₂, m₁] at m₄
  refine ⟨?_, ?_, (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)⟩
  · apply Vector.ext
    intro i hi
    simp only [Spec.Idea.blockAt, Vector.getElem_ofFn, m₄, encodeBlock_get _ hi]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
        i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [hi]
    all_goals simp (disch := decide) only [write1_apply, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, lo8, hi8, BitVec.ushiftRight_zero]
  · rw [m₄]
    repeat' apply frame_write1 _ (by decide)
    exact Frame.refl _ _

/-! ## A block -/

theorem cryptBlock_ok (z : Spec.Idea.Schedule) (s : State) {a : Addr} (ha : s.gpr .a1 = a)
    (hb : BlockRead s a) (hw : BlockWrite s a) (hk : KeyOk z s) :
    WP isa (.block cryptBlock) s fun t =>
      Spec.Idea.blockAt t.mem a = Spec.Idea.cryptBlock z (Spec.Idea.blockAt s.mem a) ∧
      Frame [⟨a, 8⟩] s.mem t.mem ∧ Keep roundWrites s t := by
  simp only [cryptBlock, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (load_ok s ha hb) fun s₁ ⟨x₁, m₁, e₁⟩ => ?_
  have k₁ := hk.keep e₁ m₁ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rounds_ok z _ 8 (by decide) s₁ x₁ k₁) fun s₂ ⟨x₂, m₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (output_ok z _ s₂ x₂ (k₁.keep e₂ m₂ (by decide) (by decide))) fun s₃ ⟨x₃, m₃, e₃⟩ => ?_
  have e₁₃ : Keep roundWrites s s₃ := ((e₁.trans e₂).trans e₃).mono (by decide)
  have m₁₃ : s₃.mem = s.mem := m₃.trans (m₂.trans m₁)
  refine WP.mono (store_ok _ s₃ ((e₁₃.gpr (by decide)).trans ha)
    (fun i hi => e₁₃.2.2 ▸ hw i hi) x₃) fun s₄ ⟨b₄, f₄, e₄⟩ => ?_
  refine ⟨?_, ?_, (e₁₃.trans e₄).mono (by decide)⟩
  · rw [b₄, Spec.Idea.cryptBlock, crypt_eq]
  · rw [← m₁₃]; exact f₄

end VG.Proof.Idea.RISCV64

end

end

/-!
# IDEA ECB on RISC-V

`ecb_verified`: `Impl.Idea.RISCV64.ecb` meets the shared ECB contract. The
blocks are transformed in a loop (`loop_ok`) whose invariant (`LoopInv`)
says how many remain, that the ones before are transformed and the ones
after not yet; each iteration is `cryptBlock_ok`.
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64

/-- `KeyOk` of the schedule in a readable region at `a0`, with the mask in `t2`. -/
theorem keyOk_of (s : State) (hr : ⟨s.gpr .a0, 104⟩ ∈ s.rd ++ s.wr) (h2 : s.gpr .t2 = 65535) :
    KeyOk (Spec.Idea.scheduleAt s.mem (s.gpr .a0)) s :=
  ⟨fun i hi => ⟨_, hr, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩,
    fun k hk => (scheduleAt_getD _ _ hk).symm, h2⟩

/-! ## The loop -/

/-- The registers the loop writes. -/
abbrev loopWrites : List Reg := [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t3]

/-- The facts about the state `o` before the loop that the loop relies on:
the schedule `z` at `r3`, readable, the mask in `r0`, and `n` blocks at `a`,
writable, apart from it and not wrapping around. -/
structure LoopCtx (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (o : State) : Prop where
  sched : ⟨o.gpr .a0, 104⟩ ∈ o.rd ++ o.wr
  data : ⟨a, 8 * n⟩ ∈ o.wr
  z : Spec.Idea.scheduleAt o.mem (o.gpr .a0) = z
  sep : (⟨o.gpr .a0, 104⟩ : Region).Disjoint ⟨a, 8 * n⟩
  bound : 8 * n ≤ 2 ^ 64
  mask : o.gpr .t2 = 65535

/-- `r` blocks remain, at `a + 8 (n - r)` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  a1 : t.gpr .a1 = a + BitVec.ofNat 64 (8 * (n - r))
  a2 : t.gpr .a2 = BitVec.ofNat 64 r
  keep : Keep loopWrites o t
  frame : Frame [⟨a, 8 * n⟩] o.mem t.mem
  done : ∀ j < n - r, Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))
  todo : ∀ j, n - r ≤ j → j < n → Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))

/-- After the loop: every block transformed. -/
structure LoopPost (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State)
    (t : State) : Prop where
  keep : Keep loopWrites o t
  frame : Frame [⟨a, 8 * n⟩] o.mem t.mem
  done : ∀ j < n, Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) =
    Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))

theorem tail_ok (s : State) :
    WP isa (.block [.addi .a1 .a1 8, .addi .a2 .a2 (-1)]) s fun t =>
      t.gpr .a1 = s.gpr .a1 + 8#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧ t.mem = s.mem ∧
      Keep [.a1, .a2] s t := by
  refine WP.mono (WP.keep [.a1, .a2] (Q := fun t =>
      t.gpr .a1 = s.gpr .a1 + 8#64 ∧ t.gpr .a2 = s.gpr .a2 - 1#64 ∧ t.mem = s.mem) ?_ (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  mrun

theorem step_ok {z : Spec.Idea.Schedule} {a : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z a n o) (r : Nat) (t : State) (hi : LoopInv z a n m₀ o r t) :
    WP isa (.block (cryptBlock ++ ([.addi .a1 .a1 8, .addi .a2 .a2 (-1)] : List Instr))) t
      (fun t' => (isa.eval (.nonzero .a2) t' = some false ∧ LoopPost z a n m₀ o t') ∨
        (isa.eval (.nonzero .a2) t' = some true ∧ ∃ r' < r, LoopInv z a n m₀ o r' t')) := by
  have hrd : t.rd = o.rd := hi.keep.2.1
  have hwr : t.wr = o.wr := hi.keep.2.2
  have ha0 : t.gpr .a0 = o.gpr .a0 := hi.keep.gpr (by decide)
  have ht2 : t.gpr .t2 = o.gpr .t2 := hi.keep.gpr (by decide)
  have hj : n - r < n := by have := hi.pos; have := hi.le; omega_arith
  have hread : BlockRead t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hrd, hwr]; exact List.mem_append_right _ hc.data, block_contains hj (by omega_using [hi']) (by decide) hc.bound⟩
  have hwrite : BlockWrite t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hwr]; exact hc.data, block_contains hj (by omega_using [hi']) (by decide) hc.bound⟩
  have hz : Spec.Idea.scheduleAt t.mem (t.gpr .a0) = z := by
    rw [ha0, ← hc.z]
    exact scheduleAt_congr (frame_bytes hi.frame (by simpa using hc.sep) (by decide))
  have hk : KeyOk z t := by
    have h := keyOk_of t (by rw [ha0, hrd, hwr]; exact hc.sched) (ht2.trans hc.mask)
    rwa [hz] at h
  rw [WP.block_append_iff]
  refine WP.mono (cryptBlock_ok z t hi.a1 hread hwrite hk) fun t₁ ⟨b₁, f₁, e₁⟩ => ?_
  refine WP.mono (tail_ok t₁) fun t₂ ⟨a1₂, a2₂, m₂, e₂⟩ => ?_
  have keep₂ : Keep loopWrites o t₂ := ((hi.keep.trans e₁).trans e₂).mono (by decide)
  have frame₂ : Frame [⟨a, 8 * n⟩] o.mem t₂.mem := by
    rw [m₂]
    refine hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base a (by omega_using [hj])
  have other (j : Nat) (hjn : j < n) (hne : j ≠ n - r) :
      Spec.Idea.blockAt t₂.mem (a + BitVec.ofNat 64 (8 * j)) =
        Spec.Idea.blockAt t.mem (a + BitVec.ofNat 64 (8 * j)) := by
    rw [m₂]
    exact blockAt_congr (frame_bytes f₁ (by
      intro q hq; simp only [List.mem_singleton] at hq; subst hq
      exact blocks_disjoint hj hjn (Ne.symm hne) hc.bound) (by decide))
  have done₂ : ∀ j < n - (r - 1), Spec.Idea.blockAt t₂.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) := by
    intro j hjr
    by_cases he : j = n - r
    · subst he
      rw [m₂, b₁, hi.todo _ (Nat.le_refl _) hj]
    · rw [other j (by omega_using [hjr]) he]
      exact hi.done j (by have := hi.pos; omega_using [hjr, he])
  have ha2 : t₂.gpr .a2 = BitVec.ofNat 64 (r - 1) := by
    rw [a2₂, e₁.gpr (by decide), hi.a2]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le; have := hc.bound
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hj]
  by_cases hlast : r = 1
  · subst hlast
    left
    refine ⟨?_, keep₂, frame₂, fun j hjn => done₂ j (by omega_using [hjn])⟩
    rw [Steps.eval_nonzero_ofNat _ _ (by omega_using []) ha2]
    rfl
  · right
    refine ⟨?_, r - 1, by have := hi.pos; omega_using [hj], ?_⟩
    · have := hi.pos; have := hi.le; have := hc.bound
      rw [Steps.eval_nonzero_ofNat _ _ (by omega_arith) ha2]
      simp only [Option.some.injEq, decide_eq_true_eq]
      omega_using [hj, hlast]
    · refine ⟨by have := hi.pos; omega_using [hj, hlast], by have := hi.le; omega_using [this], ?_, ha2, keep₂, frame₂, done₂, ?_⟩
      · rw [a1₂, e₁.gpr (by decide), hi.a1, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
          Offset.add_ofNat_add_ofNat]
        congr 2
        have := hi.pos; have := hi.le
        omega_using [hj, this]
      · intro j hj₁ hj₂
        have := hi.pos
        have := hi.le
        have hne : j ≠ n - r := by omega_using [hj, hj₁, this]
        rw [other j hj₂ hne]
        exact hi.todo j (by omega_using [hj₁]) hj₂

theorem loop_ok {z : Spec.Idea.Schedule} {a : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z a n o) (hn : 1 ≤ n) (ho : o.gpr .a1 = a) (ha2 : o.gpr .a2 = BitVec.ofNat 64 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block (cryptBlock ++ ([.addi .a1 .a1 8, .addi .a2 .a2 (-1)] : List Instr)))
      (.nonzero .a2)) o (LoopPost z a n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z a n m₀ o) (fun r t hi => step_ok hc r t hi) n o ⟨hn, Nat.le_refl _, ?_,
    ha2, Keep.refl _ _, Frame.refl _ _, fun j hj => by omega, fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero, ho]; exact (BitVec.add_zero a).symm

/-! ## The function -/

/-- The ECB contract on RISC-V. -/
def contract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 104⟩
    let data : Region := ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
    s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧
      (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  post s s' := Spec.Idea.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
    Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem (s.gpr .a0))
      (Spec.Idea.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

/-- The registers `ecb` writes: all volatile. -/
abbrev ecbWrites : List Reg := [.t2, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t3]

theorem ecb_wp (s : State) (hs : contract.pre s) :
    WP isa ecb s (fun s' => contract.post s s') := by
  obtain ⟨hrd, hwr, dSched, hbound⟩ := hs
  unfold ecb
  apply WP.seq
  have h1 : WP isa (.block setMask) s fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem ∧
      Keep [.t2] s t := by
    refine WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .t2 = 65535 ∧ t.mem = s.mem) ?_
      (by decide) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    exact WP.mono (setMask_ok s) fun t ⟨a, b⟩ => ⟨a, b⟩
  refine WP.mono h1 fun s₁ ⟨h0₁, m₁, e₁⟩ => ?_
  refine WP.ite ((s.gpr .a2) == 0) (by rw [Steps.eval_zero, e₁.gpr (show Reg.a2 ∉ [Reg.t2] by decide)])
    (fun h0 => ?_) (fun h0 => ?_)
  · -- No blocks.
    have hn : s.gpr .a2 = 0 := beq_iff_eq.mp h0
    refine WP.block_nil ?_
    show Spec.Idea.blocksAt s₁.mem _ _ = _
    rw [hn, m₁]; rfl
  · have hn : (s.gpr .a2).toNat ≠ 0 := fun h =>
      (beq_eq_false_iff_ne.mp h0) (BitVec.eq_of_toNat_eq h)
    have ctx : LoopCtx (Spec.Idea.scheduleAt s.mem (s.gpr .a0)) (s.gpr .a1) (s.gpr .a2).toNat s₁ := by
      refine ⟨?_, ?_, ?_, ?_, by omega_using [hbound], h0₁⟩
      · rw [e₁.gpr (by decide), e₁.2.1, e₁.2.2, hrd]; simp
      · rw [e₁.2.2, hwr]; simp
      · rw [e₁.gpr (by decide), m₁]
      · rw [e₁.gpr (by decide)]; exact dSched
    refine WP.mono (loop_ok ctx (Nat.pos_of_ne_zero hn) (e₁.gpr (by decide))
      (by rw [e₁.gpr (by decide), ofNat_toNat64]) (m₀ := s.mem) (fun j _ => by rw [m₁]))
      fun t ht => ?_
    show Spec.Idea.blocksAt t.mem (s.gpr .a1) (s.gpr .a2).toNat = _
    exact blocksAt_eq _ _ _ _ _ ht.done

theorem ecb_correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa ecb s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨tr, s', he, ⟨hp, hk⟩⟩ := WP.keep ecbWrites (ecb_wp s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

theorem ecb_ct : ConstantTime isa contract.pre contract.pub ecb := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

def ecbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 1 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩]

theorem ecb_verified : Verified RISCV64.target ecb (Spec.Idea.ecbContract RISCV64.abi) :=
  Verified.of_correct ecb_correct ecb_ct (by
    sig_implies [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, RISCV64.abi, RISCV64.argRegs, contract]
      [ecbSat] using ecbSat)

end VG.Proof.Idea.RISCV64
