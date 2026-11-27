module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Idea.Memory32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Idea.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Idea.Memory32
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.PPC64LE.Lit
public import VerifiedGarbage.Proof.Idea.Arith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Idea.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Spec.Idea
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Idea.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Spec.Idea
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `Idea.PPC64LE.Block`, which this module and modules that import it used -/

section

/-! ### `Idea.PPC64LE.Mul`, which only this module used -/

section

/-!
# IDEA on PPC64LE: ⊙ without branches

`mul_ok`: `mulCode` leaves `r11 ⊙ r12` (of their low 16 bits) in `r12`,
with the mask `0xffff` in `r0`, and changes nothing but `r11` and `r12`.
The arithmetic is the shared `prep_toNat` (the operands' residues) and
`reduce` (the product modulo 2¹⁶ + 1 from its halves, corrected by the sign
of their difference).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE

/-- A product of 64-bit values that does not wrap around. -/
theorem mul_ofNat (a b : BitVec 64) (_h : a.toNat * b.toNat < 2 ^ 64) :
    a * b = BitVec.ofNat 64 (a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]

theorem mul_ok (s : State) (h0 : s.gpr .r0 = 65535) :
    WP isa (.block mulCode) s fun t =>
      t.gpr .r12 = (Spec.Idea.mul ((s.gpr .r11).setWidth 16) ((s.gpr .r12).setWidth 16)).setWidth 64 ∧
      t.mem = s.mem := by
  unfold mulCode
  crunr [h0]
  have hA : ((s.gpr .r11 - 1#64 &&& 65535#64) + 1#64).toNat =
      Spec.Idea.residue ((s.gpr .r11).setWidth 16) := prep_toNat _ 65535#64 rfl
  have hB : ((s.gpr .r12 - 1#64 &&& 65535#64) + 1#64).toNat =
      Spec.Idea.residue ((s.gpr .r12).setWidth 16) := prep_toNat _ 65535#64 rfl
  have hp := Nat.mul_le_mul (residue_le ((s.gpr .r11).setWidth 16)) (residue_le ((s.gpr .r12).setWidth 16))
  rw [mul_ofNat _ _ (by rw [hA, hB]; exact Nat.lt_of_le_of_lt hp (by decide)), hA, hB, mul_toNat]
  exact reduce _ (Nat.le_trans hp (by decide)) 65535#64 rfl

end VG.Proof.Idea.PPC64LE

end

end

/-! ### `Idea.PPC64LE.Round`, which this module and modules that import it used -/

section

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
  obtain h1 : WP isa (.block [mov .r11 r, .load .w .r12 .r3 d]) s fun u =>
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

/-- Subkey `6j + i` of a round, at its offset. -/
theorem key_at {z : Spec.Idea.Schedule} {s : State} (hk : KeyOk z s) (j i : Nat) (h : 6 * j + i ≤ 50) :
    InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (12 * j + 2 * i)) 4 ∧
      (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (12 * j + 2 * i)) 32).setWidth 16 = z.getD (6 * j + i) 0 := by
  have := hk.low (6 * j + i) h
  rwa [show 2 * (6 * j + i) = 12 * j + 2 * i by omega_using []] at this

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
  obtain k0 := key_at hk j 0 (by omega_using [hj])
  simp only [Nat.mul_zero, Nat.add_zero] at k0
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok .r6 (12 * j) (by omega_using [hj]) s hk.mask k0.1) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [hx.r6, setWidth_setWidth16, k0.2] at v₁
  obtain hk₁ := hk.keep e₁ m₁ (by decide) (by decide)
  obtain k3 := key_at hk₁ j 3 (by omega_using [hj])
  simp only [Nat.reduceMul] at k3
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok .r9 (12 * j + 6) (by omega_using [hj]) s₁ hk₁.mask k3.1) fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [e₁.gpr (by decide), hx.r9, setWidth_setWidth16, k3.2] at v₂
  obtain hk₂ := hk₁.keep e₂ m₂ (by decide) (by decide)
  obtain k1 := key_at hk₂ j 1 (by omega_using [hj])
  simp only [Nat.mul_one] at k1
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok (r := .r7) (by decide) (12 * j + 2) (by omega_using [hj]) s₂ (x.getD 1 0)
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.r7)) hk₂.mask k1.1)
    fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  rw [k1.2] at v₃
  obtain hk₃ := hk₂.keep e₃ m₃ (by decide) (by decide)
  obtain k2 := key_at hk₃ j 2 (by omega_using [hj])
  simp only [Nat.reduceMul] at k2
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok (r := .r8) (by decide) (12 * j + 4) (by omega_using [hj]) s₃ (x.getD 2 0)
    ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.r8)))
    hk₃.mask k2.1) fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  rw [k2.2] at v₄
  obtain hk₄ := hk₃.keep e₄ m₄ (by decide) (by decide)
  obtain k4 := key_at hk₄ j 4 (by omega_using [hj])
  obtain k5 := key_at hk₄ j 5 (by omega_using [hj])
  simp only [Nat.reduceMul] at k4 k5
  -- The words through the pieces.
  obtain r6₄ : s₄.gpr .r6 = (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0)).setWidth 64 :=
    (e₄.gpr (by decide)).trans ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans v₁))
  obtain r9₄ : s₄.gpr .r9 = (Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)).setWidth 64 :=
    (e₄.gpr (by decide)).trans ((e₃.gpr (by decide)).trans v₂)
  obtain r7₄ : s₄.gpr .r7 = (x.getD 1 0 + z.getD (6 * j + 1) 0).setWidth 64 :=
    (e₄.gpr (by decide)).trans v₃
  have r8₄ : s₄.gpr .r8 = (x.getD 2 0 + z.getD (6 * j + 2) 0).setWidth 64 := v₄
  rw [WP.block_append_iff]
  obtain h5 : WP isa (.block [.logic .xor .r11 .r6 .r8, .load .w .r12 .r3 (12 * j + 8)]) s₄ fun u =>
      u.gpr .r11 = s₄.gpr .r6 ^^^ s₄.gpr .r8 ∧
      u.gpr .r12 = (s₄.mem.readW (s₄.gpr .r3 + BitVec.ofNat 64 (12 * j + 8)) 32).setWidth 64 ∧
      u.mem = s₄.mem ∧ Keep [.r11, .r12] s₄ u := by
    refine WP.mono (WP.keep (c := .block [.logic .xor .r11 .r6 .r8, .load .w .r12 .r3 (12 * j + 8)])
      [.r11, .r12] (Q := fun u => u.gpr .r11 = s₄.gpr .r6 ^^^ s₄.gpr .r8 ∧
      u.gpr .r12 = (s₄.mem.readW (s₄.gpr .r3 + BitVec.ofNat 64 (12 * j + 8)) 32).setWidth 64 ∧
      u.mem = s₄.mem) ?_ writes_only rfl) fun u ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    irun [k4.1, show 12 * j + 8 < 2 ^ 15 by omega_using [hj]]
  refine WP.mono h5 fun s₅ ⟨a₅, d₅, m₅, e₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep s₅ ((e₅.gpr (by decide)).trans hk₄.mask)) fun s₆ ⟨v₆, m₆, e₆⟩ => ?_
  obtain hm₆ : s₆.mem = s₄.mem := m₆.trans m₅
  obtain t₀ : s₆.gpr .r12 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
      (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
    rw [v₆, a₅, d₅, r6₄, r8₄, xor_setWidth, setWidth_setWidth16, lo16, k4.2]
  obtain e₄₆ : Keep [.r11, .r12] s₄ s₆ := (e₅.trans e₆).mono (by decide)
  obtain hk₆ : KeyOk z s₆ := hk₄.keep e₄₆ hm₆ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (p6_ok s₆ (12 * j + 10) (by omega_using [hj]) (by
    rw [e₄₆.2.1, e₄₆.2.2, e₄₆.gpr (by decide)]; exact k5.1)) fun s₇ ⟨b₇, a₇, d₇, m₇, e₇⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep s₇ ((e₇.gpr (by decide)).trans hk₆.mask)) fun s₈ ⟨v₈, m₈, e₈⟩ => ?_
  obtain t₁ : s₈.gpr .r12 = (Spec.Idea.mul (((x.getD 1 0 + z.getD (6 * j + 1) 0) ^^^
      Spec.Idea.mul (x.getD 3 0) (z.getD (6 * j + 3) 0)) +
      Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
        (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0))
      (z.getD (6 * j + 5) 0)).setWidth 64 := by
    rw [v₈, a₇, d₇, e₄₆.gpr (by decide), e₄₆.gpr (by decide), r7₄, r9₄, t₀, xor_setWidth,
      add_setWidth, lo16, e₄₆.gpr (by decide), hm₆, k5.2]
  obtain e₆₈ : Keep [.r10, .r11, .r12] s₆ s₈ := (e₇.trans e₈).mono (by decide)
  obtain r10₈ : s₈.gpr .r10 = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (z.getD (6 * j) 0) ^^^
      (x.getD 2 0 + z.getD (6 * j + 2) 0)) (z.getD (6 * j + 4) 0)).setWidth 64 := by
    rw [e₈.gpr (by decide), b₇, t₀]
  obtain g₈ : ∀ r ∈ [Reg.r6, .r7, .r8, .r9], s₈.gpr r = s₄.gpr r := by
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

end

end

/-!
# IDEA on PPC64LE: a block

`cryptBlock_ok`: `Impl.Idea.PPC64LE.cryptBlock` replaces the block at `r4`
with `Spec.Idea.cryptBlock` of it under the subkeys at `r3`: the block's
words are loaded a byte at a time (`load_ok`), run through the rounds
(`rounds_ok`) and the output transformation (`output_ok`), and stored a
byte at a time (`store_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE

/-! ## Loading -/

theorem loadWord_ok {r : Reg} (hr : r ≠ .r11 ∧ r ≠ .r4) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .r4 = a)
    (h0 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k)) 1)
    (h1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k + 1)) 1) :
    WP isa (.block (loadWord r k)) s fun t =>
      t.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++ s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.r11, r] s t := by
  refine WP.mono (WP.keep (c := .block (loadWord r k)) [.r11, r] (Q := fun t =>
      t.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++
        s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      t.mem = s.mem) ?_ (by simp [writesOnly, Code.allInstrs_eq, instrs, loadWord, dstOf]) rfl)
    fun t ⟨⟨h₁, h₂⟩, hk⟩ => ⟨h₁, h₂, hk⟩
  unfold loadWord
  irun [ha, h0, h1, hr.1, Ne.symm hr.1, hr.2, Ne.symm hr.2, show 2 * k < 2 ^ 15 by omega_using [hk], show 2 * k + 1 < 2 ^ 15 by omega_using [hk]]
  exact bytes16 _ _

/-- The bytes of the block at `a` can be read. -/
def BlockRead (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1

theorem BlockRead.keep {rs : List Reg} {s s' : State} {a : Addr} (h : BlockRead s a)
    (hk : Keep rs s s') : BlockRead s' a := by
  intro i hi; rw [hk.2.1, hk.2.2]; exact h i hi

theorem load_ok (s : State) {a : Addr} (ha : s.gpr .r4 = a) (hb : BlockRead s a) :
    WP isa (.block load) s fun t =>
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem a)) t ∧ t.mem = s.mem ∧
      Keep [.r11, .r6, .r7, .r8, .r9] s t := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem a hk
  simp only [load, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .r6) (by decide) 0 (by decide) s ha (hb _ (by decide))
    (hb _ (by decide))) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .r7) (by decide) 1 (by decide) s₁ ((e₁.gpr (by decide)).trans ha)
    ((hb.keep e₁) _ (by decide)) ((hb.keep e₁) _ (by decide))) fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .r8) (by decide) 2 (by decide) s₂
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans ha))
    ((hb.keep e₁ |>.keep e₂) _ (by decide)) ((hb.keep e₁ |>.keep e₂) _ (by decide)))
    fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  refine WP.mono (loadWord_ok (r := .r9) (by decide) 3 (by decide) s₃
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

/-- The output words: `Y₁` in `r6`, `Y₂` in `r8`, `Y₃` in `r7`, `Y₄` in `r9`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  r6 : s.gpr .r6 = (y.getD 0 0).setWidth 64
  r8 : s.gpr .r8 = (y.getD 1 0).setWidth 64
  r7 : s.gpr .r7 = (y.getD 2 0).setWidth 64
  r9 : s.gpr .r9 = (y.getD 3 0).setWidth 64

theorem hi16 (x : BitVec 32) : ((x.setWidth 64 >>> 16).setWidth 16) = (x >>> 16).setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega_using [] : x.toNat < 2 ^ 64)]

theorem out1_ok (s : State) (hk : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 100) 4) :
    WP isa (.block [mov .r11 .r9, .load .w .r12 .r3 100, .lsr .d .r12 .r12 16]) s fun t =>
      t.gpr .r11 = s.gpr .r9 ∧
      t.gpr .r12 = (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 100) 32).setWidth 64 >>> 16 ∧
      t.mem = s.mem ∧ Keep [.r11, .r12] s t := by
  refine WP.mono (WP.keep [.r11, .r12] (Q := fun t =>
      t.gpr .r11 = s.gpr .r9 ∧
      t.gpr .r12 = (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 100) 32).setWidth 64 >>> 16 ∧
      t.mem = s.mem) ?_ (by decide) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold mov
  irun [hk, BitVec.or_self]

theorem output_ok (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x s)
    (hk : KeyOk z s) :
    WP isa (.block output) s fun t =>
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) t ∧
      t.mem = s.mem ∧ Keep roundWrites s t := by
  simp only [output, List.append_assoc]
  have k48 := hk.low 48 (by decide)
  simp only [Nat.reduceMul] at k48
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok .r6 96 (by decide) s hk.mask k48.1) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [hx.r6, setWidth_setWidth16, k48.2] at v₁
  have hk₁ := hk.keep e₁ m₁ (by decide) (by decide)
  have k₁ := hk₁.low 50 (by decide)
  simp only [Nat.reduceMul] at k₁
  rw [WP.block_append_iff]
  refine WP.mono (out1_ok s₁ k₁.1) fun s₂ ⟨a₂, d₂, m₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep s₂ ((e₂.gpr (by decide)).trans hk₁.mask)) fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  have e₁₃ : Keep [.r11, .r12] s₁ s₃ := (e₂.trans e₃).mono (by decide)
  have hm₃ : s₃.mem = s₁.mem := m₃.trans m₂
  have hk₃ := hk₁.keep e₁₃ hm₃ (by decide) (by decide)
  rw [WP.block_append_iff]
  have h4 : WP isa (.block [mov .r9 .r12]) s₃ fun t => t.gpr .r9 = s₃.gpr .r12 ∧ t.mem = s₃.mem ∧
      Keep [.r9] s₃ t := by
    refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = s₃.gpr .r12 ∧ t.mem = s₃.mem) ?_
      (by decide) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    unfold mov
    irun [BitVec.or_self]
  refine WP.mono h4 fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  have hk₄ := hk₃.keep e₄ m₄ (by decide) (by decide)
  have k49 := hk₄.low 49 (by decide)
  simp only [Nat.reduceMul] at k49
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok (r := .r8) (by decide) 98 (by decide) s₄ (x.getD 2 0)
    ((e₄.gpr (by decide)).trans ((e₁₃.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.r8)))
    hk₄.mask k49.1) fun s₅ ⟨v₅, m₅, e₅⟩ => ?_
  have hk₅ := hk₄.keep e₅ m₅ (by decide) (by decide)
  have k50 := hk₅.low 50 (by decide)
  simp only [Nat.reduceMul] at k50
  refine WP.mono (addKey_ok (r := .r7) (by decide) 100 (by decide) s₅ (x.getD 1 0)
    ((e₅.gpr (by decide)).trans ((e₄.gpr (by decide)).trans ((e₁₃.gpr (by decide)).trans
      ((e₁.gpr (by decide)).trans hx.r7)))) hk₅.mask k50.1) fun s₆ ⟨v₆, m₆, e₆⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by rw [m₆, m₅, m₄, hm₃, m₁], ((((e₁.trans e₁₃).trans e₄).trans e₅).trans e₆).mono (by decide)⟩
  · rw [e₆.gpr (by decide), e₅.gpr (by decide), e₄.gpr (by decide), e₁₃.gpr (by decide), v₁,
      output_getD0]
  · rw [e₆.gpr (by decide), v₅, k49.2, output_getD1]
  · rw [v₆, k50.2, output_getD2]
  · rw [e₆.gpr (by decide), e₅.gpr (by decide), v₄, v₃, a₂, d₂, e₁.gpr (by decide), hx.r9,
      setWidth_setWidth16, hi16, hk₁.last, output_getD3]

/-! ## Storing -/

theorem storeWord_ok (r : Reg) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .r4 = a)
    (h1 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k + 1)) 1)
    (h0 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k)) 1) :
    WP isa (.block (storeWord r k)) s fun t =>
      t.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8) ∧
      Keep [.r11] s t := by
  refine WP.mono (WP.keep (c := .block (storeWord r k)) [.r11] (Q := fun t =>
      t.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8)) ?_
      (by rfl) rfl)
    fun t ⟨h, hk⟩ => ⟨h, hk⟩
  unfold storeWord
  irun [ha, h0, h1, show 2 * k < 2 ^ 15 by omega_using [hk],
    show 2 * k + 1 < 2 ^ 15 by omega_using [hk]]

/-- The bytes of the block at `a` can be written. -/
def BlockWrite (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 i) 1

theorem frame_write1 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.write (a + BitVec.ofNat 64 j) 1 v) :=
  h.write (List.mem_singleton_self _) (n := 1) v (Offset.contains_base a (by omega_using [hj]) (by omega_using [hj]))

theorem store_ok (y : Spec.Idea.State) (s : State) {a : Addr} (ha : s.gpr .r4 = a)
    (hw : BlockWrite s a) (hy : OutHolds y s) :
    WP isa (.block store) s fun t =>
      Spec.Idea.blockAt t.mem a = Spec.Idea.encodeBlock y ∧
      Frame [⟨a, 8⟩] s.mem t.mem ∧ Keep [.r11] s t := by
  simp only [store, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .r6 0 (by decide) s ha (hw _ (by decide))
    (hw _ (by decide))) fun s₁ ⟨m₁, e₁⟩ => ?_
  have ha₁ : s₁.gpr .r4 = a := (e₁.gpr (by decide)).trans ha
  have hw₁ : BlockWrite s₁ a := fun i hi => e₁.2.2 ▸ hw i hi
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .r8 1 (by decide) s₁ ha₁ (hw₁ _ (by decide))
    (hw₁ _ (by decide))) fun s₂ ⟨m₂, e₂⟩ => ?_
  have ha₂ : s₂.gpr .r4 = a := (e₂.gpr (by decide)).trans ha₁
  have hw₂ : BlockWrite s₂ a := fun i hi => e₂.2.2 ▸ hw₁ i hi
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .r7 2 (by decide) s₂ ha₂ (hw₂ _ (by decide))
    (hw₂ _ (by decide))) fun s₃ ⟨m₃, e₃⟩ => ?_
  have ha₃ : s₃.gpr .r4 = a := (e₃.gpr (by decide)).trans ha₂
  have hw₃ : BlockWrite s₃ a := fun i hi => e₃.2.2 ▸ hw₂ i hi
  refine WP.mono (storeWord_ok .r9 3 (by decide) s₃ ha₃ (hw₃ _ (by decide))
    (hw₃ _ (by decide))) fun s₄ ⟨m₄, e₄⟩ => ?_
  have v8 : s₁.gpr .r8 = (y.getD 1 0).setWidth 64 := (e₁.gpr (by decide)).trans hy.r8
  have v7 : s₂.gpr .r7 = (y.getD 2 0).setWidth 64 :=
    (e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hy.r7)
  have v9 : s₃.gpr .r9 = (y.getD 3 0).setWidth 64 :=
    (e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hy.r9))
  rw [v9] at m₄
  rw [v7] at m₃
  rw [v8] at m₂
  rw [hy.r6] at m₁
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

theorem cryptBlock_ok (z : Spec.Idea.Schedule) (s : State) {a : Addr} (ha : s.gpr .r4 = a)
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

end VG.Proof.Idea.PPC64LE

end

end

/-!
# IDEA ECB on PPC64LE

`ecb_verified`: `Impl.Idea.PPC64LE.ecb` meets the shared ECB contract. The
blocks are transformed in a loop (`loop_ok`) whose invariant (`LoopInv`)
says how many remain, that the ones before are transformed and the ones
after not yet; each iteration is `cryptBlock_ok`.
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE

/-- `KeyOk` of the schedule in a readable region at `r3`, with the mask in `r0`. -/
theorem keyOk_of (s : State) (hr : ⟨s.gpr .r3, 104⟩ ∈ s.rd ++ s.wr) (h0 : s.gpr .r0 = 65535) :
    KeyOk (Spec.Idea.scheduleAt s.mem (s.gpr .r3)) s :=
  ⟨fun k hk => ⟨⟨_, hr, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩, subkey_lo32 _ _ (by omega_using [hk])⟩,
    subkey_hi32 _ _, h0⟩

/-! ## The loop -/

/-- The registers the loop writes. -/
abbrev loopWrites : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The facts about the state `o` before the loop that the loop relies on:
the schedule `z` at `r3`, readable, the mask in `r0`, and `n` blocks at `a`,
writable, apart from it and not wrapping around. -/
structure LoopCtx (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (o : State) : Prop where
  sched : ⟨o.gpr .r3, 104⟩ ∈ o.rd ++ o.wr
  data : ⟨a, 8 * n⟩ ∈ o.wr
  z : Spec.Idea.scheduleAt o.mem (o.gpr .r3) = z
  sep : (⟨o.gpr .r3, 104⟩ : Region).Disjoint ⟨a, 8 * n⟩
  bound : 8 * n ≤ 2 ^ 64
  mask : o.gpr .r0 = 65535

/-- `r` blocks remain, at `a + 8 (n - r)` on: the ones before are transformed. -/
structure LoopInv (z : Spec.Idea.Schedule) (a : Addr) (n : Nat) (m₀ : Mem) (o : State) (r : Nat)
    (t : State) : Prop where
  pos : 1 ≤ r
  le : r ≤ n
  r4 : t.gpr .r4 = a + BitVec.ofNat 64 (8 * (n - r))
  r5 : t.gpr .r5 = BitVec.ofNat 64 r
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
    WP isa (.block [.addi .r4 .r4 8, .subi .r5 .r5 1]) s fun t =>
      t.gpr .r4 = s.gpr .r4 + 8#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64 ∧ t.mem = s.mem ∧
      Keep [.r4, .r5] s t := by
  refine WP.mono (WP.keep [.r4, .r5] (Q := fun t =>
      t.gpr .r4 = s.gpr .r4 + 8#64 ∧ t.gpr .r5 = s.gpr .r5 - 1#64 ∧ t.mem = s.mem) ?_ (by decide) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  irun

theorem step_ok {z : Spec.Idea.Schedule} {a : Addr} {n : Nat} {m₀ : Mem} {o : State}
    (hc : LoopCtx z a n o) (r : Nat) (t : State) (hi : LoopInv z a n m₀ o r t) :
    WP isa (.block (cryptBlock ++ ([.addi .r4 .r4 8, .subi .r5 .r5 1] : List Instr))) t
      (fun t' => (isa.eval (.nonzero .d .r5) t' = some false ∧ LoopPost z a n m₀ o t') ∨
        (isa.eval (.nonzero .d .r5) t' = some true ∧ ∃ r' < r, LoopInv z a n m₀ o r' t')) := by
  have hrd : t.rd = o.rd := hi.keep.2.1
  have hwr : t.wr = o.wr := hi.keep.2.2
  have hr3 : t.gpr .r3 = o.gpr .r3 := hi.keep.gpr (by decide)
  have hr0 : t.gpr .r0 = o.gpr .r0 := hi.keep.gpr (by decide)
  have hj : n - r < n := by have := hi.pos; have := hi.le; omega_arith
  have hread : BlockRead t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hrd, hwr]; exact List.mem_append_right _ hc.data, block_contains hj (by omega_using [hi']) (by decide) hc.bound⟩
  have hwrite : BlockWrite t (a + BitVec.ofNat 64 (8 * (n - r))) := fun i hi' =>
    ⟨_, by rw [hwr]; exact hc.data, block_contains hj (by omega_using [hi']) (by decide) hc.bound⟩
  have hz : Spec.Idea.scheduleAt t.mem (t.gpr .r3) = z := by
    rw [hr3, ← hc.z]
    exact scheduleAt_congr (frame_bytes hi.frame (by simpa using hc.sep) (by decide))
  have hk : KeyOk z t := by
    have h := keyOk_of t (by rw [hr3, hrd, hwr]; exact hc.sched) (hr0.trans hc.mask)
    rwa [hz] at h
  rw [WP.block_append_iff]
  refine WP.mono (cryptBlock_ok z t hi.r4 hread hwrite hk) fun t₁ ⟨b₁, f₁, e₁⟩ => ?_
  refine WP.mono (tail_ok t₁) fun t₂ ⟨r4₂, r5₂, m₂, e₂⟩ => ?_
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
  have hr5 : t₂.gpr .r5 = BitVec.ofNat 64 (r - 1) := by
    rw [r5₂, e₁.gpr (by decide), hi.r5]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le; have := hc.bound
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hj]
  by_cases hlast : r = 1
  · subst hlast
    left
    refine ⟨?_, keep₂, frame₂, fun j hjn => done₂ j (by omega_using [hjn])⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hr5]
    rfl
  · right
    refine ⟨?_, r - 1, by have := hi.pos; omega_using [hj], ?_⟩
    · simp only [eval, State.read, BitVec.setWidth_eq, hr5, Option.some.injEq]
      have := hi.pos; have := hi.le; have := hc.bound
      have h : (BitVec.ofNat 64 (r - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, toNat_zero] at this
        omega_arith
      rw [bne, h]; rfl
    · refine ⟨by have := hi.pos; omega_using [hj, hlast], by have := hi.le; omega_using [this], ?_, hr5, keep₂, frame₂, done₂, ?_⟩
      · rw [r4₂, e₁.gpr (by decide), hi.r4, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
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
    (hc : LoopCtx z a n o) (hn : 1 ≤ n) (ho : o.gpr .r4 = a) (hr5 : o.gpr .r5 = BitVec.ofNat 64 n)
    (htodo : ∀ j < n, Spec.Idea.blockAt o.mem (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j))) :
    WP isa (.loop (.block (cryptBlock ++ ([.addi .r4 .r4 8, .subi .r5 .r5 1] : List Instr)))
      (.nonzero .d .r5)) o (LoopPost z a n m₀ o) := by
  refine WP.loop (M := isa) (LoopInv z a n m₀ o) (fun r t hi => step_ok hc r t hi) n o ⟨hn, Nat.le_refl _, ?_,
    hr5, Keep.refl _ _, Frame.refl _ _, fun j hj => by omega, fun j _ hj => htodo j hj⟩
  rw [Nat.sub_self, Nat.mul_zero, ho]; exact (BitVec.add_zero a).symm

/-! ## The function -/

/-- The ECB contract on PPC64LE. -/
def contract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 104⟩
    let data : Region := ⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩
    s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧
      (s.gpr .r4).toNat + 8 * (s.gpr .r5).toNat ≤ 2 ^ 64
  post s s' := Spec.Idea.blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
    Spec.Idea.ecb (Spec.Idea.scheduleAt s.mem (s.gpr .r3))
      (Spec.Idea.blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

/-- The registers `ecb` writes: all volatile. -/
abbrev ecbWrites : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem ecb_wp (s : State) (hs : contract.pre s) :
    WP isa ecb s (fun s' => contract.post s s') := by
  obtain ⟨hrd, hwr, dSched, hbound⟩ := hs
  unfold ecb
  apply WP.seq
  have h1 : WP isa (.block setMask) s fun t => t.gpr .r0 = 65535 ∧ t.mem = s.mem ∧
      Keep [.r0] s t := by
    refine WP.mono (WP.keep [.r0] (Q := fun t => t.gpr .r0 = 65535 ∧ t.mem = s.mem) ?_
      (by decide) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    unfold setMask
    irun
    rfl
  refine WP.mono h1 fun s₁ ⟨h0₁, m₁, e₁⟩ => ?_
  refine WP.ite ((s.gpr .r5) == 0) (by simp only [eval, State.read, BitVec.setWidth_eq,
    e₁.gpr (show Reg.r5 ∉ [Reg.r0] by decide)]) (fun h0 => ?_) (fun h0 => ?_)
  · -- No blocks.
    have hn : s.gpr .r5 = 0 := beq_iff_eq.mp h0
    refine WP.block_nil ?_
    show Spec.Idea.blocksAt s₁.mem _ _ = _
    rw [hn, m₁]; rfl
  · have hn : (s.gpr .r5).toNat ≠ 0 := fun h =>
      (beq_eq_false_iff_ne.mp h0) (BitVec.eq_of_toNat_eq h)
    have ctx : LoopCtx (Spec.Idea.scheduleAt s.mem (s.gpr .r3)) (s.gpr .r4) (s.gpr .r5).toNat s₁ := by
      refine ⟨?_, ?_, ?_, ?_, by omega_using [hbound], h0₁⟩
      · rw [e₁.gpr (by decide), e₁.2.1, e₁.2.2, hrd]; simp
      · rw [e₁.2.2, hwr]; simp
      · rw [e₁.gpr (by decide), m₁]
      · rw [e₁.gpr (by decide)]; exact dSched
    refine WP.mono (loop_ok ctx (Nat.pos_of_ne_zero hn) (e₁.gpr (by decide))
      (by rw [e₁.gpr (by decide), ofNat_toNat64]) (m₀ := s.mem) (fun j _ => by rw [m₁]))
      fun t ht => ?_
    show Spec.Idea.blocksAt t.mem (s.gpr .r4) (s.gpr .r5).toNat = _
    exact blocksAt_eq _ _ _ _ _ ht.done

theorem ecb_correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa ecb s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨tr, s', he, ⟨hp, hk⟩⟩ := WP.keep ecbWrites (ecb_wp s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp⟩

theorem ecb_ct : ConstantTime isa contract.pre contract.pub ecb := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

def ecbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 1 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩]

theorem ecb_verified : Verified target ecb (Spec.Idea.ecbContract abi) :=
  Verified.of_correct ecb_correct ecb_ct (by
    sig_implies [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, abi, argRegs, contract]
      [ecbSat] using ecbSat)

end VG.Proof.Idea.PPC64LE
