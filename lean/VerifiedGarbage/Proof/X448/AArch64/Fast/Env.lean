module

public import VerifiedGarbage.Impl.Curve448.AArch64.Fast
public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Bounds
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Prelude
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.X448.Field
public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
public import VerifiedGarbage.Proof.Curve448.AArch64.Stage
public import VerifiedGarbage.Proof.Curve448.AArch64.Swap
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Proof.X448.Wide.Pass
public import VerifiedGarbage.Proof.X448.Wide.Pack
public import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
public import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.X448.AArch64.Carry
public import VerifiedGarbage.Proof.X448.AArch64.Copy
public import VerifiedGarbage.Proof.X448.AArch64.Mul
public import VerifiedGarbage.Proof.X448.AArch64.Step
public import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
public import VerifiedGarbage.Proof.X448.Wide.Fold
public import VerifiedGarbage.Proof.X448.Wide.Term
public import VerifiedGarbage.Impl.X448.AArch64
public import VerifiedGarbage.Proof.X448.Limbs
public import Batteries.Logic
public import VerifiedGarbage.Impl.X448.AArch64.Symmetric
public import VerifiedGarbage.Proof.X448.Wide.CacheRegs
public import VerifiedGarbage.Proof.X448.Wide.Memory
public import VerifiedGarbage.Proof.X448.Wide.Product
public import VerifiedGarbage.Proof.X448.Wide.Word
public import VerifiedGarbage.Proof.X448.Wide.Column
public import VerifiedGarbage.Proof.X448.AArch64.Swap
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Finish
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.X448.Wide.Limbs

/-! ### `Curve448.AArch64.Fast.Butterfly`, which this module and modules that import it used -/

section

/-! ### `Curve448.AArch64.Fast.Sub`, which this module and modules that import it used -/

section

/-! ### `Curve448.AArch64.Fast.Limbwise`, which only this module used -/

section

/-!
# Limb-by-limb operations

Untrusted: everything here is checked by Lean. `limbs_loop`: eight steps,
step `i` writing limb `i` of each output slot from the unchanged inputs.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs)

/-- Byte `x` is outside every output slot (64 bytes from each of `outs`). -/
def Away (base : Addr) (outs : List Nat) (n : Nat) (x : Addr) : Prop :=
  ∀ o ∈ outs, ofs base x < o ∨ o + n ≤ ofs base x

theorem word_congr {base : Addr} {m m' : Mem} {d : Nat} (hd : d + 8 ≤ 8192)
    (h : ∀ x, d ≤ ofs base x → ofs base x < d + 8 → m' x = m x) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])]; omega_using [])
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])]; omega_using [hi])).symm).symm

theorem limbs_loop {base : Addr} {body : Nat → List Instr} {outs : List Nat} {rs : List Reg}
    (P : State → Prop) (hP : ∀ t u, P t → Keeps rs t u → P u) (hrs : .x3 ∉ rs ∧ .x12 ∉ rs)
    (V : Nat → Nat → BitVec 64) (s : State)
    (hstep : ∀ i < 8, ∀ t, Scr t base → P t → (∀ x, Away base outs 64 x → t.mem x = s.mem x) →
      WP isa (.block (body i)) t fun u =>
        (∀ o ∈ outs, word u.mem base (o + 8 * i) = V o i) ∧
        (∀ x, (∀ o ∈ outs, ofs base x < o + 8 * i ∨ o + 8 * i + 8 ≤ ofs base x) → u.mem x = t.mem x) ∧
        Keeps rs t u)
    (hw : ∀ o ∈ outs, o + 64 ≤ 8192) (sep : ∀ o ∈ outs, ∀ o' ∈ outs, o ≠ o' → o + 64 ≤ o' ∨ o' + 64 ≤ o)
    (hs : Scr s base) (hP0 : P s) :
    WP isa (.block ((List.range 8).flatMap body)) s fun t =>
      (∀ o ∈ outs, ∀ i < 8, word t.mem base (o + 8 * i) = V o i) ∧
      (∀ x, Away base outs 64 x → t.mem x = s.mem x) ∧ Keeps rs s t := by
  let inv := fun n (t : State) =>
    Scr t base ∧ P t ∧ (∀ o ∈ outs, ∀ i < n, word t.mem base (o + 8 * i) = V o i) ∧
      (∀ x, (∀ o ∈ outs, ofs base x < o ∨ o + 8 * n ≤ ofs base x) → t.mem x = s.mem x) ∧
      Keeps rs s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨ts, tp, tv, tm, tk⟩ => ?_) 8
    (by decide) s ⟨hs, hP0, fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, Keeps.refl _ _⟩)
    fun t ⟨_, _, tv, tm, tk⟩ => ⟨tv, fun x hx => tm x hx, tk⟩
  refine WP.mono (hstep n hn t ts tp (fun x hx => tm x fun o ho => by
    have := hx o ho; omega_using [hn, this])) fun u ⟨uv, um, uk⟩ => ⟨ts.of_keeps uk hrs, hP t u tp uk, ?_, ?_, tk.trans uk⟩
  · intro o ho i hi
    by_cases h : i = n
    · subst h; exact uv o ho
    · rw [← tv o ho i (by omega_using [hi, h])]
      have ho64 := hw o ho
      refine word_congr (by omega_using [hn, hi, ho64]) fun x h1 h2 => um x fun o' ho' => ?_
      by_cases e : o' = o
      · subst e; omega_using [hi, h, h2]
      · have := sep o ho o' ho' (Ne.symm e)
        omega_using [hn, hi, h1, h2, this]
  · intro x hx
    rw [um x (fun o ho => by have := hx o ho; omega_using [this]), tm x (fun o ho => by have := hx o ho; omega_using [this])]

end VG.Proof.Curve448.AArch64.Fast

end

end


/-!
# Differences and sums

Untrusted: everything here is checked by Lean. `sub o a b` writes
`a + 2p - b` limb by limb, and `addSub` also `a + b`.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq)
open VG.Proof.Ed25519.AArch64 (read_x)

def K2 : BitVec 64 := BitVec.ofNat 64 (2 ^ 57 - 2)
def K4 : BitVec 64 := BitVec.ofNat 64 (2 ^ 57 - 4)

def twoPW (i : Nat) : BitVec 64 := if i = 4 then K4 else K2

theorem twoPRegs_ok (s : State) :
    WP isa (.block twoPRegs) s fun t =>
      t.gpr .x0 = K2 ∧ t.gpr .x2 = K4 ∧ t.mem = s.mem ∧ Keeps [.x0, .x2] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [twoPRegs, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide,
      show 16 * 2 < 64 from by decide, show 16 * 3 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [State.read, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem twoPReg_val {t : State} (h0 : t.gpr .x0 = K2) (h2 : t.gpr .x2 = K4) (i : Nat) :
    t.gpr (twoPReg i) = twoPW i := by
  simp only [twoPReg, twoPW]; split <;> with_reducible assumption

/-- Load two words, from the working space. -/
theorem ld2 {t : State} {base : Addr} (ht : Scr t base) {d e : Nat} (hd : d % 8 = 0) (hd' : d + 8 ≤ 8192)
    (he : e % 8 = 0) (he' : e + 8 ≤ 8192) :
    InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 d) 8 ∧
      (d % 8 = 0 ∧ d < 4096 * 8) ∧ InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 e) 8 ∧
      (e % 8 = 0 ∧ e < 4096 * 8) :=
  ⟨ht.read hd', ⟨hd, by omega_arith⟩, ht.read he', ⟨he, by omega_arith⟩⟩

theorem subStep_ok {t : State} {base : Addr} (ht : Scr t base) {o a b i : Nat} (hi : i < 8)
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (h0 : t.gpr .x0 = K2) (h2 : t.gpr .x2 = K4) :
    WP isa (.block [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 (twoPReg i),
      .sub .x .x4 .x4 .x5, st .x4 (o + 8 * i)]) t fun u =>
      u.mem = t.mem.writeW (off base (o + 8 * i))
        (word t.mem base (a + 8 * i) + twoPW i - word t.mem base (b + 8 * i)) ∧
      Keeps [.x4, .x5] t u := by
  obtain ⟨ra, aa, rb, ab⟩ := ld2 ht (d := a + 8 * i) (e := b + 8 * i) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)
  have wo := ht.write (d := o + 8 * i) (n := 8) (by omega_arith)
  have ao : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 4096 * 8 := ⟨by omega_arith, by omega_arith⟩
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 := by simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, aa, ab, ao, ra, rb, wo, and_self,
      Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · simp only [tw.1, tw.2, ite_false, BitVec.setWidth_eq, write8_eq, read8_eq, twoPReg_val h0 h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem away_word {base : Addr} {outs : List Nat} {m m' : Mem}
    (h : ∀ x, Away base outs 64 x → m' x = m x) {d : Nat} (hd : d + 8 ≤ 8192)
    (ho : ∀ o ∈ outs, d + 8 ≤ o ∨ o + 64 ≤ d) : word m' base d = word m base d :=
  word_congr hd fun x h1 h2 => h x fun o h' => by have := ho o h'; omega_arith

theorem writeW_frame {base : Addr} (m : Mem) {d : Nat} (hd : d + 8 ≤ 8192) (v : BitVec 64) (x : Addr)
    (hx : ofs base x < d ∨ d + 8 ≤ ofs base x) : (m.writeW (off base d) v) x = m x :=
  writeW_outside m base v hd x hx

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hoa : o + 64 ≤ a ∨ a + 64 ≤ o) (hob : o + 64 ≤ b ∨ b + 64 ≤ o) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.sub o a b)) s fun t =>
      (∀ i < 8, word t.mem base (o + 8 * i) =
        word s.mem base (a + 8 * i) + twoPW i - word s.mem base (b + 8 * i)) ∧
      (∀ x, Away base [o] 64 x → t.mem x = s.mem x) ∧ Keeps [.x0, .x2, .x4, .x5] s t := by
  rw [Impl.Curve448.AArch64.Fast.sub, WP.block_append_iff]
  refine WP.mono (twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have := limbs_loop (base := base) (outs := [o]) (rs := [.x4, .x5])
    (body := fun i => [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 (twoPReg i),
      .sub .x .x4 .x4 .x5, st .x4 (o + 8 * i)])
    (fun u => u.gpr .x0 = K2 ∧ u.gpr .x2 = K4)
    (fun u v ⟨h0, h2⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2⟩) (by decide)
    (fun _ i => word t.mem base (a + 8 * i) + twoPW i - word t.mem base (b + 8 * i)) t
    (fun i hi u us ⟨h0, h2⟩ hm => WP.mono (subStep_ok us hi ho ha hb ho8 ha8 hb8 h0 h2)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'; subst ho'
          rw [wm, word, Mem.readW_writeW_self64, away_word hm (by omega_arith) (by simp; omega_using [hi, hoa]),
            away_word hm (by omega_arith) (by simp; omega_using [hi, hob])],
        fun x hx => by rw [wm]; exact writeW_frame _ (by omega_arith) _ x (hx o (by simp)), wk⟩)
    (by simp; omega_using [ho]) (by simp) ts ⟨t0, t2⟩
  refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun i hi => by rw [uv o (by simp) i hi, tm], fun x hx => by
    rw [um x hx, tm], (tk.mono (by decide)).trans (uk.mono (by decide))⟩

theorem addSubStep_ok {t : State} {base : Addr} (ht : Scr t base) {o₁ o₂ a b i : Nat} (hi : i < 8)
    (ho₁ : o₁ + 64 ≤ 8192) (ho₂ : o₂ + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ho₁8 : o₁ % 8 = 0) (ho₂8 : o₂ % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (h0 : t.gpr .x0 = K2) (h2 : t.gpr .x2 = K4) :
    WP isa (.block [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x6 .x4 .x5, st .x6 (o₁ + 8 * i),
      .add .x .x7 .x4 (twoPReg i), .sub .x .x7 .x7 .x5, st .x7 (o₂ + 8 * i)]) t fun u =>
      u.mem = (t.mem.writeW (off base (o₁ + 8 * i))
        (word t.mem base (a + 8 * i) + word t.mem base (b + 8 * i))).writeW (off base (o₂ + 8 * i))
        (word t.mem base (a + 8 * i) + twoPW i - word t.mem base (b + 8 * i)) ∧
      Keeps [.x4, .x5, .x6, .x7] t u := by
  obtain ⟨ra, aa, rb, ab⟩ := ld2 ht (d := a + 8 * i) (e := b + 8 * i) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)
  have wo₁ := ht.write (d := o₁ + 8 * i) (n := 8) (by omega_arith)
  have wo₂ := ht.write (d := o₂ + 8 * i) (n := 8) (by omega_arith)
  have ao₁ : (o₁ + 8 * i) % 8 = 0 ∧ o₁ + 8 * i < 4096 * 8 := ⟨by omega_arith, by omega_arith⟩
  have ao₂ : (o₂ + 8 * i) % 8 = 0 ∧ o₂ + 8 * i < 4096 * 8 := ⟨by omega_arith, by omega_arith⟩
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 ∧ twoPReg i ≠ .x6 ∧ twoPReg i ≠ .x7 := by
    simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, aa, ab, ao₁, ao₂, ra, rb, wo₁, wo₂,
      and_self, Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · simp only [tw.1, tw.2.1, tw.2.2.1, ite_false, BitVec.setWidth_eq, write8_eq, read8_eq,
      twoPReg_val h0 h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, ite_false]

theorem addSub_ok {s : State} {base : Addr} (hs : Scr s base) {o₁ o₂ a b : Nat}
    (ho₁ : o₁ + 64 ≤ 8192) (ho₂ : o₂ + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ho₁8 : o₁ % 8 = 0) (ho₂8 : o₂ % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (h12 : o₁ + 64 ≤ o₂ ∨ o₂ + 64 ≤ o₁) (h1a : o₁ + 64 ≤ a ∨ a + 64 ≤ o₁)
    (h1b : o₁ + 64 ≤ b ∨ b + 64 ≤ o₁) (h2a : o₂ + 64 ≤ a ∨ a + 64 ≤ o₂)
    (h2b : o₂ + 64 ≤ b ∨ b + 64 ≤ o₂) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.addSub o₁ o₂ a b)) s fun t =>
      (∀ i < 8, word t.mem base (o₁ + 8 * i) = word s.mem base (a + 8 * i) + word s.mem base (b + 8 * i)) ∧
      (∀ i < 8, word t.mem base (o₂ + 8 * i) =
        word s.mem base (a + 8 * i) + twoPW i - word s.mem base (b + 8 * i)) ∧
      (∀ x, Away base [o₁, o₂] 64 x → t.mem x = s.mem x) ∧ Keeps [.x0, .x2, .x4, .x5, .x6, .x7] s t := by
  rw [Impl.Curve448.AArch64.Fast.addSub, WP.block_append_iff]
  refine WP.mono (twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have ne : o₁ ≠ o₂ := by omega_arith
  have := limbs_loop (base := base) (outs := [o₁, o₂]) (rs := [.x4, .x5, .x6, .x7])
    (body := fun i => [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x6 .x4 .x5, st .x6 (o₁ + 8 * i),
      .add .x .x7 .x4 (twoPReg i), .sub .x .x7 .x7 .x5, st .x7 (o₂ + 8 * i)])
    (fun u => u.gpr .x0 = K2 ∧ u.gpr .x2 = K4)
    (fun u v ⟨h0, h2⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2⟩) (by decide)
    (fun o i => if o = o₁ then word t.mem base (a + 8 * i) + word t.mem base (b + 8 * i)
      else word t.mem base (a + 8 * i) + twoPW i - word t.mem base (b + 8 * i)) t
    (fun i hi u us ⟨h0, h2⟩ hm => WP.mono (addSubStep_ok us hi ho₁ ho₂ ha hb ho₁8 ho₂8 ha8 hb8 h0 h2)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => by
          have ea := away_word hm (d := a + 8 * i) (by omega_arith) (by simp; omega_using [hi, h1a, h2a])
          have eb := away_word hm (d := b + 8 * i) (by omega_arith) (by simp; omega_using [hi, h1b, h2b])
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
          rcases ho' with rfl | rfl
          · rw [wm, VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ (by omega_arith) (by omega_arith) (by omega_arith),
              ite_eq_right (by omega_arith), word, Mem.readW_writeW_self64, ite_eq_left rfl, ea, eb]
          · rw [wm, word, Mem.readW_writeW_self64, ite_eq_right (Ne.symm ne), ea, eb],
        fun x hx => by
          rw [wm, writeW_frame _ (by omega_arith) _ x (hx o₂ (by simp)),
            writeW_frame _ (by omega_arith) _ x (hx o₁ (by simp))], wk⟩)
    (by simp; omega_using [ho₁, ho₂]) (by simp; omega_using [h12]) ts ⟨t0, t2⟩
  refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun i hi => ?_, fun i hi => ?_, fun x hx => by
    rw [um x hx, tm], (tk.mono (by decide)).trans (uk.mono (by decide))⟩
  · rw [uv o₁ (by simp) i hi, ite_eq_left rfl, tm]
  · rw [uv o₂ (by simp) i hi, ite_eq_right (Ne.symm ne), tm]

end VG.Proof.Curve448.AArch64.Fast

end

end

/-!
# The ladder's sums and differences, of conditionally swapped coordinates

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq mask xor_sel)
open VG.Proof.Ed25519.AArch64 (read_x)

def bflyBody (x2 z2 x3 z3 a b c d i : Nat) : List Instr :=
  [ld .x4 (x2 + 8 * i), ld .x7 (x3 + 8 * i), ld .x5 (z2 + 8 * i), ld .x8 (z3 + 8 * i),
    .logic .eor .x .x9 .x4 .x7, .logic .and .x .x9 .x9 .x6,
    .logic .eor .x .x4 .x4 .x9, .logic .eor .x .x7 .x7 .x9,
    .logic .eor .x .x9 .x5 .x8, .logic .and .x .x9 .x9 .x6,
    .logic .eor .x .x5 .x5 .x9, .logic .eor .x .x8 .x8 .x9,
    .add .x .x9 .x4 .x5, st .x9 (a + 8 * i),
    .add .x .x10 .x4 (twoPReg i), .sub .x .x10 .x10 .x5, st .x10 (b + 8 * i),
    .add .x .x11 .x7 .x8, st .x11 (c + 8 * i),
    .add .x .x13 .x7 (twoPReg i), .sub .x .x13 .x13 .x8, st .x13 (d + 8 * i)]

theorem butterfly_split (x2 z2 x3 z3 a b c d : Nat) :
    butterfly x2 z2 x3 z3 a b c d = twoPRegs ++ (List.range 8).flatMap (bflyBody x2 z2 x3 z3 a b c d) :=
  rfl

/-- The swapped words. -/
def sel (sw : Bool) (p q : BitVec 64) : BitVec 64 := if sw then q else p

theorem bflyStep_ok {t : State} {base : Addr} (ht : Scr t base) {x2 z2 x3 z3 a b c d i : Nat}
    (hi : i < 8) (h : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], e + 64 ≤ 8192 ∧ e % 8 = 0)
    (h0 : t.gpr .x0 = K2) (h2 : t.gpr .x2 = K4) {sw : Bool} (hm : t.gpr .x6 = mask sw) :
    WP isa (.block (bflyBody x2 z2 x3 z3 a b c d i)) t fun u =>
      let X2 := sel sw (word t.mem base (x2 + 8 * i)) (word t.mem base (x3 + 8 * i))
      let X3 := sel sw (word t.mem base (x3 + 8 * i)) (word t.mem base (x2 + 8 * i))
      let Z2 := sel sw (word t.mem base (z2 + 8 * i)) (word t.mem base (z3 + 8 * i))
      let Z3 := sel sw (word t.mem base (z3 + 8 * i)) (word t.mem base (z2 + 8 * i))
      u.mem = (((t.mem.writeW (off base (a + 8 * i)) (X2 + Z2)).writeW (off base (b + 8 * i))
        (X2 + twoPW i - Z2)).writeW (off base (c + 8 * i)) (X3 + Z3)).writeW (off base (d + 8 * i))
        (X3 + twoPW i - Z3) ∧
      Keeps [.x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13] t u := by
  have g : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], (e + 8 * i) % 8 = 0 ∧ e + 8 * i < 4096 * 8 ∧
      InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 (e + 8 * i)) 8 ∧
      InRegions t.wr (base + BitVec.ofNat 64 (e + 8 * i)) 8 := fun e he => by
    have := h e he
    exact ⟨by omega_using [this], by omega_using [hi, this], ht.read (by omega_using [hi, this]), ht.write (by omega_using [hi, this])⟩
  obtain ⟨ax2, bx2, rx2, -⟩ := g x2 (by simp)
  obtain ⟨az2, bz2, rz2, -⟩ := g z2 (by simp)
  obtain ⟨ax3, bx3, rx3, -⟩ := g x3 (by simp)
  obtain ⟨az3, bz3, rz3, -⟩ := g z3 (by simp)
  obtain ⟨aa, ba, -, wa⟩ := g a (by simp)
  obtain ⟨ab, bb, -, wb⟩ := g b (by simp)
  obtain ⟨ac, bc, -, wc⟩ := g c (by simp)
  obtain ⟨ad, bd, -, wd⟩ := g d (by simp)
  have tw : twoPReg i ≠ .x4 ∧ twoPReg i ≠ .x5 ∧ twoPReg i ≠ .x7 ∧ twoPReg i ≠ .x8 ∧
      twoPReg i ≠ .x9 ∧ twoPReg i ≠ .x10 ∧ twoPReg i ≠ .x11 := by
    simp only [twoPReg]; split <;> decide
  refine WP.of_runBlock ⟨_, by
    simp only [bflyBody, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      State.load, State.store, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, reduceCtorEq, ite_true, ite_false, ht.x3, ax2, bx2, ax3, bx3, az2, bz2, az3, bz3,
      aa, ba, ab, bb, ac, bc, ad, bd, rx2, rx3, rz2, rz3, wa, wb, wc, wd, and_self, Option.map_some,
      Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, fun q hq => ?_, rfl, rfl⟩
  · have sx := xor_sel sw (word t.mem base (x2 + 8 * i)) (word t.mem base (x3 + 8 * i))
    have sz := xor_sel sw (word t.mem base (z2 + 8 * i)) (word t.mem base (z3 + 8 * i))
    simp only [word, off] at sx sz
    simp only [tw.1, tw.2.1, tw.2.2.1, tw.2.2.2.1, tw.2.2.2.2.1,
      tw.2.2.2.2.2.1, tw.2.2.2.2.2.2, ite_false, BitVec.setWidth_eq, write8_eq,
      read8_eq, word, off, hm, sx.1, sx.2, sz.1, sz.2, twoPReg_val h0 h2, sel]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
    simp only [RegUpd.gpr_write, q1, q2, q3, q4, q5, q6, q7, q8, ite_false]

/-- Slots `x` and `y` (64 bytes each) are disjoint. -/
abbrev Dj (x y : Nat) : Prop := x + 64 ≤ y ∨ y + 64 ≤ x

theorem word_w4 (m : Mem) (base : Addr) {p q r t d : Nat} (v₁ v₂ v₃ v₄ : BitVec 64)
    (hp : p + 8 ≤ 8192) (hq : q + 8 ≤ 8192) (hr : r + 8 ≤ 8192) (ht : t + 8 ≤ 8192) (hd : d + 8 ≤ 8192)
    (sp : d = p ∨ d + 8 ≤ p ∨ p + 8 ≤ d) (sq : d = q ∨ d + 8 ≤ q ∨ q + 8 ≤ d)
    (sr : d = r ∨ d + 8 ≤ r ∨ r + 8 ≤ d) (st' : d = t ∨ d + 8 ≤ t ∨ t + 8 ≤ d) :
    word ((((m.writeW (off base p) v₁).writeW (off base q) v₂).writeW (off base r) v₃).writeW
      (off base t) v₄) base d =
      if d = t then v₄ else if d = r then v₃ else if d = q then v₂ else if d = p then v₁ else
        word m base d := by
  rw [VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ ht hd st',
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hr hd sr,
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hq hd sq,
    VG.Proof.Curve448.AArch64.Fast.word_writeW _ _ hp hd sp]

def bflyV (m : Mem) (base : Addr) (sw : Bool) (x2 z2 x3 z3 a b c : Nat) (o i : Nat) : BitVec 64 :=
  let X2 := sel sw (word m base (x2 + 8 * i)) (word m base (x3 + 8 * i))
  let X3 := sel sw (word m base (x3 + 8 * i)) (word m base (x2 + 8 * i))
  let Z2 := sel sw (word m base (z2 + 8 * i)) (word m base (z3 + 8 * i))
  let Z3 := sel sw (word m base (z3 + 8 * i)) (word m base (z2 + 8 * i))
  if o = a then X2 + Z2 else if o = b then X2 + twoPW i - Z2 else if o = c then X3 + Z3
  else X3 + twoPW i - Z3

theorem butterfly_ok {s : State} {base : Addr} (hs : Scr s base) {x2 z2 x3 z3 a b c d : Nat}
    (h : ∀ e ∈ [x2, z2, x3, z3, a, b, c, d], e + 64 ≤ 8192 ∧ e % 8 = 0)
    (hout : ∀ o ∈ [a, b, c, d], ∀ o' ∈ [a, b, c, d], o ≠ o' → Dj o o')
    (hin : ∀ o ∈ [a, b, c, d], ∀ e ∈ [x2, z2, x3, z3], Dj o e)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (butterfly x2 z2 x3 z3 a b c d)) s fun t =>
      (∀ o ∈ [a, b, c, d], ∀ i < 8, word t.mem base (o + 8 * i) = bflyV s.mem base sw x2 z2 x3 z3 a b c o i) ∧
      (∀ x, Away base [a, b, c, d] 64 x → t.mem x = s.mem x) ∧
      Keeps [.x0, .x2, .x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13] s t := by
  rw [butterfly_split, WP.block_append_iff]
  refine WP.mono (twoPRegs_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have h6 : t.gpr .x6 = mask sw := by rw [tk.1 _ (by decide), hm]
  have hb := fun e (he : e ∈ [x2, z2, x3, z3, a, b, c, d]) => h e he
  have ha' := hb a (by simp); have hb' := hb b (by simp); have hc' := hb c (by simp)
  have hd' := hb d (by simp)
  have dab := hout a (by simp) b (by simp) hab; have dac := hout a (by simp) c (by simp) hac
  have dad := hout a (by simp) d (by simp) had; have dbc := hout b (by simp) c (by simp) hbc
  have dbd := hout b (by simp) d (by simp) hbd; have dcd := hout c (by simp) d (by simp) hcd
  have := limbs_loop (base := base) (outs := [a, b, c, d]) (rs := [.x4, .x5, .x7, .x8, .x9, .x10, .x11, .x13])
    (body := bflyBody x2 z2 x3 z3 a b c d)
    (fun u => u.gpr .x0 = K2 ∧ u.gpr .x2 = K4 ∧ u.gpr .x6 = mask sw)
    (fun u v ⟨h0, h2, h6⟩ k => ⟨(k.1 _ (by decide)).trans h0, (k.1 _ (by decide)).trans h2,
      (k.1 _ (by decide)).trans h6⟩) (by decide)
    (bflyV t.mem base sw x2 z2 x3 z3 a b c) t
    (fun i hi u us ⟨h0, h2, h6⟩ hm' => WP.mono (bflyStep_ok us hi h h0 h2 h6)
      fun w ⟨wm, wk⟩ => ⟨fun o' ho' => ?_, fun x hx => ?_, wk⟩)
    (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> omega_arith) hout ts ⟨t0, t2, h6⟩
  · refine WP.mono this fun u ⟨uv, um, uk⟩ => ⟨fun o ho i hi => ?_, fun x hx => by rw [um x hx, tm],
      (tk.mono (by decide)).trans (uk.mono (by decide))⟩
    rw [uv o ho i hi]; simp only [bflyV, tm]
  · have e : ∀ q ∈ [x2, z2, x3, z3], word u.mem base (q + 8 * i) = word t.mem base (q + 8 * i) := by
      intro q hq
      have := (h q (List.mem_append_left [a, b, c, d] (by exact hq))).1
      exact away_word hm' (by omega_arith) (fun o ho => by have := hin o ho q hq; simp only [Dj] at this; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
    rw [wm]
    rcases ho' with rfl | rfl | rfl | rfl
    all_goals
      rw [word_w4 _ _ _ _ _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
        (by omega_arith) (by omega_arith)]
      simp only [bflyV, e x2 (by simp), e z2 (by simp), e x3 (by simp), e z3 (by simp)]
    all_goals simp only [Nat.add_right_cancel_iff, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm,
      hbc.symm, hbd.symm, hcd.symm, ↓reduceIte]
  · rw [wm]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [writeW_frame _ (by omega_arith) _ x hx.2.2.2, writeW_frame _ (by omega_arith) _ x hx.2.2.1,
      writeW_frame _ (by omega_arith) _ x hx.2.1, writeW_frame _ (by omega_arith) _ x hx.1]

end VG.Proof.Curve448.AArch64.Fast

end

end

/-! ### `Curve448.AArch64.Fast.Field`, which only this module used -/

section

/-! ### `Curve448.AArch64.Fast.Small`, which only this module used -/

section

/-!
# `a + 39081 e`

Untrusted: everything here is checked by Lean. Limb `i` of the result is
`a_i + (39081 e_i mod 2⁵⁶) + c_{i-1}` (and `+ c₇` for limb 4), with
`c_i = ⌊39081 e_i / 2⁵⁶⌋` and `c_{-1} = c₇`.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq)
open VG.Proof.Ed25519.AArch64 (read_x)

def smallRegs : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16, .x17, .x21, .x22, .x23, .x24]

theorem small_mem : ∀ i < 8, smallX i ∈ smallRegs ∧ smallC i ∈ smallRegs := by decide
theorem small_not : ∀ i < 8, smallX i ∉ [Reg.x0, .x2, .x24, .x3, .x12] ∧
    smallC i ∉ [Reg.x0, .x2, .x24, .x3, .x12] ∧ smallX i ≠ smallC i := by decide
theorem small_inj : ∀ i < 8, ∀ j < 8, j ≠ i → smallX j ≠ smallX i ∧ smallC j ≠ smallC i ∧
    smallX j ≠ smallC i ∧ smallC j ≠ smallX i := by decide

/-- The carry of limb `i`. -/
def sc (e : Nat → Nat) (i : Nat) : Nat := 39081 * e i / radix

/-- Limb `i` before the carries. -/
def sl (a e : Nat → Nat) (i : Nat) : Nat := a i + 39081 * e i % radix

theorem smallLimb_val (x e : BitVec 64) (hx : x.toNat + 2 ^ 56 ≤ 2 ^ 64) (he : e.toNat < 2 ^ 59) :
    (x + e * BitVec.ofNat 64 39081 - (BitVec.ofNat 64 (e.toNat * 10004736 / 2 ^ 64) <<< 56)).toNat =
      x.toNat + 39081 * e.toNat % radix ∧
    (BitVec.ofNat 64 (e.toNat * 10004736 / 2 ^ 64)).toNat = 39081 * e.toNat / radix := by
  have hc : e.toNat * 10004736 / 2 ^ 64 = 39081 * e.toNat / radix := by
    simp only [radix]; omega_arith
  rw [hc]
  have hcl : 39081 * e.toNat / radix < 2 ^ 64 := by simp only [radix]; omega_arith
  refine ⟨?_, by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hcl⟩
  generalize hl : 39081 * e.toNat % radix = l
  generalize hcc : 39081 * e.toNat / radix = c at hcl
  have hm : l + radix * c = 39081 * e.toNat := by rw [← hl, ← hcc]; exact Nat.mod_add_div _ _
  have hlt : l < radix := by rw [← hl]; exact Nat.mod_lt _ (by decide)
  have h1 : c * 2 ^ 56 % 2 ^ 64 = c % 2 ^ 8 * 2 ^ 56 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 8 * 2 ^ 56 by decide, Nat.mul_mod_mul_right]
  have h2 : e.toNat * 39081 % 2 ^ 64 = l + c % 2 ^ 8 * 2 ^ 56 := by
    rw [Nat.mul_comm, ← hm]
    simp only [radix] at hlt ⊢
    omega_arith
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hcl,
    show 39081 % 2 ^ 64 = 39081 by decide, h1, h2]
  simp only [radix] at hlt ⊢
  omega_arith

def K39 : BitVec 64 := BitVec.ofNat 64 39081
def K8 : BitVec 64 := BitVec.ofNat 64 10004736

theorem smallConsts_ok (s : State) :
    WP isa (.block [.movz .x .x0 39081 0, .movz .x .x2 0xa900 0, .movk .x .x2 0x0098 1]) s fun t =>
      t.gpr .x0 = K39 ∧ t.gpr .x2 = K8 ∧ t.mem = s.mem ∧ Keeps [.x0, .x2] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; decide
  · simp only [State.read, RegUpd.gpr_write, ite_true]; decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem smallLimbStep_ok {t : State} {base : Addr} (ht : Scr t base) {a e i : Nat} (hi : i < 8)
    (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ha8 : a % 8 = 0) (he8 : e % 8 = 0)
    (h0 : t.gpr .x0 = K39) (h2 : t.gpr .x2 = K8) :
    WP isa (.block (smallLimb a e i)) t fun u =>
      u.gpr (smallX i) = word t.mem base (a + 8 * i) + word t.mem base (e + 8 * i) * K39 -
        (BitVec.ofNat 64 ((word t.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56) ∧
      u.gpr (smallC i) = BitVec.ofNat 64 ((word t.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) ∧
      u.mem = t.mem ∧ Keeps [.x24, smallX i, smallC i] t u := by
  obtain ⟨re, ae, ra, aa⟩ := ld2 ht (d := e + 8 * i) (e := a + 8 * i) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)
  obtain ⟨n1, n2, n3⟩ := small_not i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at n1 n2
  obtain ⟨x0, x2, x24, x3, -⟩ := n1
  obtain ⟨c0, c2, c24, c3, -⟩ := n2
  refine WP.of_runBlock ⟨_, by
    simp only [smallLimb, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      Size.bits, State.load, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, x24, Ne.symm x24, reduceCtorEq, ite_true, ite_false, ht.x3, ae, aa, re, ra, and_self,
      show 56 < 64 from by decide, Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · have k8 : (BitVec.ofNat 64 10004736 : BitVec 64).toNat = 10004736 := rfl
    simp only [RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, x24, 
      n3, Ne.symm x0, Ne.symm x2, read8_eq, h0, h2,
      K8, k8]
  · have k8 : (BitVec.ofNat 64 10004736 : BitVec 64).toNat = 10004736 := rfl
    simp only [RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, c24, 
      Ne.symm n3, n3, Ne.symm x2, read8_eq, h2, K8, k8]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2, ite_false]

theorem smallLoop1_ok {s : State} {base : Addr} (hs : Scr s base) {a e : Nat}
    (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ha8 : a % 8 = 0) (he8 : e % 8 = 0)
    (h0 : s.gpr .x0 = K39) (h2 : s.gpr .x2 = K8) :
    WP isa (.block ((List.range 8).flatMap (smallLimb a e))) s fun t =>
      (∀ i < 8, t.gpr (smallX i) = word s.mem base (a + 8 * i) + word s.mem base (e + 8 * i) * K39 -
        (BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56)) ∧
      (∀ i < 8, t.gpr (smallC i) = BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64)) ∧
      t.mem = s.mem ∧ Keeps smallRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (smallX i) = word s.mem base (a + 8 * i) + word s.mem base (e + 8 * i) * K39 -
      (BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56)) ∧
    (∀ i < n, t.gpr (smallC i) = BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64)) ∧
    t.mem = s.mem ∧ Keeps smallRegs s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tx, tc, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (smallLimbStep_ok ts hn ha he ha8 he8 ((tk.1 _ (by decide)).trans h0)
    ((tk.1 _ (by decide)).trans h2)) fun u ⟨ux, uc, um, uk⟩ => ?_
  have nk : ∀ i < 8, i ≠ n → smallX i ∉ [Reg.x24, smallX n, smallC n] ∧
      smallC i ∉ [Reg.x24, smallX n, smallC n] := by
    intro i hi h
    obtain ⟨q1, q2, -⟩ := small_not i hi
    obtain ⟨r1, r2, r3, r4⟩ := small_inj n hn i hi h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at q1 q2 ⊢
    exact ⟨⟨q1.2.2.1, r1, r3⟩, ⟨q2.2.2.1, r4, r2⟩⟩
  refine ⟨fun i hi => ?_, fun i hi => ?_, um.trans tm, tk.trans (uk.mono fun r hr => ?_)⟩
  · by_cases h : i = n
    · subst h; rw [ux, tm]
    · rw [uk.1 _ (nk i (by omega_arith) h).1, tx i (by omega_arith)]
  · by_cases h : i = n
    · subst h; rw [uc, tm]
    · rw [uk.1 _ (nk i (by omega_arith) h).2, tc i (by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · exact (small_mem n hn).1
    · exact (small_mem n hn).2

def smallStore (o i : Nat) : List Instr :=
  [.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++
    (if i = 4 then [.add .x (smallX i) (smallX i) (smallC 7)] else []) ++ [st (smallX i) (o + 8 * i)]

theorem small_split (o a e : Nat) :
    small o a e = ([.movz .x .x0 39081 0, .movz .x .x2 0xa900 0, .movk .x .x2 0x0098 1] : List Instr) ++
      (List.range 8).flatMap (smallLimb a e) ++ (List.range 8).flatMap (smallStore o) := rfl

/-- The value `smallStore` writes. -/
def smallOut (X C : Nat → BitVec 64) (i : Nat) : BitVec 64 :=
  X i + C ((i + 7) % 8) + if i = 4 then C 7 else 0

theorem smallCX : ∀ i < 8, smallC ((i + 7) % 8) ≠ smallX i ∧ smallC 7 ≠ smallX i := by decide

theorem smallStore_ok {t : State} {base : Addr} (ht : Scr t base) {o i : Nat} (hi : i < 8)
    (ho : o + 64 ≤ 8192) (ho8 : o % 8 = 0) :
    WP isa (.block (smallStore o i)) t fun u =>
      (∀ d, d + 8 ≤ 8192 → (d = o + 8 * i ∨ d + 8 ≤ o + 8 * i ∨ o + 8 * i + 8 ≤ d) →
        word u.mem base d = if d = o + 8 * i then smallOut (fun j => t.gpr (smallX j)) (fun j => t.gpr (smallC j)) i else word t.mem base d) ∧
      Outside base (o + 8 * i) 8 t.mem u.mem ∧ Keeps [smallX i] t u := by
  obtain ⟨cx, c7⟩ := smallCX i hi
  have hx3 := (small_not i hi).1
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx3
  by_cases h4 : i = 4
  · subst h4
    simp only [smallStore, ite_true, List.cons_append, List.nil_append]
    rw [show [Instr.add .x (smallX 4) (smallX 4) (smallC ((4 + 7) % 8)),
        .add .x (smallX 4) (smallX 4) (smallC 7), st (smallX 4) (o + 8 * 4)] =
        [Instr.add .x (smallX 4) (smallX 4) (smallC ((4 + 7) % 8))] ++
        [Instr.add .x (smallX 4) (smallX 4) (smallC 7)] ++ [st (smallX 4) (o + 8 * 4)] from rfl,
      List.append_assoc, WP.block_append_iff]
    refine WP.mono (add_ok t _ _ _) fun u ⟨uv, um, uk⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (add_ok u _ _ _) fun v ⟨vv, vm, vk⟩ => ?_
    have vs : Scr v base := (ht.of_keeps uk (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)).of_keeps vk
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)
    refine WP.mono (stw_ok vs _ (d := o + 8 * 4) (by omega_arith) (by omega_arith))
      fun w ⟨ww, wo, wg, wr, wwr⟩ => ⟨fun d hd hs => ?_, by rw [← um, ← vm]; exact wo,
        ⟨fun q hq => ?_, wr.trans (vk.2.1.trans uk.2.1), wwr.trans (vk.2.2.trans uk.2.2)⟩⟩
    · rw [ww d hd hs, vv, vm, um, uk.1 (smallC 7) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact c7), uv]
      by_cases e : d = o + 8 * 4
      · rw [ite_eq_left e, ite_eq_left e]; simp only [smallOut, ite_true]
      · rw [ite_eq_right e, ite_eq_right e]
    · rw [wg, vk.1 q hq, uk.1 q hq]
  · simp only [smallStore, h4, ite_false, List.append_nil]
    rw [show [Instr.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++ [st (smallX i) (o + 8 * i)] =
        [Instr.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++ [st (smallX i) (o + 8 * i)] from rfl,
      WP.block_append_iff]
    refine WP.mono (add_ok t _ _ _) fun u ⟨uv, um, uk⟩ => ?_
    have us : Scr u base := ht.of_keeps uk (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)
    refine WP.mono (stw_ok us _ (d := o + 8 * i) (by omega_arith) (by omega_arith))
      fun w ⟨ww, wo, wg, wr, wwr⟩ => ⟨fun d hd hs => ?_, by rw [← um]; exact wo,
        ⟨fun q hq => ?_, wr.trans uk.2.1, wwr.trans uk.2.2⟩⟩
    · rw [ww d hd hs, uv, um]
      by_cases e : d = o + 8 * i
      · rw [ite_eq_left e, ite_eq_left e]; simp only [smallOut, h4, ite_false]; exact (BitVec.add_zero _).symm
      · rw [ite_eq_right e, ite_eq_right e]
    · rw [wg, uk.1 q hq]

theorem smallLoop2_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 64 ≤ 8192)
    (ho8 : o % 8 = 0) :
    WP isa (.block ((List.range 8).flatMap (smallStore o))) s fun t =>
      (∀ i < 8, word t.mem base (o + 8 * i) =
        smallOut (fun j => s.gpr (smallX j)) (fun j => s.gpr (smallC j)) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps smallRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (o + 8 * i) =
      smallOut (fun j => s.gpr (smallX j)) (fun j => s.gpr (smallC j)) i) ∧
    (∀ i < 8, n ≤ i → t.gpr (smallX i) = s.gpr (smallX i)) ∧
    (∀ i < 8, t.gpr (smallC i) = s.gpr (smallC i)) ∧
    Outside base o (8 * n) s.mem t.mem ∧ Keeps smallRegs s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tx, tc, tO, tk⟩ => ?_) 8
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, fun _ _ => rfl,
      Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tv, _, _, tO, tk⟩ => ⟨tv, tO, tk⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (smallStore_ok ts hn ho ho8) fun u ⟨uw, uO, uk⟩ => ⟨fun i hi => ?_, fun i hi hni => ?_,
    fun i hi => ?_, ?_, tk.trans (uk.mono fun r hr => ?_)⟩
  · rw [uw _ (by omega_arith) (by omega_arith)]
    by_cases h : i = n
    · subst h
      rw [ite_eq_left rfl]
      simp only [smallOut, tx i hn (Nat.le_refl _), tc _ (Nat.mod_lt _ (by decide)), tc 7 (by decide)]
    · rw [ite_eq_right (by omega_arith)]; exact tv i (by omega_arith)
  · have := (small_inj n hn i hi (by omega_arith)).1
    rw [uk.1 _ (by simp [this]), tx i hi (by omega_arith)]
  · by_cases h : i = n
    · subst h; rw [uk.1 _ (by simp [(small_not i hi).2.2.symm]), tc i hi]
    · rw [uk.1 _ (by simp [(small_inj n hn i hi h).2.2.2]), tc i hi]
  · rw [show 8 * (n + 1) = 8 * n + 8 by omega_arith]
    intro x hx
    rw [uO x (by omega_arith), tO x (by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact (small_mem n hn).1

/-- The limbs `small` writes, from the operands' limbs. -/
def smallVal (a e : Nat → Nat) (i : Nat) : Nat :=
  sl a e i + sc e ((i + 7) % 8) + if i = 4 then sc e 7 else 0

theorem small_ok {s : State} {base : Addr} (hs : Scr s base) {o a e : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (he8 : e % 8 = 0) (fa : ∀ i < 8, limbs s.mem base a i < Mb) (fe : ∀ i < 8, limbs s.mem base e i < Ib) :
    WP isa (.block (small o a e)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = smallVal (limbs s.mem base a) (limbs s.mem base e) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps (.x0 :: .x2 :: smallRegs) s t := by
  rw [small_split, List.append_assoc, WP.block_append_iff]
  refine WP.mono (smallConsts_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (smallLoop1_ok ts ha he ha8 he8 t0 t2) fun u ⟨ux, uc, um, uk⟩ => ?_
  have us : Scr u base := ts.of_keeps uk (by decide)
  refine WP.mono (smallLoop2_ok us ho ho8) fun w ⟨wv, wo, wk⟩ => ⟨fun i hi => ?_, ?_,
    (tk.mono (by decide)).trans ((uk.mono (by decide)).trans (wk.mono (by decide)))⟩
  · have lv : ∀ j < 8, (u.gpr (smallX j)).toNat = sl (limbs s.mem base a) (limbs s.mem base e) j ∧
        (u.gpr (smallC j)).toNat = sc (limbs s.mem base e) j := by
      intro j hj
      have hb := fa j hj; have hb' := fe j hj
      simp only [Mb, Ib] at hb hb'
      have := smallLimb_val (word s.mem base (a + 8 * j)) (word s.mem base (e + 8 * j))
        (by simp only [limbs] at hb; omega_arith) (by simp only [limbs] at hb'; omega_arith)
      rw [ux j hj, uc j hj, tm]
      exact this
    have hc : ∀ j < 8, sc (limbs s.mem base e) j < 2 ^ 20 := by
      intro j hj; have := fe j hj; simp only [sc, Ib, radix] at this ⊢; omega_arith
    have hsl : sl (limbs s.mem base a) (limbs s.mem base e) i < 2 ^ 58 := by
      have := fa i hi; have := Nat.mod_lt (39081 * limbs s.mem base e i) (show 0 < radix by decide)
      simp only [sl, Mb, radix] at *; omega_arith
    change (word w.mem base (o + 8 * i)).toNat = _
    rw [wv i hi]
    simp only [smallOut, smallVal]
    have h7 := (lv 7 (by decide)).2
    have hj := (lv ((i + 7) % 8) (Nat.mod_lt _ (by decide))).2
    have hx := (lv i hi).1
    have c7 := hc 7 (by decide)
    have cj := hc ((i + 7) % 8) (Nat.mod_lt _ (by decide))
    split
    · rw [BitVec.toNat_add, BitVec.toNat_add, hx, hj, h7]
      omega_arith
    · rw [BitVec.toNat_add, BitVec.toNat_add, hx, hj, show (0 : BitVec 64).toNat = 0 from rfl]
      omega_arith
  · intro x hx
    rw [wo x hx, um, tm]

end VG.Proof.Curve448.AArch64.Fast

end

end


/-!
# The field operations, modulo `p`

Untrusted: everything here is checked by Lean. Reduced elements (`Mb`)
are the outputs of products and the inputs of sums and differences; products
take any limbs below `Ib`, which sums, differences and `a + a24 e` keep.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.Spec.X448
open VG.Impl.Curve448.AArch64.Fast
open VG.Proof.X448 (toFe toFe_mul toFe_add toFe_sub toFe_congr)
open VG.Proof.X448.Wide (radix valN valN_congr valN_add rows reduced reduced_mod rows_val)

theorem Mb_le_Ib : Mb ≤ Ib := by decide

theorem prod_val (f g : Nat → Nat) :
    toFe (valN (prodOut f g) 8) = toFe (valN f 8) * toFe (valN g 8) := by
  apply toFe_mul
  rw [out_mod, reduced_mod, rows_val f g (by decide)]

theorem prod_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < Ib) (hg : ∀ i < 8, g i < Ib) :
    ∀ i < 8, prodOut f g i < Mb := (fits_of hf hg).out

theorem twoP_val : valN twoP 8 = 2 * P := by decide +kernel

theorem twoP_le (i : Nat) : Mb ≤ twoP i := by simp only [twoP, Mb]; split <;> omega_using []

theorem twoPW_toNat (i : Nat) : (twoPW i).toNat = twoP i := by
  simp only [twoPW, twoP, K2, K4]; split <;> rfl

/-- `a + 2p - b`, for reduced `b`. -/
def diffN (f g : Nat → Nat) (i : Nat) : Nat := f i + twoP i - g i

theorem diff_val {f g : Nat → Nat} (hg : ∀ i < 8, g i < Mb) :
    toFe (valN (diffN f g) 8) = toFe (valN f 8) - toFe (valN g 8) := by
  apply toFe_sub
  have : valN (diffN f g) 8 + valN g 8 = valN f 8 + 2 * P := by
    rw [← valN_add, ← twoP_val, ← valN_add]
    apply valN_congr
    intro i hi
    have := hg i hi; have := twoP_le i
    simp only [diffN]; omega_arith
  rw [this, Nat.add_mul_mod_self_right]

theorem diff_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < Mb) : ∀ i < 8, diffN f g i < Ib := by
  intro i hi
  have := hf i hi
  simp only [diffN, twoP, Mb, Ib] at *
  split <;> omega_using [this]

theorem diff_word (x y : BitVec 64) (i : Nat) (hx : x.toNat < Mb) (hy : y.toNat < Mb) :
    (x + twoPW i - y).toNat = x.toNat + twoP i - y.toNat := by
  have := twoP_le i
  have h2 : twoP i < 2 ^ 58 := by simp only [twoP]; split <;> omega_using []
  simp only [Mb] at hx hy this
  rw [BitVec.toNat_sub, BitVec.toNat_add, twoPW_toNat]
  have := y.isLt
  simp only [Nat.reducePow] at *
  omega_arith

theorem sum_val (f g : Nat → Nat) :
    toFe (valN (fun i => f i + g i) 8) = toFe (valN f 8) + toFe (valN g 8) := by
  apply toFe_add; rw [valN_add]

theorem sum_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < Mb) (hg : ∀ i < 8, g i < Mb) :
    ∀ i < 8, f i + g i < Ib := by
  intro i hi; have := hf i hi; have := hg i hi; simp only [Mb, Ib] at *; omega_arith

theorem sum_word (x y : BitVec 64) (hx : x.toNat < Mb) (hy : y.toNat < Mb) :
    (x + y).toNat = x.toNat + y.toNat := by
  simp only [Mb] at hx hy
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_using [hx, hy])]

theorem small_val (f g : Nat → Nat) :
    valN (smallVal f g) 8 + P * sc g 7 = valN f 8 + 39081 * valN g 8 := by
  have hs : ∀ i, sl f g i + radix * sc g i = f i + 39081 * g i := fun i => by
    simp only [sl, sc]; have := Nat.mod_add_div (39081 * g i) radix; omega_using [this]
  have h0 := hs 0; have h1 := hs 1; have h2 := hs 2; have h3 := hs 3
  have h4 := hs 4; have h5 := hs 5; have h6 := hs 6; have h7 := hs 7
  have hp : P = radix ^ 8 - radix ^ 4 - 1 := by decide +kernel
  simp only [valN, smallVal, Nat.reduceAdd, Nat.reduceMod, ite_true, ite_false,
    show ¬ (0 = 4) by decide, show ¬ (1 = 4) by decide, show ¬ (2 = 4) by decide,
    show ¬ (3 = 4) by decide, show ¬ (5 = 4) by decide, show ¬ (6 = 4) by decide,
    show ¬ (7 = 4) by decide, Nat.zero_add, Nat.add_zero, Nat.pow_zero, Nat.one_mul]
  simp only [hp, radix, Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  omega_using [h0, h1, h2, h3, h4, h5, h6, h7]

theorem smallF (f g : Nat → Nat) :
    toFe (valN (smallVal f g) 8) = toFe (valN f 8) + a24 * toFe (valN g 8) := by
  have : toFe (valN (smallVal f g) 8) = toFe (valN f 8 + 39081 * valN g 8) := by
    apply toFe_congr; rw [← small_val, Nat.add_mul_mod_self_left]
  rw [this]
  exact toFe_add (b := 39081 * valN g 8) rfl |>.trans (congrArg _ (toFe_mul rfl))

theorem small_bound {f g : Nat → Nat} (hf : ∀ i < 8, f i < Mb) (hg : ∀ i < 8, g i < Ib) :
    ∀ i < 8, smallVal f g i < Ib := by
  intro i hi
  have hc : ∀ j < 8, sc g j < 2 ^ 20 := fun j hj => by
    have := hg j hj; simp only [sc, Ib, radix] at *; omega_using [this]
  have := hf i hi
  have hl := Nat.mod_lt (39081 * g i) (show 0 < radix by decide)
  have := hc ((i + 7) % 8) (Nat.mod_lt _ (by decide))
  have := hc 7 (by decide)
  simp only [smallVal, sl, Mb, Ib, radix] at *
  split <;> omega_arith

end VG.Proof.Curve448.AArch64.Fast

end

end


/-!
# X448 on AArch64: the working space as field-element slots

Untrusted: everything here is checked by Lean. Each field operation updates
the slots it writes. Every slot's limbs stay below `Ib`; products leave
reduced limbs (below `Mb`), which sums and differences need of their
operands.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot)
open VG.Proof.X448.AArch64.Weak (Index Env slot_bound slot_aligned slot_sep opMul opAdd opSub
  opA24 opCopy opSwap)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (toFe)

abbrev fclob := VG.Proof.Curve448.AArch64.Fast.clob

/-- Limbs below `n`. -/
def Bnd (n : Nat) (m : Mem) (base : Addr) (o : Nat) : Prop := ∀ i < 8, limbs m base o i < n

/-- Every slot's limbs are below `Ib`. -/
def BEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, Bnd Ib m base (slot i.val)

/-- What a field operation preserves: registers outside `clob`, and memory
outside the field slots and the coefficient area. -/
structure FKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps fclob s t
  mem : Outside2 base 64 2816 ACC 1152 s.mem t.mem

theorem FKeep.trans {base : Addr} {s t u : State} (h : FKeep base s t) (h' : FKeep base t u) :
    FKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem FKeep.scr {base : Addr} {s t : State} (h : FKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

/-- Slots other than `os` keep their limbs. -/
def Same (base : Addr) (os : List Index) (m m' : Mem) : Prop :=
  ∀ i : Index, i ∉ os → ∀ j < 8, limbs m' base (slot i.val) j = limbs m base (slot i.val) j

theorem Same.bnd {base : Addr} {os : List Index} {m m' : Mem} (h : Same base os m m') {n : Nat}
    {i : Index} (hi : i ∉ os) (hb : Bnd n m base (slot i.val)) : Bnd n m' base (slot i.val) :=
  fun j hj => by rw [h i hi j hj]; exact hb j hj

theorem Same.env {base : Addr} {os : List Index} {m m' : Mem} (h : Same base os m m') {i : Index}
    (hi : i ∉ os) : VG.Proof.X448.AArch64.Weak.E m' base i = VG.Proof.X448.AArch64.Weak.E m base i :=
  congrArg toFe (VG.Proof.X448.Wide.valN_congr (h i hi))

theorem slot_64 (i : Index) : slot i.val + 64 ≤ ACC := by have := slot_bound i; omega

theorem slot_mem (i : Index) : slot i.val + 128 ≤ 8192 := by
  have := slot_bound i; have : ACC = 3584 := rfl; omega

theorem slot_sep64 {i j : Index} (h : i ≠ j) : slot i.val + 64 ≤ slot j.val ∨ slot j.val + 64 ≤ slot i.val := by
  have := slot_sep h; omega_using [this]

/-- Byte frame of an operation writing slot `o`'s first 64 bytes and the coefficient area. -/
theorem fieldMem_same {base : Addr} {o : Index} {m m' : Mem} (h : FieldMem base (slot o.val) m m') :
    Same base [o] m m' := by
  intro i hi j hj
  have hne : i ≠ o := fun e => hi (by simp [e])
  exact h.limbs (slot_sep hne) (slot_bound i) (by omega_using [hj] : j < 16)

theorem fieldMem_outside2 {base : Addr} {o : Index} {m m' : Mem} (h : FieldMem base (slot o.val) m m') :
    Outside2 base 64 2816 ACC 1152 m m' := by
  intro p hp hq
  apply h p _ (hq.imp_right fun h => Nat.le_trans (Nat.add_le_add_left (by decide : 512 ≤ 1152) _) h)
  have := o.isLt
  simp only [slot]
  omega_using [hp]

theorem slot_inj {i j : Index} (h : slot i.val = slot j.val) : i = j := by
  apply Fin.ext; simp only [slot] at h; omega_using [h]

theorem env_update {base : Addr} {s t : State} {o : Index} (hb : BEnv s.mem base)
    (hm : FieldMem base (slot o.val) s.mem t.mem) (ho : Bnd Ib t.mem base (slot o.val)) :
    BEnv t.mem base := by
  intro i
  by_cases h : i = o
  · subst h; exact ho
  · exact (fieldMem_same hm).bnd (by simp [h]) (hb i)

theorem fmulE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : a = b ∨ o ≠ b) :
    WP isa (.block (Impl.X448.AArch64.Fast.fmul (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot o.val) ∧
      Same base [o] s.mem t.mem ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = opMul o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
  have post : ∀ t : State, (∀ i < 8, limbs t.mem base (slot o.val) i =
      VG.Proof.Curve448.AArch64.Fast.prodOut (limbs s.mem base (slot a.val))
        (limbs s.mem base (slot b.val)) i) → FieldMem base (slot o.val) s.mem t.mem → Keeps fclob s t →
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot o.val) ∧
      Same base [o] s.mem t.mem ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = opMul o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
    intro t tv tm tk
    have bo : Bnd Mb t.mem base (slot o.val) := fun i hi => by
      rw [tv i hi]; exact VG.Proof.Curve448.AArch64.Fast.prod_bound (hb a) (hb b) i hi
    refine ⟨⟨tk, fieldMem_outside2 tm⟩, env_update hb tm (fun i hi =>
      Nat.lt_of_lt_of_le (bo i hi) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib), bo, fieldMem_same tm, ?_⟩
    rw [VG.Proof.X448.AArch64.Weak.E_update tm]
    simp only [opMul]
    refine congrArg (Function.update _ o) ?_
    change toFe _ = toFe _ * toFe _
    rw [show VG.Proof.X448.Wide.valN (limbs t.mem base (slot o.val)) 8 =
      VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.prodOut (limbs s.mem base (slot a.val))
        (limbs s.mem base (slot b.val))) 8 from VG.Proof.X448.Wide.valN_congr tv]
    exact VG.Proof.Curve448.AArch64.Fast.prod_val _ _
  simp only [Impl.X448.AArch64.Fast.fmul]
  split
  · rename_i h
    have hab := slot_inj h
    subst hab
    exact WP.mono (VG.Proof.Curve448.AArch64.Fast.sqr_ok hs (slot_64 o) (slot_aligned o) (slot_64 a)
      (slot_aligned a) (hb a)) fun t ⟨tv, tm, tk⟩ => post t tv tm tk
  · rename_i h
    have hob' : o ≠ b := hob.resolve_left fun e => h (e ▸ rfl)
    exact WP.mono (VG.Proof.Curve448.AArch64.Fast.mul_ok hs (slot_64 o) (slot_aligned o) (slot_64 a)
      (slot_aligned a) (slot_64 b) (slot_aligned b) (slot_sep64 hob') (hb a) (hb b))
      fun t ⟨tv, tm, tk⟩ => post t tv tm tk

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

open VG.Proof.Curve448.AArch64.Fast (Away)

theorem away_same {base : Addr} {os : List Index} {m m' : Mem}
    (h : ∀ x, Away base (os.map fun i => slot i.val) 64 x → m' x = m x) : Same base os m m' := by
  intro i hi j hj
  change (word m' base (slot i.val + 8 * j)).toNat = (word m base (slot i.val + 8 * j)).toNat
  rw [VG.Proof.Curve448.AArch64.Fast.away_word h (by have := slot_mem i; omega_using [hj, this]) (fun o ho => by
    simp only [List.mem_map] at ho
    obtain ⟨k, hk, rfl⟩ := ho
    have := slot_sep (show i ≠ k from fun e => hi (e ▸ hk))
    omega_using [hj, this])]

theorem away_outside2 {base : Addr} {os : List Index} {m m' : Mem}
    (h : ∀ x, Away base (os.map fun i => slot i.val) 64 x → m' x = m x) :
    Outside2 base 64 2816 ACC 1152 m m' := by
  intro p hp _
  apply h p
  intro o ho
  simp only [List.mem_map] at ho
  obtain ⟨k, -, rfl⟩ := ho
  have := k.isLt
  simp only [slot]
  omega_using [hp]

theorem away_fieldMem {base : Addr} {o : Index} {m m' : Mem}
    (h : ∀ x, Away base [slot o.val] 64 x → m' x = m x) : FieldMem base (slot o.val) m m' :=
  fun x hx _ => h x fun o' ho' => by simp at ho'; subst ho'; omega_using [hx]

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [o] s.mem t.mem ∧ EV t.mem base = opSub o a b (EV s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.sub_ok hs (by have := slot_mem o; omega_using [this])
    (by have := slot_mem a; omega_using [this]) (by have := slot_mem b; omega_using [this]) (slot_aligned o) (slot_aligned a)
    (slot_aligned b) (slot_sep64 hoa) (slot_sep64 hob)) fun t ⟨tv, tm, tk⟩ => ?_
  have tl : ∀ i < 8, limbs t.mem base (slot o.val) i =
      VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot a.val)) (limbs s.mem base (slot b.val)) i := by
    intro i hi
    change (word t.mem base (slot o.val + 8 * i)).toNat = _
    rw [tv i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (ha i hi) (hb' i hi)]; rfl
  have fm := away_fieldMem tm
  refine ⟨⟨tk.mono (by decide), fieldMem_outside2 fm⟩, env_update hb fm (fun i hi => by
    rw [tl i hi]; exact VG.Proof.Curve448.AArch64.Fast.diff_bound ha i hi), fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  simp only [opSub]
  refine congrArg (Function.update _ o) ?_
  change toFe _ = toFe _ - toFe _
  rw [VG.Proof.X448.Wide.valN_congr tl]
  exact VG.Proof.Curve448.AArch64.Fast.diff_val hb'

theorem bnd_of_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat} {n : Nat}
    (h : ∀ i < 8, limbs m base o i = f i) (hf : ∀ i < 8, f i < n) : Bnd n m base o :=
  fun i hi => by rw [h i hi]; exact hf i hi

theorem fe_of_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat}
    (h : ∀ i < 8, limbs m base o i = f i) :
    VG.Proof.X448.AArch64.Weak.F m base o = toFe (VG.Proof.X448.Wide.valN f 8) :=
  congrArg toFe (VG.Proof.X448.Wide.valN_congr h)

theorem addSubE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o₁ o₂ a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (h12 : o₁ ≠ o₂)
    (h1a : o₁ ≠ a) (h1b : o₁ ≠ b) (h2a : o₂ ≠ a) (h2b : o₂ ≠ b) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.addSub (slot o₁.val) (slot o₂.val) (slot a.val)
        (slot b.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [o₁, o₂] s.mem t.mem ∧
      EV t.mem base = Function.update (Function.update (EV s.mem base) o₁ (EV s.mem base a + EV s.mem base b))
        o₂ (EV s.mem base a - EV s.mem base b) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.addSub_ok hs (by have := slot_mem o₁; omega_using [this])
    (by have := slot_mem o₂; omega_using [this]) (by have := slot_mem a; omega_using [this]) (by have := slot_mem b; omega_using [this])
    (slot_aligned o₁) (slot_aligned o₂) (slot_aligned a) (slot_aligned b) (slot_sep64 h12)
    (slot_sep64 h1a) (slot_sep64 h1b) (slot_sep64 h2a) (slot_sep64 h2b)) fun t ⟨t1, t2, tm, tk⟩ => ?_
  have l1 : ∀ i < 8, limbs t.mem base (slot o₁.val) i =
      limbs s.mem base (slot a.val) i + limbs s.mem base (slot b.val) i := fun i hi => by
    change (word t.mem base (slot o₁.val + 8 * i)).toNat = _
    rw [t1 i hi, VG.Proof.Curve448.AArch64.Fast.sum_word _ _ (ha i hi) (hb' i hi)]
  have l2 : ∀ i < 8, limbs t.mem base (slot o₂.val) i =
      VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot a.val)) (limbs s.mem base (slot b.val)) i :=
    fun i hi => by
      change (word t.mem base (slot o₂.val + 8 * i)).toNat = _
      rw [t2 i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (ha i hi) (hb' i hi)]; rfl
  have sm : Same base [o₁, o₂] s.mem t.mem := away_same (os := [o₁, o₂]) tm
  refine ⟨⟨tk.mono (by decide), away_outside2 (os := [o₁, o₂]) tm⟩, fun i => ?_, sm, ?_⟩
  · by_cases e1 : i = o₁
    · subst e1; exact bnd_of_limbs l1 (VG.Proof.Curve448.AArch64.Fast.sum_bound ha hb')
    · by_cases e2 : i = o₂
      · subst e2; exact bnd_of_limbs l2 (VG.Proof.Curve448.AArch64.Fast.diff_bound ha)
      · exact sm.bnd (by simp [e1, e2]) (hb i)
  · funext i
    simp only [Function.update_apply]
    by_cases e2 : i = o₂
    · subst e2
      rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot i.val) = _
      rw [fe_of_limbs l2]
      exact VG.Proof.Curve448.AArch64.Fast.diff_val hb'
    · rw [ite_eq_right e2]
      by_cases e1 : i = o₁
      · subst e1
        rw [ite_eq_left rfl]
        change VG.Proof.X448.AArch64.Weak.F t.mem base (slot i.val) = _
        rw [fe_of_limbs l1]
        exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
      · rw [ite_eq_right e1]; exact sm.env (by simp [e1, e2])

theorem smallE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a e : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.small (slot o.val) (slot a.val) (slot e.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [o] s.mem t.mem ∧
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a + Spec.X448.a24 * EV s.mem base e) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.small_ok hs (by have := slot_mem o; omega_using [this])
    (by have := slot_mem a; omega_using [this]) (by have := slot_mem e; omega_using [this]) (slot_aligned o) (slot_aligned a)
    (slot_aligned e) ha (hb e)) fun t ⟨tv, tm, tk⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := VG.Proof.X448.AArch64.FieldMem.output (tm.mono (Nat.le_refl _) (by omega_using []))
  refine ⟨⟨tk.mono (by decide), fieldMem_outside2 fm⟩, env_update hb fm
    (bnd_of_limbs tv (VG.Proof.Curve448.AArch64.Fast.small_bound ha (hb e))), fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  refine congrArg (Function.update _ o) ?_
  change VG.Proof.X448.AArch64.Weak.F t.mem base (slot o.val) = _
  rw [fe_of_limbs tv]
  exact VG.Proof.Curve448.AArch64.Fast.smallF _ _

/-- Slot `i` of the swapped coordinates (`x₂, z₂, x₃, z₃` are slots 1–4). -/
def swp (sw : Bool) (i : Index) : Index := if sw then (if i = 1 then 3 else if i = 3 then 1 else
  if i = 2 then 4 else if i = 4 then 2 else i) else i

/-- The butterfly's result on the field slots. -/
def bflyEnv (sw : Bool) (e : Env) : Env := fun i =>
  if i = 5 then e (swp sw 1) + e (swp sw 2) else if i = 6 then e (swp sw 1) - e (swp sw 2)
  else if i = 7 then e (swp sw 3) + e (swp sw 4) else if i = 8 then e (swp sw 3) - e (swp sw 4)
  else e i

theorem sel_slot (m : Mem) (base : Addr) (sw : Bool) (p q : Index) (i : Nat) :
    VG.Proof.Curve448.AArch64.Fast.sel sw (word m base (slot p.val + 8 * i)) (word m base (slot q.val + 8 * i)) =
      word m base (slot (if sw then q else p).val + 8 * i) := by
  cases sw <;> rfl

theorem bflyE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hM : ∀ i : Index, i.val ∈ [1, 2, 3, 4] → Bnd Mb s.mem base (slot i.val))
    {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.butterfly X2 Z2 X3 Z3 A B C D)) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [5, 6, 7, 8] s.mem t.mem ∧
      EV t.mem base = bflyEnv sw (EV s.mem base) := by
  have hX2 : X2 = slot (1 : Index).val := rfl
  have hZ2 : Z2 = slot (2 : Index).val := rfl
  have hX3 : X3 = slot (3 : Index).val := rfl
  have hZ3 : Z3 = slot (4 : Index).val := rfl
  have hA : A = slot (5 : Index).val := rfl
  have hB : B = slot (6 : Index).val := rfl
  have hC : C = slot (7 : Index).val := rfl
  have hD : D = slot (8 : Index).val := rfl
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.butterfly_ok hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hm) fun t ⟨tv, tm, tk⟩ => ?_
  have sw1 : ∀ p q : Index, p.val ∈ [1, 2, 3, 4] → q.val ∈ [1, 2, 3, 4] →
      Bnd Mb s.mem base (slot (if sw then q else p).val) := fun p q hp hq => by
    cases sw
    · exact hM p hp
    · exact hM q hq
  have val : ∀ (o : Nat) (k : Index) (p q : Index), o = slot k.val →
      (∀ i < 8, word t.mem base (o + 8 * i) = word s.mem base (slot p.val + 8 * i) +
        word s.mem base (slot q.val + 8 * i)) → Bnd Mb s.mem base (slot p.val) → Bnd Mb s.mem base (slot q.val) →
      (∀ i < 8, limbs t.mem base (slot k.val) i = limbs s.mem base (slot p.val) i + limbs s.mem base (slot q.val) i) :=
    fun o k p q ho h hp hq i hi => by
      subst ho
      change (word t.mem base (slot k.val + 8 * i)).toNat = _
      rw [h i hi, VG.Proof.Curve448.AArch64.Fast.sum_word _ _ (hp i hi) (hq i hi)]
  have dif : ∀ (k : Index) (p q : Index),
      (∀ i < 8, word t.mem base (slot k.val + 8 * i) = word s.mem base (slot p.val + 8 * i) +
        VG.Proof.Curve448.AArch64.Fast.twoPW i - word s.mem base (slot q.val + 8 * i)) →
      Bnd Mb s.mem base (slot p.val) → Bnd Mb s.mem base (slot q.val) →
      (∀ i < 8, limbs t.mem base (slot k.val) i =
        VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot p.val)) (limbs s.mem base (slot q.val)) i) :=
    fun k p q h hp hq i hi => by
      change (word t.mem base (slot k.val + 8 * i)).toNat = _
      rw [h i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (hp i hi) (hq i hi)]; rfl
  let x2 := swp sw 1; let z2 := swp sw 2; let x3 := swp sw 3; let z3 := swp sw 4
  have ex2 : (if sw then (3 : Index) else 1) = x2 := by cases sw <;> rfl
  have ez2 : (if sw then (4 : Index) else 2) = z2 := by cases sw <;> rfl
  have ex3 : (if sw then (1 : Index) else 3) = x3 := by cases sw <;> rfl
  have ez3 : (if sw then (2 : Index) else 4) = z3 := by cases sw <;> rfl
  have mx2 := sw1 1 3 (by decide) (by decide); rw [ex2] at mx2
  have mz2 := sw1 2 4 (by decide) (by decide); rw [ez2] at mz2
  have mx3 := sw1 3 1 (by decide) (by decide); rw [ex3] at mx3
  have mz3 := sw1 4 2 (by decide) (by decide); rw [ez3] at mz3
  have wA : ∀ i < 8, word t.mem base (slot (5 : Index).val + 8 * i) =
      word s.mem base (slot x2.val + 8 * i) + word s.mem base (slot z2.val + 8 * i) := fun i hi => by
    rw [← hA, tv A (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, ite_true, hX2, hX3, hZ2, hZ3, sel_slot, ex2, ez2]
  have wB : ∀ i < 8, word t.mem base (slot (6 : Index).val + 8 * i) =
      word s.mem base (slot x2.val + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i -
        word s.mem base (slot z2.val + 8 * i) := fun i hi => by
    rw [← hB, tv B (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show B ≠ A by decide, ite_true, ite_false, hX2, hX3,
      hZ2, hZ3, sel_slot, ex2, ez2]
  have wC : ∀ i < 8, word t.mem base (slot (7 : Index).val + 8 * i) =
      word s.mem base (slot x3.val + 8 * i) + word s.mem base (slot z3.val + 8 * i) := fun i hi => by
    rw [← hC, tv C (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show C ≠ A by decide, show C ≠ B by decide, ite_true,
      ite_false, hX2, hX3, hZ2, hZ3, sel_slot, ex3, ez3]
  have wD : ∀ i < 8, word t.mem base (slot (8 : Index).val + 8 * i) =
      word s.mem base (slot x3.val + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i -
        word s.mem base (slot z3.val + 8 * i) := fun i hi => by
    rw [← hD, tv D (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show D ≠ A by decide, show D ≠ B by decide,
      show D ≠ C by decide, ite_false, hX2, hX3, hZ2, hZ3, sel_slot, ex3, ez3]
  have lA := val _ 5 x2 z2 rfl wA mx2 mz2
  have lB := dif 6 x2 z2 wB mx2 mz2
  have lC := val _ 7 x3 z3 rfl wC mx3 mz3
  have lD := dif 8 x3 z3 wD mx3 mz3
  have sm : Same base [5, 6, 7, 8] s.mem t.mem := away_same (os := [5, 6, 7, 8]) tm
  refine ⟨⟨tk.mono (by decide), away_outside2 (os := [5, 6, 7, 8]) tm⟩, fun i => ?_, sm, ?_⟩
  · by_cases e5 : i = 5
    · subst e5; exact bnd_of_limbs lA (VG.Proof.Curve448.AArch64.Fast.sum_bound mx2 mz2)
    by_cases e6 : i = 6
    · subst e6; exact bnd_of_limbs lB (VG.Proof.Curve448.AArch64.Fast.diff_bound mx2)
    by_cases e7 : i = 7
    · subst e7; exact bnd_of_limbs lC (VG.Proof.Curve448.AArch64.Fast.sum_bound mx3 mz3)
    by_cases e8 : i = 8
    · subst e8; exact bnd_of_limbs lD (VG.Proof.Curve448.AArch64.Fast.diff_bound mx3)
    exact sm.bnd (by simp [e5, e6, e7, e8]) (hb i)
  · funext i
    simp only [bflyEnv]
    by_cases e5 : i = 5
    · subst e5; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((5 : Index) : Nat)) = _
      rw [fe_of_limbs lA]; exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
    rw [ite_eq_right e5]
    by_cases e6 : i = 6
    · subst e6; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((6 : Index) : Nat)) = _
      rw [fe_of_limbs lB]; exact VG.Proof.Curve448.AArch64.Fast.diff_val mz2
    rw [ite_eq_right e6]
    by_cases e7 : i = 7
    · subst e7; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((7 : Index) : Nat)) = _
      rw [fe_of_limbs lC]; exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
    rw [ite_eq_right e7]
    by_cases e8 : i = 8
    · subst e8; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((8 : Index) : Nat)) = _
      rw [fe_of_limbs lD]; exact VG.Proof.Curve448.AArch64.Fast.diff_val mz3
    rw [ite_eq_right e8]
    exact sm.env (by simp [e5, e6, e7, e8])

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o.val) (slot a.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ (∀ j < 8, limbs t.mem base (slot o.val) j = limbs s.mem base (slot a.val) j) ∧
      Same base [o] s.mem t.mem ∧ EV t.mem base = opCopy o a (EV s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (slot_sep h)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (slot_mem o) (slot_mem a) (slot_aligned o)
    (slot_aligned a) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := VG.Proof.X448.AArch64.FieldMem.output tm
  refine ⟨⟨tk.mono (by decide), fieldMem_outside2 fm⟩, env_update hb fm (fun i hi => by
    rw [tf i hi]; exact hb a i hi), tf, fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm, opCopy]
  refine congrArg (Function.update _ o) ?_
  exact congrArg toFe (VG.Proof.X448.Wide.valN_congr tf)

end VG.Proof.X448.AArch64.Fast
