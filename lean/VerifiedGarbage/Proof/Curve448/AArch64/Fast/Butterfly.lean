module

public import VerifiedGarbage.Proof.X448.AArch64.Swap
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Finish
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Curve448.AArch64.Fast
import VerifiedGarbage.Proof.X448.Wide.Limbs
import VerifiedGarbage.Impl.X448.AArch64.Symmetric

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
