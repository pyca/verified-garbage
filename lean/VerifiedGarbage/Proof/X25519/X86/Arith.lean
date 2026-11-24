module
public import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Spec.X25519

import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86.Reduce

/-!
# X25519 on x86 (32-bit): the field operations

Each operation of `Impl/X25519/X86.lean` on elements at offsets of the working
space, as the operation of `GF(p)` on their values modulo `p`: `mul` (by
product scanning into `T`, then `lo + 38 hi`), `add` and `sub` (three passes of a
carry or a borrow, `addSub_ok`), `mulSmall` (by 121665). Each leaves the rest of
memory unchanged but for the output and, for `mul`, `T`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

variable {W : Nat} {c : Bool}

/-! ## Numbers in any base, for `grind`'s ring normalization -/

/-- `num` in any base. -/
def numB (B : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => numB B f n + B ^ n * f n

theorem num_eq_numB (f : Nat → Nat) (n : Nat) : num f n = numB (2 ^ 32) f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [num_succ, numB, ih]

/-- Product scanning: the columns of `a b` in radix `2³²`. -/
theorem prod_identity (fa fb : Nat → Nat) :
    num (fun k => (((List.range 8).filter fun i => i ≤ k && k - i < 8).map fun i =>
      fa i * fb (k - i)).sum) 16 = num fa 8 * num fb 8 := by
  simp only [num_eq_numB]
  generalize 2 ^ 32 = B
  simp only [numB, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.filter_cons, List.filter_nil]
  simp (config := {decide := true}) only [↓reduceIte, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  grind

theorem num_16 (f : Nat → Nat) : num f 16 = num f 8 + 2 ^ 256 * num (fun k => f (8 + k)) 8 := by
  simp only [num_eq_numB]
  rw [show (2 : Nat) ^ 256 = (2 ^ 32) ^ 8 by rw [← Nat.pow_mul]]
  generalize 2 ^ 32 = B
  simp only [numB]
  grind

/-- The complements of the words. -/
theorem num_not {f : Nat → Nat} (h : ∀ k < 8, f k < 2 ^ 32) :
    num (fun k => 2 ^ 32 - 1 - f k) 8 = 2 ^ 256 - 1 - num f 8 := by
  have hs := num_add (fun k => 2 ^ 32 - 1 - f k) f 8
  have hc : num (fun k => 2 ^ 32 - 1 - f k + f k) 8 = num (fun _ => 2 ^ 32 - 1) 8 :=
    num_congr fun k hk => by have := h k hk; omega_using [this]
  have h1 : num (fun _ => 2 ^ 32 - 1) 8 = 2 ^ 256 - 1 := rfl
  omega_using [hs, hc, h1]

/-! ## Columns -/

theorem colv_le_len {m : Mem} {x : BitVec 32} {B : Nat} :
    ∀ {ts : List Term}, (∀ t ∈ ts, tval m x t ≤ B) → colv m x ts ≤ ts.length * B
  | [], _ => by simp [colv]
  | t :: ts, h => by
    have h1 := h t List.mem_cons_self
    have h2 := colv_le_len (ts := ts) fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [colv, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    rw [Nat.add_mul, Nat.one_mul]; omega_using [h1, h2]

theorem wv_lt (m : Mem) (x : BitVec 32) (d : Nat) : wv m x d < 2 ^ 32 := BitVec.isLt _

theorem wv_mul_le (m : Mem) (x : BitVec 32) (a b : Nat) : wv m x a * wv m x b ≤ 2 ^ 64 := by
  have h1 := wv_lt m x a; have h2 := wv_lt m x b
  exact Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt h1) (Nat.le_of_lt h2)) (by decide)

/-- Three offsets of elements, each either equal to or apart from the other. -/
def Apart (o a : Nat) : Prop := a = o ∨ a + 32 ≤ o ∨ o + 32 ≤ a

instance (o a : Nat) : Decidable (Apart o a) := inferInstanceAs (Decidable (a = o ∨ a + 32 ≤ o ∨ o + 32 ≤ a))

/-- The words of `[a]` a column `k` of an output at `o` reads. -/
theorem apart_read {o a k j : Nat} (h : Apart o a) (hk : k ≤ j) (hj : j < 8) :
    a + 4 * j + 4 ≤ o ∨ o + 4 * k ≤ a + 4 * j := by
  rcases h with h | h | h <;> omega_using [h, hk, hj]

/-! ## The operations -/

theorem zeroAcc_ok {s : State} :
    WP isa (.block zeroAcc) s fun s' => Keep s s' ∧ s'.mem = s.mem ∧ acc s' = 0 := by
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => Wp.wp_movi fun s₃ u₃ => WP.block_nil ?_
  refine ⟨(updKeep u₁).trans ((updKeep u₂).trans (updKeep u₃)), by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  simp only [acc, v, u₃.gpr, u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₂.gpr,
    u₂.other .ebx (by decide), u₁.gpr, toNat_zero32]

/-- The offsets the arithmetic uses: elements below `T`. -/
def Below (o : Nat) : Prop := o + 32 ≤ T

instance : DecidablePred Below := fun o => inferInstanceAs (Decidable (o + 32 ≤ T))

/-- Squaring by columns: the products of distinct words doubled, and the squares. -/
theorem sqr_identity (fa : Nat → Nat) :
    num (fun k => ((((List.range 8).filter fun i => 2 * i < k && k - i < 8).map fun i =>
      2 * (fa i * fa (k - i))) ++ if k % 2 == 0 && k < 16 then [fa (k / 2) * fa (k / 2)] else []).sum) 16 =
      num fa 8 * num fa 8 := by
  simp only [num_eq_numB]
  generalize 2 ^ 32 = B
  simp only [numB, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.filter_cons, List.filter_nil]
  simp (config := {decide := true}) only [↓reduceIte, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.nil_append, List.cons_append]
  grind

/-- The reads of a column `k` of an output at `o` from `[a + 4k]`. -/
theorem read_ok {o a k : Nat} (h : Apart o a) (ha : Below a) (hk : k < 8) :
    a + 4 * k + 4 ≤ 4096 ∧ (a + 4 * k + 4 ≤ o ∨ o + 4 * k ≤ a + 4 * k) :=
  ⟨by simp only [Below, T] at ha; omega_using [ha, hk], apart_read h (Nat.le_refl _) hk⟩

/-! ## Addition and subtraction

`addSub op o a b` runs a carry (or borrow) through the eight words three times: the words of `[a]`
and `[b]`, then 38 for the carry out and the carries it starts, then 38 into word 0 for a carry
out of that, after which the number is small (or, subtracting, large) and nothing is carried.
`PassRel op A Y c R c' B` is what a pass does to numbers below `B`: `A + Y + c = R + B c'` for `adc`,
and `A + B c' = R + Y + c` for `sbb`. -/

/-- A pass of `adc` or of `sbb`: the numbers, the carry in, the result and the carry out. -/
def PassRel (op : AluOp) (A Y c R c' B : Nat) : Prop :=
  if op = .adc then A + Y + c = R + B * c' else A + B * c' = R + Y + c

theorem PassRel.succ {op : AluOp} {A Y c₀ R c a y r c' P : Nat} (h : PassRel op A Y c₀ R c P)
    (hs : PassRel op a y c r c' (2 ^ 32)) : PassRel op (A + P * a) (Y + P * y) c₀ (R + P * r) c' (P * 2 ^ 32) := by
  unfold PassRel at *
  split at h
  · rw [ite_eq_left ‹_›] at hs ⊢
    have e := congrArg (P * ·) hs
    simp only [Nat.mul_add] at e
    rw [← Nat.mul_assoc] at e
    omega_using [h, e]
  · rw [ite_eq_right ‹_›] at hs ⊢
    have e := congrArg (P * ·) hs
    simp only [Nat.mul_add] at e
    rw [← Nat.mul_assoc] at e
    omega_using [h, e]

theorem sub3_toNat (a b : BitVec 32) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 32).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 32 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  rw [BitVec.toNat_sub, BitVec.toNat_sub, ofBool_toNat]
  by_cases h : a.toNat < b.toNat + c.toNat
  · simp only [h, decide_true, Bool.toNat_true]; omega_using [ha, hb, hc, h]
  · simp only [h, decide_false, Bool.toNat_false]; omega_using [ha, hb, hc, h]

section
open VG.X86.Wp
variable {s : State} {is : List Instr} {Q : State → Prop}

/-- `adc d, src`, with the carry `c`, and the carry out. -/
theorem wp_adcC {d : Reg} {src : Src} {y : BitVec 32} {c : Bool} (h : readSrc s src = some y)
    (hc : s.cf = some c)
    (k : ∀ t, Upd s t d (s.gpr d + y + (BitVec.ofBool c).setWidth 32) →
      t.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + y.toNat + c.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q :=
  cons (by simp only [reduceExec, execAlu, h, Option.bind_some, hc, Option.map_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `add d, src`, and the carry out. -/
theorem wp_addC {d : Reg} {src : Src} {y : BitVec 32} (h : readSrc s src = some y)
    (k : ∀ t, Upd s t d (s.gpr d + y) → t.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + y.toNat)) →
      WP isa (.block is) t Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  cons (by simp only [reduceExec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `sbb d, src`, with the borrow `c`, and the borrow out. -/
theorem wp_sbbC {d : Reg} {src : Src} {y : BitVec 32} {c : Bool} (h : readSrc s src = some y)
    (hc : s.cf = some c)
    (k : ∀ t, Upd s t d (s.gpr d - y - (BitVec.ofBool c).setWidth 32) →
      t.cf = some (decide ((s.gpr d).toNat < y.toNat + c.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sbb d src :: is)) s Q :=
  cons (by simp only [reduceExec, execAlu, h, Option.bind_some, hc, Option.map_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `mov d, [edi + o]`, which keeps the carry. -/
theorem wp_ldC {W : Nat} {c : Bool} {x : BitVec 32} (hc : Ctx W x s c) {d : Reg} {o : Nat} (ho : o + 4 ≤ 4096)
    (k : ∀ t, Upd s t d (wd s.mem x o) → t.cf = s.cf → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem (sc o)) :: is)) s Q :=
  cons (s' := s.setReg d (wd s.mem x o)) (by simp only [reduceExec, readSrc_sc hc ho, Option.map_some])
    (k _ (Upd.setReg _ _ _) rfl)

end

/-- A word of a pass: the word of `[a]`, `op` the operand's value `y` and the carry, into `[o]`. -/
theorem carryStep_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {x : BitVec 32} {s : State}
    (hc : Ctx W x s c) {o a k : Nat} (ha : a + 4 * k + 4 ≤ 4096) (ho : o + 4 * k + 4 ≤ 4096) {src : Src}
    {y : BitVec 32} {cin : Bool} (hcf : s.cf = some cin)
    (hy : ∀ t, Keep s t → t.gpr .ecx = s.gpr .ecx → t.mem = s.mem → readSrc t src = some y) :
    WP isa (.block (carryStep op o a k src)) s fun t => Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧
      ∃ r : BitVec 32, ∃ c' : Bool, t.mem = s.mem.writeW (addr x (o + 4 * k)) r ∧ t.cf = some c' ∧
        PassRel op (wv s.mem x (a + 4 * k)) y.toNat cin.toNat r.toNat c'.toNat (2 ^ 32) := by
  unfold carryStep
  refine wp_ldC hc ha fun s₁ u₁ f₁ => ?_
  have k₁ : Keep s s₁ := updKeep u₁
  have y₁ := hy s₁ k₁ (u₁.other _ (by decide)) u₁.mem
  have hw := wv_lt s.mem x (a + 4 * k)
  have hyl := y.isLt
  have hcl : cin.toNat ≤ 1 := by cases cin <;> decide
  rcases hop with rfl | rfl
  · refine wp_adcC y₁ (f₁.trans hcf) fun s₂ u₂ f₂ => ?_
    refine Wp.wp_stm ((u₂.other _ (by decide)).trans ((u₁.other _ (by decide)).trans hc.edi))
      (by rw [u₂.wr, u₁.wr]; exact hc.inW4 ho (by decide)) fun t m => WP.block_nil ?_
    refine ⟨k₁.trans ((updKeep u₂).trans ⟨by rw [m.gpr], by rw [m.gpr], by rw [m.gpr], m.rd, m.wr⟩),
      by rw [m.gpr, u₂.other _ (by decide), u₁.other _ (by decide)], _, _,
      by rw [m.mem, u₂.mem, u₁.mem], by rw [m.cf, f₂], ?_⟩
    rw [u₂.gpr, u₁.gpr, add3_toNat]
    show PassRel .adc (wv s.mem x (a + 4 * k)) y.toNat cin.toNat _ _ _
    rw [PassRel, ite_eq_left rfl, carry_toNat (by omega_using [hw, hyl, hcl])]
    exact (Nat.mod_add_div _ _).symm
  · refine wp_sbbC y₁ (f₁.trans hcf) fun s₂ u₂ f₂ => ?_
    refine Wp.wp_stm ((u₂.other _ (by decide)).trans ((u₁.other _ (by decide)).trans hc.edi))
      (by rw [u₂.wr, u₁.wr]; exact hc.inW4 ho (by decide)) fun t m => WP.block_nil ?_
    refine ⟨k₁.trans ((updKeep u₂).trans ⟨by rw [m.gpr], by rw [m.gpr], by rw [m.gpr], m.rd, m.wr⟩),
      by rw [m.gpr, u₂.other _ (by decide), u₁.other _ (by decide)], _, _,
      by rw [m.mem, u₂.mem, u₁.mem], by rw [m.cf, f₂], ?_⟩
    rw [u₂.gpr, u₁.gpr]
    show PassRel .sbb (wv s.mem x (a + 4 * k)) y.toNat cin.toNat _ _ _
    rw [PassRel, ite_eq_right (by decide)]
    exact (sub3_toNat _ _ _).symm

theorem carryPass_succ (op : AluOp) (o a n : Nat) (src : Nat → Src) :
    ((List.range (n + 1)).flatMap fun k => carryStep op o a k (src k)) =
      ((List.range n).flatMap fun k => carryStep op o a k (src k)) ++ carryStep op o a n (src n) := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The first `n` words of a pass, for operands of values `y k` whatever the words below theirs
hold. -/
theorem carryPassTo_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {x : BitVec 32} {s : State}
    (hc : Ctx W x s c) {o a : Nat} (ho : Below o) (ha : Below a) (hoa : Apart o a) {src : Nat → Src}
    {y : Nat → BitVec 32} {cin : Bool} (hcf : s.cf = some cin)
    (hy : ∀ k < 8, ∀ t, Keep s t → t.gpr .ecx = s.gpr .ecx → Frame [sub x o (4 * k)] s.mem t.mem →
      readSrc t (src k) = some (y k)) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k => carryStep op o a k (src k))) s fun t =>
      Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧ Frame [sub x o (4 * n)] s.mem t.mem ∧
        ∃ c' : Bool, t.cf = some c' ∧ PassRel op (num (fun k => wv s.mem x (a + 4 * k)) n)
          (num (fun k => (y k).toNat) n) cin.toNat (num (fun k => wv t.mem x (o + 4 * k)) n) c'.toNat
          ((2 ^ 32) ^ n)
  | 0, _ => WP.block_nil ⟨Keep.refl _, rfl, Frame.refl _ _, cin, hcf, by
      rcases hop with rfl | rfl <;> simp [PassRel, num]⟩
  | n + 1, hn => by
    simp only [Below, T] at ho ha
    have hfit := hc.fit4
    rw [carryPass_succ]
    refine WP.block_append (WP.mono (carryPassTo_ok hop hc (by simpa only [Below, T] using ho)
      (by simpa only [Below, T] using ha) hoa hcf hy n (by omega_using [hn]))
      fun t ⟨kt, et, ft, ct, hct, rt⟩ => ?_)
    have wa : wd t.mem x (a + 4 * n) = wd s.mem x (a + 4 * n) :=
      wd_frame1 ft hfit (by omega_using [ho, hn]) (by omega_using [ha, hn])
        (apart_read hoa (Nat.le_refl n) (by omega_using [hn]))
    refine WP.mono (carryStep_ok hop (kt.ctx hc) (k := n) (by omega_using [ha, hn]) (by omega_using [ho, hn]) hct
      fun u ku eu mu => hy n (by omega_using [hn]) u (kt.trans ku) (eu.trans et) (by rw [mu]; exact ft))
      fun u ⟨ku, eu, r, c', mu, cu, ru⟩ => ⟨kt.trans ku, eu.trans et, ?_, c', cu, ?_⟩
    · rw [mu]
      exact frame_write1 (frameWiden ft hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn])) hfit
        (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
    · have lowO : num (fun k => wv u.mem x (o + 4 * k)) n = num (fun k => wv t.mem x (o + 4 * k)) n :=
        num_congr fun k hk => by
          show (wd u.mem x (o + 4 * k)).toNat = (wd t.mem x (o + 4 * k)).toNat
          rw [mu, wd_write_ne _ _ (by omega_using [hfit, ho, hk, hn]) (by omega_using [hfit, ho, hn])
            (Or.inl (by omega_using [hk]))]
      have topO : wv u.mem x (o + 4 * n) = r.toNat := by
        show (wd u.mem x (o + 4 * n)).toNat = _
        rw [mu, wd_write_self]
      rw [num_succ, num_succ, num_succ, lowO, topO, Nat.pow_succ]
      have ru' : PassRel op (wv s.mem x (a + 4 * n)) (y n).toNat ct.toNat r.toNat c'.toNat (2 ^ 32) := by
        have e : wv t.mem x (a + 4 * n) = wv s.mem x (a + 4 * n) := congrArg BitVec.toNat wa
        rw [e] at ru; exact ru
      exact rt.succ ru'

/-- A pass over the eight words of `[a]`, into `[o]`. -/
theorem carryPass_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {x : BitVec 32} {s : State}
    (hc : Ctx W x s c) {o a : Nat} (ho : Below o) (ha : Below a) (hoa : Apart o a) {src : Nat → Src}
    {y : Nat → BitVec 32} {cin : Bool} (hcf : s.cf = some cin)
    (hy : ∀ k < 8, ∀ t, Keep s t → t.gpr .ecx = s.gpr .ecx → Frame [sub x o (4 * k)] s.mem t.mem →
      readSrc t (src k) = some (y k)) :
    WP isa (.block (carryPass op o a src)) s fun t => Keep s t ∧ t.gpr .ecx = s.gpr .ecx ∧
      Frame [sub x o 32] s.mem t.mem ∧ ∃ c' : Bool, t.cf = some c' ∧
        PassRel op (fe s.mem x a) (num (fun k => (y k).toNat) 8) cin.toNat (fe t.mem x o) c'.toNat (2 ^ 256) :=
  carryPassTo_ok hop hc ho ha hoa hcf hy 8 (Nat.le_refl _)

/-- The carry flag cleared. -/
theorem clearCarry_ok {s : State} :
    WP isa (.block clearCarry) s fun t => Keep s t ∧ t.mem = s.mem ∧ t.cf = some false :=
  Wp.cons (s' := (arithFlags s (s.gpr .ecx ^^^ s.gpr .ecx) false false).setReg .ecx (s.gpr .ecx ^^^ s.gpr .ecx)) rfl
    (WP.block_nil ⟨updKeep (Wp.Upd.flags _ _ _ _ _ _), rfl, rfl⟩)

/-- 38 for a carry: `ecx = 38 c`, and the carry flag cleared. -/
theorem carry38_ok {s : State} {c : Bool} (hcf : s.cf = some c) :
    WP isa (.block carry38) s fun t => Keep s t ∧ t.mem = s.mem ∧ t.cf = some false ∧
      t.gpr .ecx = BitVec.ofNat 32 (38 * c.toNat) := by
  refine Wp.wp_sbb_self hcf fun u hu => ?_
  have hv := Wp.Upd.flags u .ecx (u.gpr .ecx &&& 38) false false (u.gpr .ecx &&& 38)
  refine Wp.cons (s' := (arithFlags u (u.gpr .ecx &&& 38) false false).setReg .ecx (u.gpr .ecx &&& 38)) rfl
    (WP.block_nil ⟨(updKeep hu).trans (updKeep hv), hv.mem.trans hu.mem, rfl, ?_⟩)
  rw [hv.gpr, hu.gpr]
  cases c <;> rfl

theorem ofNat38_toNat (c : Bool) : (BitVec.ofNat 32 (38 * c.toNat)).toNat = 38 * c.toNat := by
  cases c <;> rfl

theorem num_low (f : Nat → Nat) (n : Nat) : num f (n + 1) = f 0 + 2 ^ 32 * num (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [num]
  | succ n ih =>
    rw [num_succ, ih, num_succ, Nat.mul_add, Nat.pow_succ (2 ^ 32) n, Nat.mul_comm ((2 ^ 32) ^ n) (2 ^ 32),
      Nat.mul_assoc]
    omega_using []

theorem num_first (E : BitVec 32) :
    num (fun k => (if k = 0 then E else (0 : BitVec 32)).toNat) 8 = E.toNat := by
  rw [num_low]
  have z : num (fun k => (if k + 1 = 0 then E else (0 : BitVec 32)).toNat) 7 = 0 := by
    rw [num_congr (g := fun _ => 0) fun k _ => by rw [ite_eq_right (Nat.succ_ne_zero k)]; rfl]
    rfl
  rw [z, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The end of `addSub` and of `reduceT`: the number in `ecx` added to (or subtracted from) `[o]`
through the eight words, then 38 into word 0 for a carry out. `R₂` is the number after the pass,
of which word 0 is `w` and the rest `hi`, and `r` is word 0 at the end. -/
theorem foldTail_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {x : BitVec 32} {s : State}
    (hc : Ctx W x s c) {o : Nat} (ho : Below o) (hcf : s.cf = some false) :
    WP isa (.block (carryPass op o o foldSrc ++ (carry38 ++ carryStep op o o 0 (.reg .ecx)))) s fun t =>
      Keep s t ∧ Frame [sub x o 32] s.mem t.mem ∧
      ∃ R₂ w r hi : Nat, ∃ c₂ c₃ : Bool,
        PassRel op (fe s.mem x o) (s.gpr .ecx).toNat 0 R₂ c₂.toNat (2 ^ 256) ∧
        PassRel op w (38 * c₂.toNat) 0 r c₃.toNat (2 ^ 32) ∧ R₂ = w + 2 ^ 32 * hi ∧
        fe t.mem x o = r + 2 ^ 32 * hi ∧ w < 2 ^ 32 ∧ r < 2 ^ 32 ∧ hi < 2 ^ 224 := by
  have hfit := hc.fit4
  have ho' : o + 32 ≤ 864 := ho
  refine WP.block_append (WP.mono (carryPass_ok hop hc ho ho (.inl rfl)
    (y := fun k => if k = 0 then s.gpr .ecx else 0) hcf (fun k hk t kt et _ => ?_))
    fun u₃ ⟨k₃, _, f₃, c₂, cf₃, r₃⟩ => ?_)
  · unfold foldSrc
    split
    · show some (t.gpr .ecx) = _; rw [et]
    · rfl
  rw [num_first] at r₃
  refine WP.block_append (WP.mono (carry38_ok cf₃) fun u₄ ⟨k₄, m₄, f₄, e₄⟩ => ?_)
  have c₄ := k₄.ctx (k₃.ctx hc)
  refine WP.mono (carryStep_ok hop c₄ (o := o) (a := o) (k := 0) (by omega_using [ho']) (by omega_using [ho']) f₄
    (y := BitVec.ofNat 32 (38 * c₂.toNat)) fun t _ et _ => by show some (t.gpr .ecx) = _; rw [et, e₄])
    fun t ⟨k₅, _, r, c₃, m₅, _, r₅⟩ => ?_
  rw [m₄, ofNat38_toNat, Nat.mul_zero, Nat.add_zero] at r₅
  rw [m₄, Nat.mul_zero, Nat.add_zero] at m₅
  refine ⟨k₃.trans (k₄.trans k₅), ?_, fe u₃.mem x o, wv u₃.mem x o, r.toNat,
    num (fun k => wv u₃.mem x (o + 4 * (k + 1))) 7, c₂, c₃, r₃, r₅, ?_, ?_, wv_lt _ _ _, r.isLt,
    num_lt fun _ _ => wv_lt _ _ _⟩
  · rw [m₅]
    exact frame_write1 f₃ hfit (by omega_using [ho']) (Nat.le_refl _) (by omega_using []) _
  · rw [fe, num_low]; rfl
  · rw [fe, num_low, m₅]
    have e0 : wv (u₃.mem.writeW (addr x o) r) x (o + 4 * 0) = r.toNat := by
      show (wd _ x (o + 4 * 0)).toNat = _
      rw [Nat.mul_zero, Nat.add_zero, wd_write_self]
    have eh : num (fun k => wv (u₃.mem.writeW (addr x o) r) x (o + 4 * (k + 1))) 7 =
        num (fun k => wv u₃.mem x (o + 4 * (k + 1))) 7 := num_congr fun k hk => by
      show (wd _ x (o + 4 * (k + 1))).toNat = (wd _ x (o + 4 * (k + 1))).toNat
      rw [wd_write_ne _ _ (by omega_using [hfit, ho', hk]) (by omega_using [hfit, ho']) (Or.inr (by omega_using []))]
    rw [e0, eh]

/-- The three passes of `addSub`: `R₁` after the first, `R₂` after the second, of which word 0 is
`w` and the rest `hi`, and `r` for `w` after the third. -/
theorem addSub_ok {op : AluOp} (hop : op = .adc ∨ op = .sbb) {x : BitVec 32} {s : State}
    (hc : Ctx W x s c) {o a b : Nat} (ho : Below o) (ha : Below a) (hb : Below b) (hoa : Apart o a)
    (hob : Apart o b) :
    WP isa (.block (addSub op o a b)) s fun t => Keep s t ∧ Frame [sub x o 32] s.mem t.mem ∧
      ∃ R₁ R₂ w r hi : Nat, ∃ c₁ c₂ c₃ : Bool,
        PassRel op (fe s.mem x a) (fe s.mem x b) 0 R₁ c₁.toNat (2 ^ 256) ∧
        PassRel op R₁ (38 * c₁.toNat) 0 R₂ c₂.toNat (2 ^ 256) ∧
        PassRel op w (38 * c₂.toNat) 0 r c₃.toNat (2 ^ 32) ∧ R₂ = w + 2 ^ 32 * hi ∧
        fe t.mem x o = r + 2 ^ 32 * hi ∧ R₁ < 2 ^ 256 ∧ w < 2 ^ 32 ∧ r < 2 ^ 32 ∧ hi < 2 ^ 224 := by
  have hfit := hc.fit4
  have ho' : o + 32 ≤ 864 := ho
  have hb' : b + 32 ≤ 864 := hb
  unfold addSub
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono clearCarry_ok fun u₀ ⟨k₀, m₀, f₀⟩ => ?_)
  -- The words of `[a]` and `[b]`.
  refine WP.block_append (WP.mono (carryPass_ok hop (k₀.ctx hc) ho ha hoa (y := fun k => wd s.mem x (b + 4 * k)) f₀
    (fun k hk t kt _ ft => ?_)) fun u₁ ⟨k₁, _, f₁, c₁, cf₁, r₁⟩ => ?_)
  · rw [readSrc_sc (kt.ctx (k₀.ctx hc)) (by omega_using [hb', hk])]
    exact congrArg some ((wd_frame1 ft hfit (by omega_using [ho', hk]) (by omega_using [hb', hk])
      (apart_read hob (Nat.le_refl k) hk)).trans (by rw [m₀]))
  rw [m₀] at r₁ f₁
  -- 38 for the carry out and the carries it starts, and 38 for a carry out of that.
  refine WP.block_append (WP.mono (carry38_ok cf₁) fun u₂ ⟨k₂, m₂, f₂, e₂⟩ => ?_)
  refine WP.mono (foldTail_ok hop (k₂.ctx (k₁.ctx (k₀.ctx hc))) ho f₂)
    fun t ⟨k₃, f₃, R₂, w, r, hi, c₂, c₃, r₃, r₅, eR, eF, lw, lr, lh⟩ => ?_
  rw [m₂, e₂, ofNat38_toNat] at r₃
  rw [m₂] at f₃
  exact ⟨k₀.trans (k₁.trans (k₂.trans k₃)), f₁.trans f₃, fe u₁.mem x o, R₂, w, r, hi, c₁, c₂, c₃, r₁, r₃, r₅,
    eR, eF, fe_lt _ _ _, lw, lr, lh⟩

theorem add_ok {x : BitVec 32} {s : State} (hc : Ctx W x s c) {o a b : Nat} (ho : Below o) (ha : Below a)
    (hb : Below b) (hoa : Apart o a) (hob : Apart o b) :
    WP isa (.block (add o a b)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o % P = (fe s.mem x a + fe s.mem x b) % P := by
  refine WP.mono (addSub_ok (.inl rfl) hc ho ha hb hoa hob)
    fun t ⟨kt, ft, R₁, R₂, w, r, hi, c₁, c₂, c₃, h₁, h₂, h₃, eR, eF, lR, lw, lr, _⟩ => ⟨kt, ft, ?_⟩
  simp only [PassRel, ↓reduceIte, Nat.add_zero] at h₁ h₂ h₃
  have hA := fe_lt s.mem x a
  have hB := fe_lt s.mem x b
  have b₁ : c₁.toNat ≤ 1 := by cases c₁ <;> decide
  have b₂ : c₂.toNat ≤ 1 := by cases c₂ <;> decide
  have b₃ : c₃.toNat ≤ 1 := by cases c₃ <;> decide
  generalize c₁.toNat = d₁ at *
  generalize c₂.toNat = d₂ at *
  generalize c₃.toNat = d₃ at *
  have z₃ : d₃ = 0 := by omega_using [h₁, h₂, h₃, eR, lR, lw, lr, b₁, b₂, b₃, hA, hB]
  have e : fe t.mem x o + (2 ^ 256 - 38) * (d₁ + d₂) = fe s.mem x a + fe s.mem x b := by
    omega_using [h₁, h₂, h₃, eR, eF, z₃]
  rw [← e]
  simp only [P]
  omega_using [b₁, b₂]

theorem sub_ok {x : BitVec 32} {s : State} (hc : Ctx W x s c) {o a b : Nat} (ho : Below o) (ha : Below a)
    (hb : Below b) (hoa : Apart o a) (hob : Apart o b) :
    WP isa (.block (Impl.X25519.X86.sub o a b)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      (fe s'.mem x o + fe s.mem x b) % P = fe s.mem x a % P := by
  refine WP.mono (addSub_ok (.inr rfl) hc ho ha hb hoa hob)
    fun t ⟨kt, ft, R₁, R₂, w, r, hi, c₁, c₂, c₃, h₁, h₂, h₃, eR, eF, lR, lw, lr, lh⟩ => ⟨kt, ft, ?_⟩
  simp only [PassRel, reduceCtorEq, ↓reduceIte, Nat.add_zero] at h₁ h₂ h₃
  have hA := fe_lt s.mem x a
  have hB := fe_lt s.mem x b
  have b₁ : c₁.toNat ≤ 1 := by cases c₁ <;> decide
  have b₂ : c₂.toNat ≤ 1 := by cases c₂ <;> decide
  have b₃ : c₃.toNat ≤ 1 := by cases c₃ <;> decide
  generalize c₁.toNat = d₁ at *
  generalize c₂.toNat = d₂ at *
  generalize c₃.toNat = d₃ at *
  have z₃ : d₃ = 0 := by omega_using [h₁, h₂, h₃, eR, lR, lw, lr, lh, b₁, b₂, b₃, hA, hB]
  have e : fe t.mem x o + fe s.mem x b = fe s.mem x a + (2 ^ 256 - 38) * (d₁ + d₂) := by
    omega_using [h₁, h₂, h₃, eR, eF, z₃]
  rw [e]
  simp only [P]
  omega_using [b₁, b₂]

/-! ## The reduction of a product

`reduceT o` takes the 16 words of `T` to `[o]`: a pass with a carry word, `lo + 38 hi` word by word
(`redStep_ok`, `redPass_ok`), then 38 times the carry word out added by `addSub`'s end
(`foldTail_ok`). -/

/-- A word of the reduction: `38 hi + lo` and the carry word, into `[o]`, and the next carry word. -/
theorem redStep_ok {x : BitVec 32} {s : State} (hc : Ctx W x s c) {o k : Nat} (ho : o + 4 * k + 4 ≤ 4096)
    (hk : k < 8) (hcx : s.gpr .ecx = 38) {b : Nat} (hb : v s .ebx = b) (hb' : b < 39) :
    WP isa (.block (redStep o k)) s fun t => Keep s t ∧ t.gpr .ecx = 38 ∧
      ∃ r : BitVec 32, ∃ b' : Nat, t.mem = s.mem.writeW (addr x (o + 4 * k)) r ∧ v t .ebx = b' ∧ b' < 39 ∧
        38 * wv s.mem x (T + 32 + 4 * k) + b + wv s.mem x (T + 4 * k) = r.toNat + 2 ^ 32 * b' := by
  have hT : T = 864 := rfl
  unfold redStep
  refine Wp.wp_ldm hc.edi (hc.inRW4 (by omega_using [hT, hk]) (by decide)) fun s₁ u₁ => ?_
  refine wp_mul fun s₂ u₂ => ?_
  refine Wp.wp_add fun s₃ u₃ f₃ => ?_
  refine wp_adcC rfl f₃ fun s₄ u₄ _ => ?_
  have k₄ : Keep s s₄ := (updKeep u₁).trans (u₂.keep.trans ((updKeep u₃).trans (updKeep u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_addC (readSrc_sc (k₄.ctx hc) (by omega_using [hT, hk])) fun s₅ u₅ f₅ => ?_
  refine wp_adcC rfl f₅ fun s₆ u₆ _ => ?_
  have k₆ : Keep s s₆ := k₄.trans ((updKeep u₅).trans (updKeep u₆))
  refine Wp.wp_stm (k₆.edi.trans hc.edi) (by rw [k₆.wr]; exact hc.inW4 ho (by decide)) fun s₇ m₇ => ?_
  refine Wp.wp_mov fun t u₈ => WP.block_nil ?_
  -- The words.
  have hh : (s₁.gpr .eax).toNat = wv s.mem x (T + 32 + 4 * k) := by rw [u₁.gpr]
  have e38 : (s₁.gpr .ecx).toNat = 38 := by rw [u₁.other _ (by decide), hcx]; rfl
  have hw := wv_lt s.mem x (T + 32 + 4 * k)
  have hl := wv_lt s.mem x (T + 4 * k)
  have a₂ : (s₂.gpr .eax).toNat = wv s.mem x (T + 32 + 4 * k) * 38 % 2 ^ 32 := by
    have := u₂.eax; simp only [v] at this; rw [this, hh, e38]
  have d₂ : (s₂.gpr .edx).toNat = wv s.mem x (T + 32 + 4 * k) * 38 / 2 ^ 32 := by
    have := u₂.edx; simp only [v] at this; rw [this, hh, e38]
  have b₂ : (s₂.gpr .ebx).toNat = b := by
    rw [u₂.other _ (by decide) (by decide), u₁.other _ (by decide)]; exact hb
  have a₃ : (s₃.gpr .eax).toNat = ((s₂.gpr .eax).toNat + b) % 2 ^ 32 := by
    rw [u₃.gpr, BitVec.toNat_add, b₂]
  have hA := (s₂.gpr .eax).isLt
  have hD : (s₂.gpr .edx).toNat ≤ 37 := by rw [d₂]; omega_using [hw]
  have d₄ : (s₄.gpr .edx).toNat = (s₂.gpr .edx).toNat + ((s₂.gpr .eax).toNat + b) / 2 ^ 32 := by
    rw [u₄.gpr, add3_toNat, u₃.other _ (by decide), toNat_zero32, Nat.add_zero, b₂,
      carry_toNat (by omega_using [hA, hb'])]
    exact Nat.mod_eq_of_lt (by omega_using [hA, hD, hb'])
  have l₄ : (wd s₄.mem x (T + 4 * k)).toNat = wv s.mem x (T + 4 * k) := by rw [m₄]
  have a₅ : (s₅.gpr .eax).toNat = ((s₃.gpr .eax).toNat + wv s.mem x (T + 4 * k)) % 2 ^ 32 := by
    rw [u₅.gpr, BitVec.toNat_add, u₄.other .eax (by decide), l₄]
  have hA₃ := (s₃.gpr .eax).isLt
  have d₆ : (s₆.gpr .edx).toNat =
      (s₄.gpr .edx).toNat + ((s₃.gpr .eax).toNat + wv s.mem x (T + 4 * k)) / 2 ^ 32 := by
    rw [u₆.gpr, add3_toNat, u₅.other .edx (by decide), toNat_zero32, Nat.add_zero, u₄.other .eax (by decide), l₄,
      carry_toNat (by omega_using [hA₃, hl])]
    exact Nat.mod_eq_of_lt (by rw [d₄]; omega_using [hA, hA₃, hD, hb', hl])
  have value : 38 * wv s.mem x (T + 32 + 4 * k) + b + wv s.mem x (T + 4 * k) =
      (s₅.gpr .eax).toNat + 2 ^ 32 * (s₆.gpr .edx).toNat := by
    rw [a₅, d₆, d₄, a₃, a₂, d₂]; omega_using []
  have k₇ : Keep s₆ s₇ := ⟨by rw [m₇.gpr], by rw [m₇.gpr], by rw [m₇.gpr], m₇.rd, m₇.wr⟩
  refine ⟨k₆.trans (k₇.trans (updKeep u₈)), ?_, s₆.gpr .eax, (s₆.gpr .edx).toNat, ?_, ?_, ?_, ?_⟩
  · rw [u₈.other _ (by decide), m₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide) (by decide), u₁.other _ (by decide), hcx]
  · rw [u₈.mem, m₇.mem, u₆.mem, u₅.mem, m₄]
  · show (t.gpr .ebx).toNat = _; rw [u₈.gpr, m₇.gpr]
  · have := (s₅.gpr .eax).isLt; omega_using [value, hw, hl, hb', this]
  · rw [u₆.other _ (by decide)]; exact value

/-- A word more of the pass, in numbers. -/
theorem red_succ {N Lo Hi b h l r b' P : Nat} (hv : N + P * b = Lo + 38 * Hi)
    (hs : 38 * h + b + l = r + 2 ^ 32 * b') :
    N + P * r + P * 2 ^ 32 * b' = Lo + P * l + 38 * (Hi + P * h) := by
  have e := congrArg (P * ·) hs
  simp only [Nat.mul_add] at e
  rw [← Nat.mul_assoc P (2 ^ 32) b', Nat.mul_left_comm P 38 h] at e
  omega_using [hv, e]

theorem redPass_succ (o n : Nat) :
    (List.range (n + 1)).flatMap (redStep o) = (List.range n).flatMap (redStep o) ++ redStep o n := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The first `n` words of the reduction's pass. -/
theorem redPass_ok {x : BitVec 32} {s : State} (hc : Ctx W x s c) {o : Nat} (ho : Below o)
    (hcx : s.gpr .ecx = 38) (hbx : v s .ebx = 0) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (redStep o))) s fun t => Keep s t ∧ t.gpr .ecx = 38 ∧
      Frame [sub x o (4 * n)] s.mem t.mem ∧ ∃ b : Nat, v t .ebx = b ∧ b < 39 ∧
        num (fun k => wv t.mem x (o + 4 * k)) n + (2 ^ 32) ^ n * b =
          num (fun k => wv s.mem x (T + 4 * k)) n + 38 * num (fun k => wv s.mem x (T + 32 + 4 * k)) n
  | 0, _ => WP.block_nil ⟨Keep.refl _, hcx, Frame.refl _ _, 0, hbx, by decide, by simp [num]⟩
  | n + 1, hn => by
    have ho' : o + 32 ≤ 864 := ho
    have hT : T = 864 := rfl
    have hfit := hc.fit4
    rw [redPass_succ]
    refine WP.block_append (WP.mono (redPass_ok hc ho hcx hbx n (by omega_using [hn]))
      fun t ⟨kt, et, ft, b, hb, lb, vt⟩ => ?_)
    have wT : ∀ d, T ≤ d → d + 4 ≤ 4096 → wd t.mem x d = wd s.mem x d := fun d h1 h2 =>
      wd_frame1 ft hfit (by omega_using [ho', hn]) h2 (Or.inr (by omega_using [ho', hn, hT, h1]))
    refine WP.mono (redStep_ok (kt.ctx hc) (k := n) (by omega_using [ho', hn]) (by omega_using [hn]) et hb lb)
      fun u ⟨ku, eu, r, b', mu, hb', lb', vu⟩ => ⟨kt.trans ku, eu, ?_, b', hb', lb', ?_⟩
    · rw [mu]
      exact frame_write1 (frameWiden ft hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho', hn])) hfit
        (by omega_using [ho', hn]) (by omega_using []) (by omega_using []) _
    · have lowO : num (fun k => wv u.mem x (o + 4 * k)) n = num (fun k => wv t.mem x (o + 4 * k)) n :=
        num_congr fun k hk => by
          show (wd u.mem x (o + 4 * k)).toNat = (wd t.mem x (o + 4 * k)).toNat
          rw [mu, wd_write_ne _ _ (by omega_using [hfit, ho', hk, hn]) (by omega_using [hfit, ho', hn])
            (Or.inl (by omega_using [hk]))]
      have topO : wv u.mem x (o + 4 * n) = r.toNat := by
        show (wd u.mem x (o + 4 * n)).toNat = _
        rw [mu, wd_write_self]
      have eh : wv t.mem x (T + 32 + 4 * n) = wv s.mem x (T + 32 + 4 * n) :=
        congrArg BitVec.toNat (wT _ (by omega_using []) (by omega_using [hT, hn]))
      have el : wv t.mem x (T + 4 * n) = wv s.mem x (T + 4 * n) :=
        congrArg BitVec.toNat (wT _ (by omega_using []) (by omega_using [hT, hn]))
      rw [eh, el] at vu
      rw [num_succ, num_succ, num_succ, lowO, topO, Nat.pow_succ]
      exact red_succ vt vu

/-- `reduceT`: the 512 bits of `T`, as `lo + 38 hi`, modulo `p`. -/
theorem reduceT_ok {x : BitVec 32} {s : State} (hc : Ctx W x s c) {o : Nat} (ho : Below o) :
    WP isa (.block (reduceT o)) s fun t => Keep s t ∧ Frame [sub x o 32] s.mem t.mem ∧
      fe t.mem x o % P = (num (fun k => wv s.mem x (T + 4 * k)) 8 +
        38 * num (fun k => wv s.mem x (T + 32 + 4 * k)) 8) % P := by
  have ho' : o + 32 ≤ 864 := ho
  have hfit := hc.fit4
  unfold reduceT
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine Wp.wp_movi fun s₁ u₁ => Wp.wp_movi fun s₂ u₂ => ?_
  have k₂ : Keep s s₂ := (updKeep u₁).trans (updKeep u₂)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.block_append (WP.mono (redPass_ok (k₂.ctx hc) ho u₂.gpr
    (by show (s₂.gpr .ebx).toNat = 0; rw [u₂.other _ (by decide), u₁.gpr]; rfl) 8 (Nat.le_refl _))
    fun s₃ ⟨k₃, _, f₃, b, hb, lb, v₃⟩ => ?_)
  rw [m₂] at v₃ f₃
  -- 38 times the carry word, and the carry flag cleared.
  refine Wp.wp_movi fun s₄ u₄ => wp_mul fun s₅ u₅ => Wp.wp_mov fun s₆ u₆ => ?_
  refine Wp.cons (s' := arithFlags s₆ (s₆.gpr .ecx &&& s₆.gpr .ecx) false false) rfl ?_
  have k₆ : Keep s₃ s₆ := (updKeep u₄).trans (u₅.keep.trans (updKeep u₆))
  have m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have e₆ : (s₆.gpr .ecx).toNat = 38 * b := by
    have h := u₅.eax
    simp only [v] at h hb
    rw [u₆.gpr, h, u₄.gpr, u₄.other _ (by decide), hb, toNat_38]
    exact Nat.mod_eq_of_lt (by omega_using [lb])
  have c₇ : Ctx W x (arithFlags s₆ (s₆.gpr .ecx &&& s₆.gpr .ecx) false false) c :=
    (k₆.ctx (k₃.ctx (k₂.ctx hc))).keep rfl rfl rfl
  refine WP.mono (foldTail_ok (.inl rfl) c₇ ho rfl)
    fun t ⟨k₈, f₈, R₂, w, r, hi, c₂, c₃, r₈, r₉, eR, eF, lw, lr, _⟩ => ?_
  have k₇ : Keep s₆ (arithFlags s₆ (s₆.gpr .ecx &&& s₆.gpr .ecx) false false) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨k₂.trans (k₃.trans (k₆.trans (k₇.trans k₈))), ?_, ?_⟩
  · have f₈' : Frame [sub x o 32] s₃.mem t.mem := by rw [← m₆]; exact f₈
    exact f₃.trans f₈'
  · have r₈' : PassRel .adc (fe s₃.mem x o) (38 * b) 0 R₂ c₂.toNat (2 ^ 256) := by
      rw [← m₆, ← e₆]; exact r₈
    simp only [PassRel, ↓reduceIte, Nat.add_zero] at r₈' r₉
    have b₂ : c₂.toNat ≤ 1 := by cases c₂ <;> decide
    have b₃ : c₃.toNat ≤ 1 := by cases c₃ <;> decide
    have hR := fe_lt s₃.mem x o
    rw [show ((2 : Nat) ^ 32) ^ 8 = 2 ^ 256 by decide] at v₃
    have v₃' : fe s₃.mem x o + 2 ^ 256 * b = _ := v₃
    rw [← v₃']
    generalize fe s₃.mem x o = R₁ at r₈' hR ⊢
    generalize c₂.toNat = d₂ at r₈' r₉ b₂
    generalize c₃.toNat = d₃ at r₉ b₃
    have z₃ : d₃ = 0 := by omega_using [r₈', r₉, eR, lw, lr, lb, b₂, b₃, hR]
    have e : fe t.mem x o + (2 ^ 256 - 38) * (d₂ + b) = R₁ + 2 ^ 256 * b := by
      omega_using [r₈', r₉, eR, eF, z₃]
    rw [← e]
    simp only [P]
    omega_using [b₂, lb]

/-- 16 columns summed into `T`, then reduced to `[o]`: the value of the columns modulo `p`, when
they read only below `T` and each is below `2⁶⁸`. -/
theorem mulCols_ok {x : BitVec 32} {s : State} (hc : Ctx W x s c) {o : Nat} (ho : Below o)
    (ts : Nat → List Term) (hr : ∀ k < 16, ∀ t ∈ ts k, ∀ d ∈ treads t, d + 4 ≤ T)
    (hb : ∀ k < 16, colv s.mem x (ts k) < 2 ^ 68) {V : Nat} (hV : V < 2 ^ 256 * 2 ^ 256)
    (hv : num (fun k => colv s.mem x (ts k)) 16 = V) :
    WP isa (.block (mulCols o ts)) s fun s' => Keep s s' ∧ Frame [sub x o 32, sub x T 64] s.mem s'.mem ∧
      fe s'.mem x o % P = V % P := by
  have hoB : Below o := ho
  simp only [Below, T] at ho
  have hfit := hc.fit4
  refine WP.block_append (WP.block_append (WP.mono zeroAcc_ok fun s₁ ⟨k₁, m₁, a₁⟩ => ?_))
  have c₁ := k₁.ctx hc
  refine WP.mono (cols_ok c₁ ts 16 (by simp only [T]; decide) (fun k hk t ht d hd => ?_)
    (fun k hk => ?_) (by rw [a₁]; decide)) fun s₂ ⟨k₂, f₂, e₂, _⟩ => ?_
  · have := hr k hk t ht d hd
    simp only [T] at this ⊢
    exact ⟨by omega_using [this], .inl this⟩
  · rw [m₁]; exact hb k hk
  · -- The product, in `T`.
    rw [a₁, Nat.zero_add, m₁, hv] at e₂
    have e₃ : num (fun k => wv s₂.mem x (T + 4 * k)) 16 = V := by
      have hQ : ((2 : Nat) ^ 32) ^ 16 = 2 ^ 256 * 2 ^ 256 := by decide
      rw [hQ] at e₂
      have : acc s₂ = 0 := by
        rcases Nat.eq_zero_or_pos (acc s₂) with h | h
        · exact h
        · have := Nat.mul_le_mul_left (2 ^ 256 * 2 ^ 256) h
          omega_using [this, e₂, hV]
      rw [this, Nat.mul_zero, Nat.add_zero] at e₂
      exact e₂
    rw [num_16] at e₃
    have c₂ := k₂.ctx c₁
    refine WP.mono (reduceT_ok c₂ hoB) fun s₃ ⟨k₃, f₃, e₄⟩ => ⟨k₁.trans (k₂.trans k₃), ?_, ?_⟩
    · rw [m₁] at f₂
      exact (f₂.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
        (f₃.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
    · have eh : num (fun k => wv s₂.mem x (T + 4 * (8 + k))) 8 = num (fun k => wv s₂.mem x (T + 32 + 4 * k)) 8 :=
        num_congr fun k _ => by rw [show T + 4 * (8 + k) = T + 32 + 4 * k by omega_using []]
      rw [e₄, ← eh, ← fold256, ← e₃]

theorem mul_ok {x : BitVec 32} {s : State} (hc : Ctx W x s c) {o a b : Nat} (ho : Below o) (ha : Below a)
    (hb : Below b) :
    WP isa (.block (mul o a b)) s fun s' => Keep s s' ∧ Frame [sub x o 32, sub x T 64] s.mem s'.mem ∧
      fe s'.mem x o % P = fe s.mem x a * fe s.mem x b % P := by
  simp only [Below, T] at ha hb
  have hA := fe_lt s.mem x a; have hB := fe_lt s.mem x b
  have hAB : fe s.mem x a * fe s.mem x b < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul_of_lt_of_lt hA hB
  unfold mul mulSq mulPr
  split
  · subst b
    refine mulCols_ok hc ho _ (fun k hk t ht d hd => ?_) (fun k hk => ?_) hAB ?_
    · simp only [sqrTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        Bool.and_eq_true, decide_eq_true_eq] at ht
      rcases ht with ⟨i, ⟨hi, -, hki⟩, rfl⟩ | ht
      · simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
        simp only [T]
        rcases hd with rfl | rfl <;> omega_using [ha, hi, hki]
      · split at ht
        · rename_i hk2
          simp only [beq_iff_eq] at hk2
          simp only [List.mem_singleton] at ht
          subst ht
          simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
          simp only [T]
          rcases hd with rfl | rfl <;> omega_using [ha, hk2]
        · exact absurd ht List.not_mem_nil
    · have hl : (sqrTerms a k).length ≤ 5 := by
        simp only [sqrTerms, List.length_append, List.length_map]
        have := (by decide : ∀ k < 16, ((List.range 8).filter fun i => 2 * i < k && k - i < 8).length ≤ 4) k hk
        split <;> simp only [List.length_cons, List.length_nil] <;> omega_using [this]
      have h1 := colv_le_len (m := s.mem) (x := x) (B := 2 ^ 65) (ts := sqrTerms a k) fun t ht => by
        simp only [sqrTerms, List.mem_append, List.mem_map] at ht
        rcases ht with ⟨i, -, rfl⟩ | ht
        · have := wv_mul_le s.mem x (a + 4 * i) (a + 4 * (k - i))
          simp only [tval]; omega_using [this]
        · split at ht
          · simp only [List.mem_singleton] at ht
            subst ht
            have := wv_mul_le s.mem x (a + 4 * (k / 2)) (a + 4 * (k / 2))
            simp only [tval]; omega_using [this]
          · exact absurd ht List.not_mem_nil
      have h2 := Nat.mul_le_mul_right (2 ^ 65) hl
      omega_using [h1, h2]
    · have hcol : ∀ k, colv s.mem x (sqrTerms a k) = ((((List.range 8).filter fun i => 2 * i < k && k - i < 8).map
          fun i => 2 * (wv s.mem x (a + 4 * i) * wv s.mem x (a + 4 * (k - i)))) ++
          if k % 2 == 0 && k < 16 then [wv s.mem x (a + 4 * (k / 2)) * wv s.mem x (a + 4 * (k / 2))]
          else []).sum := fun k => by
        unfold colv sqrTerms
        rw [List.map_append, List.map_map]
        split <;> rfl
      simp only [hcol]
      exact sqr_identity (fun i => wv s.mem x (a + 4 * i))
  · refine mulCols_ok hc ho _ (fun k hk t ht d hd => ?_) (fun k hk => ?_) hAB ?_
    · simp only [prodTerms, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq] at ht
      obtain ⟨i, ⟨hi, -, hki⟩, rfl⟩ := ht
      simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
      simp only [T]
      rcases hd with rfl | rfl <;> omega_using [ha, hb, hi, hki]
    · have hl : (prodTerms a b k).length ≤ 8 := by
        simp only [prodTerms, List.length_map]
        exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      have h1 := colv_le_len (m := s.mem) (x := x) (B := 2 ^ 64) (ts := prodTerms a b k) fun t ht => by
        simp only [prodTerms, List.mem_map] at ht
        obtain ⟨i, -, rfl⟩ := ht
        exact wv_mul_le _ _ _ _
      have h2 := Nat.mul_le_mul_right (2 ^ 64) hl
      omega_using [h1, h2]
    · have hcol : ∀ k, colv s.mem x (prodTerms a b k) = (((List.range 8).filter fun i => i ≤ k && k - i < 8).map
          fun i => wv s.mem x (a + 4 * i) * wv s.mem x (b + 4 * (k - i))).sum := fun k => by
        simp only [colv, prodTerms, List.map_map]; rfl
      simp only [hcol]
      exact prod_identity (fun i => wv s.mem x (a + 4 * i)) (fun j => wv s.mem x (b + 4 * j))

theorem mulSmall_ok {x : BitVec 32} {s : State} (hc : Ctx W x s c) {o a : Nat} (ho : Below o) (ha : Below a)
    (hoa : Apart o a) :
    WP isa (.block (mulSmall o a)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o % P = 121665 * fe s.mem x a % P := by
  have hs : num (fun k => colv s.mem x [.mulI (a + 4 * k) 121665]) 8 = 121665 * fe s.mem x a := by
    rw [fe, ← num_mul]
    refine num_congr fun k _ => ?_
    simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.mul_comm (wv _ _ _)]
    rfl
  refine WP.mono (linear_ok hc o _ (by simp only [Below, T] at ho; omega_using [ho])
    (fun k hk t ht d hd => ?_) (fun k _ => ?_) ?_) fun s' ⟨k', f', e'⟩ => ⟨k', f', by rw [e', hs]⟩
  · simp only [List.mem_singleton] at ht; subst ht
    simp only [treads, List.mem_singleton] at hd; subst hd
    exact read_ok hoa ha hk
  · simp only [colv, tval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 := wv_lt s.mem x (a + 4 * k)
    have : wv s.mem x (a + 4 * k) * (121665 : BitVec 32).toNat ≤ 2 ^ 32 * 121665 :=
      Nat.mul_le_mul (Nat.le_of_lt h1) (by decide)
    omega_using [this]
  · rw [hs]; have h1 := fe_lt s.mem x a; omega_using [h1]

end VG.Proof.X25519.X86
