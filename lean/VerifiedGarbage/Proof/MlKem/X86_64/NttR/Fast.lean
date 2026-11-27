module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sym

/-!
# ML-KEM on x86-64: the NTT on registers, the machine's run for the kernel

`St.step` (`Sym.lean`) finds each word of a register by its index in the
registers the instruction reads (`Y.ofFn`, `Y.get`): the kernel walks a list
for every word of every instruction, more than half of what it evaluates in
a run (`Run.lean`). `St.stepF` is the same step (`St.stepF_eq`) for the
kernel: it takes the sixteen words of each register it reads in one walk
(`Y.app16`) and writes the result out word by word (`binL`, `shiftL`,
`blendL`: `binW`, `shiftW` and `blendW` at each index), finds an entry of
the table of constants from the one before (`drop4`), and takes the zetas
`zmTab`, and `St.step` for any other instruction, as parameters. The
literals of the runs (`RunR100.lean`, …) are evaluated with
`St.runF zmTab R (St.step R rs)`, which is `St.run R rs` (`St.runF_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR

/-- A function of sixteen words. -/
abbrev Fn16 (α : Type) : Type :=
  E → E → E → E → E → E → E → E → E → E → E → E → E → E → E → E → α

/-! ## The zetas as a parameter

`mkAdd` and `mkSub` with the function `zt` for `zmTab`, and `St.stepF` with
`step` for `St.step R rs`: the term of a run names `zmTab` and `St.step`, in
which `materialize_value` then reads the zetas from their table
(`ZmLit.lean`), where the kernel would evaluate the power of each one. (Were
`St.runF` itself to lead to `zmTab`, it would be unfolded down to it, and to
check that unfolding the kernel evaluates the list the recursion is on: a
pass, by its register allocation, before it is rewritten to its literal.) -/

/-- `bflyOk`, the zetas from `zt`. -/
def bflyOkZ (zt : Nat → Nat) (R : Rules) (st p p' z z' : Nat) : Bool :=
  match R.ops[st]? with
  | some (.ct len) => pairOk len p p' && z == zt (128 / len + p / (2 * len)) && z' == z * qinvN % 65536
  | _ => false

/-- `gsOk`, the zetas from `zt`. -/
def gsOkZ (zt : Nat → Nat) (R : Rules) (st p p' z z' : Nat) : Bool :=
  match R.ops[st]? with
  | some (.gs len) => pairOk len p p' && z == zt (256 / len - 1 - p / (2 * len)) && z' == z * qinvN % 65536
  | _ => false

/-- `mkAdd`, the zetas from `zt`. -/
def mkAddZ (zt : Nat → Nat) (R : Rules) (a b : E) : E :=
  if a.isJunk || b.isJunk then .junk else
  match a, b with
  | .lv st p, .sub (.mhi (.lv st₁ p') (.c z)) (.mhi (.mlo (.lv st₂ p'') (.c z')) (.c q)) =>
    if st₁ == st && st₂ == st && p'' == p' && q == qN && bflyOkZ zt R st p p' z z' then .lv (st + 1) p
    else .add a b
  | .lv st p, .lv st₁ p' =>
    if st₁ == st && gsPairOk R st p p' then .lv (st + 1) p else .add a b
  | .sub (.mhi (.lv st p) (.c z)) (.mhi (.mlo (.lv st₁ p₁) (.c z')) (.c q)),
    .and (.sra r) (.c q') =>
    if st == R.ops.length && st₁ == st && p₁ == p && q == qN && q' == qN && z == R.fin &&
      z' == R.fin * qinvN % 65536 && r.beq a && p < 256 then .out p
    else .add a b
  | _, _ => .add a b

/-- `mkSub`, the zetas from `zt`. -/
def mkSubZ (zt : Nat → Nat) (R : Rules) (a b : E) : E :=
  if a.isJunk || b.isJunk then .junk else
  match a, b with
  | .lv st p, .sub (.mhi (.lv st₁ p') (.c z)) (.mhi (.mlo (.lv st₂ p'') (.c z')) (.c q)) =>
    if st₁ == st && st₂ == st && p'' == p' && q == qN && bflyOkZ zt R st p p' z z' then .lv (st + 1) p'
    else .sub a b
  | .mhi (.sub (.lv st p') (.lv st₁ p)) (.c z),
    .mhi (.mlo (.sub (.lv st₂ p'') (.lv st₃ p₁)) (.c z')) (.c q) =>
    if st₁ == st && st₂ == st && st₃ == st && p'' == p' && p₁ == p && q == qN && gsOkZ zt R st p p' z z' then
      .lv (st + 1) p'
    else .sub a b
  | .mhi (.lv st p) (.c z), .mhi (.mlo (.lv st₁ p₁) (.c z')) (.c q) =>
    if st₁ == st && p₁ == p && q == qN && z == zt 0 && z' == zt 0 * qinvN % 65536 && redOk R st && p < 256 then
      .lv (st + 1) p
    else .sub a b
  | _, _ => .sub a b

theorem mkAddZ_eq (R : Rules) : mkAddZ zmTab R = mkAdd R := rfl

theorem mkSubZ_eq (R : Rules) : mkSubZ zmTab R = mkSub R := rfl

/-! ## The words written out -/

/-- The first word of `a` and the others. -/
def Y.uncons : Y → E × Y
  | [] => (.junk, [])
  | x :: a => (x, a)

/-- `k` of the sixteen words of `a` (`a.get 0`, …, `a.get 15`), each from the
words after the one before: the kernel walks `a` once, where an index walks
it from its head for every word. -/
def Y.app16 {α : Type} (a : Y) (k : Fn16 α) : α :=
  let u0 := a.uncons
  let u1 := u0.2.uncons
  let u2 := u1.2.uncons
  let u3 := u2.2.uncons
  let u4 := u3.2.uncons
  let u5 := u4.2.uncons
  let u6 := u5.2.uncons
  let u7 := u6.2.uncons
  let u8 := u7.2.uncons
  let u9 := u8.2.uncons
  let u10 := u9.2.uncons
  let u11 := u10.2.uncons
  let u12 := u11.2.uncons
  let u13 := u12.2.uncons
  let u14 := u13.2.uncons
  let u15 := u14.2.uncons
  k u0.1 u1.1 u2.1 u3.1 u4.1 u5.1 u6.1 u7.1
    u8.1 u9.1 u10.1 u11.1 u12.1 u13.1 u14.1 u15.1

theorem Y.uncons_eq (a : Y) : a.uncons = (a.get 0, a.tail) := by cases a <;> rfl

theorem Y.get_tail (a : Y) (n : Nat) : Y.get a.tail n = a.get (n + 1) := by cases a <;> rfl

theorem Y.app16_eq {α : Type} (a : Y) (k : Fn16 α) :
    a.app16 k = k (a.get 0) (a.get 1) (a.get 2) (a.get 3) (a.get 4) (a.get 5) (a.get 6) (a.get 7)
      (a.get 8) (a.get 9) (a.get 10) (a.get 11) (a.get 12) (a.get 13) (a.get 14) (a.get 15) := by
  simp only [Y.app16, Y.uncons_eq, Y.get_tail]

/-- `binW` at each word, of the registers with the words `a0`, … and `b0`, …,
for the operations the machine follows (`binOk`), with `add` and `sub` for
`mkAdd R` and `mkSub R`: the operation first, so that the kernel instantiates
only its sixteen words. -/
def binL (add sub : E → E → E) (op : VBinOp) : Fn16 (Fn16 Y) :=
  match op with
  | .vpaddw => fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
    [add a0 b0, add a1 b1, add a2 b2, add a3 b3,
     add a4 b4, add a5 b5, add a6 b6, add a7 b7,
     add a8 b8, add a9 b9, add a10 b10, add a11 b11,
     add a12 b12, add a13 b13, add a14 b14, add a15 b15]
  | .vpsubw => fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
    [sub a0 b0, sub a1 b1, sub a2 b2, sub a3 b3,
     sub a4 b4, sub a5 b5, sub a6 b6, sub a7 b7,
     sub a8 b8, sub a9 b9, sub a10 b10, sub a11 b11,
     sub a12 b12, sub a13 b13, sub a14 b14, sub a15 b15]
  | .vpmullw => fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
    [mk2 .mlo a0 b0, mk2 .mlo a1 b1, mk2 .mlo a2 b2, mk2 .mlo a3 b3,
     mk2 .mlo a4 b4, mk2 .mlo a5 b5, mk2 .mlo a6 b6, mk2 .mlo a7 b7,
     mk2 .mlo a8 b8, mk2 .mlo a9 b9, mk2 .mlo a10 b10, mk2 .mlo a11 b11,
     mk2 .mlo a12 b12, mk2 .mlo a13 b13, mk2 .mlo a14 b14, mk2 .mlo a15 b15]
  | .vpmulhw => fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
    [mk2 .mhi a0 b0, mk2 .mhi a1 b1, mk2 .mhi a2 b2, mk2 .mhi a3 b3,
     mk2 .mhi a4 b4, mk2 .mhi a5 b5, mk2 .mhi a6 b6, mk2 .mhi a7 b7,
     mk2 .mhi a8 b8, mk2 .mhi a9 b9, mk2 .mhi a10 b10, mk2 .mhi a11 b11,
     mk2 .mhi a12 b12, mk2 .mhi a13 b13, mk2 .mhi a14 b14, mk2 .mhi a15 b15]
  | .vpand => fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
    [mk2 .and a0 b0, mk2 .and a1 b1, mk2 .and a2 b2, mk2 .and a3 b3,
     mk2 .and a4 b4, mk2 .and a5 b5, mk2 .and a6 b6, mk2 .and a7 b7,
     mk2 .and a8 b8, mk2 .and a9 b9, mk2 .and a10 b10, mk2 .and a11 b11,
     mk2 .and a12 b12, mk2 .and a13 b13, mk2 .and a14 b14, mk2 .and a15 b15]
  | .vpxor => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    [.c 0, .c 0, .c 0, .c 0, .c 0, .c 0, .c 0, .c 0,
     .c 0, .c 0, .c 0, .c 0, .c 0, .c 0, .c 0, .c 0]
  | .vpackssdw => fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
    [pk a0 a1, pk a2 a3, pk a4 a5, pk a6 a7,
     pk b0 b1, pk b2 b3, pk b4 b5, pk b6 b7,
     pk a8 a9, pk a10 a11, pk a12 a13, pk a14 a15,
     pk b8 b9, pk b10 b11, pk b12 b13, pk b14 b15]
  | .vpunpcklwd => fun a0 a1 a2 a3 _ _ _ _ a8 a9 a10 a11 _ _ _ _
      b0 b1 b2 b3 _ _ _ _ b8 b9 b10 b11 _ _ _ _ =>
    [a0, b0, a1, b1, a2, b2, a3, b3,
     a8, b8, a9, b9, a10, b10, a11, b11]
  | .vpunpckhwd => fun _ _ _ _ a4 a5 a6 a7 _ _ _ _ a12 a13 a14 a15
      _ _ _ _ b4 b5 b6 b7 _ _ _ _ b12 b13 b14 b15 =>
    [a4, b4, a5, b5, a6, b6, a7, b7,
     a12, b12, a13, b13, a14, b14, a15, b15]
  | .vpunpckldq => fun a0 a1 a2 a3 _ _ _ _ a8 a9 a10 a11 _ _ _ _
      b0 b1 b2 b3 _ _ _ _ b8 b9 b10 b11 _ _ _ _ =>
    [a0, a1, b0, b1, a2, a3, b2, b3,
     a8, a9, b8, b9, a10, a11, b10, b11]
  | .vpunpckhdq => fun _ _ _ _ a4 a5 a6 a7 _ _ _ _ a12 a13 a14 a15
      _ _ _ _ b4 b5 b6 b7 _ _ _ _ b12 b13 b14 b15 =>
    [a4, a5, b4, b5, a6, a7, b6, b7,
     a12, a13, b12, b13, a14, a15, b14, b15]
  | .vpunpcklqdq => fun a0 a1 a2 a3 _ _ _ _ a8 a9 a10 a11 _ _ _ _
      b0 b1 b2 b3 _ _ _ _ b8 b9 b10 b11 _ _ _ _ =>
    [a0, a1, a2, a3, b0, b1, b2, b3,
     a8, a9, a10, a11, b8, b9, b10, b11]
  | .vpunpckhqdq => fun _ _ _ _ a4 a5 a6 a7 _ _ _ _ a12 a13 a14 a15
      _ _ _ _ b4 b5 b6 b7 _ _ _ _ b12 b13 b14 b15 =>
    [a4, a5, a6, a7, b4, b5, b6, b7,
     a12, a13, a14, a15, b12, b13, b14, b15]
  | _ => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => []

/-- `shiftW` at each word, for the shifts the machine follows (`shiftOk`). -/
def shiftL (op : XShiftOp) : Fn16 Y :=
  match op with
  | .psllq => fun a0 a1 _ _ a4 a5 _ _ a8 a9 _ _ a12 a13 _ _ =>
    [.c 0, .c 0, a0, a1, .c 0, .c 0, a4, a5,
     .c 0, .c 0, a8, a9, .c 0, .c 0, a12, a13]
  | .psrlq => fun _ _ a2 a3 _ _ a6 a7 _ _ a10 a11 _ _ a14 a15 =>
    [a2, a3, .c 0, .c 0, a6, a7, .c 0, .c 0,
     a10, a11, .c 0, .c 0, a14, a15, .c 0, .c 0]
  | .psraw => fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =>
    [mkSra a0, mkSra a1, mkSra a2, mkSra a3,
     mkSra a4, mkSra a5, mkSra a6, mkSra a7,
     mkSra a8, mkSra a9, mkSra a10, mkSra a11,
     mkSra a12, mkSra a13, mkSra a14, mkSra a15]
  | _ => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => []

/-- `blendW` at each word. -/
def blendL (sel : Nat) : Fn16 (Fn16 Y) :=
  fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
    [if sel.testBit 0 then b0 else a0, if sel.testBit 0 then b1 else a1,
     if sel.testBit 1 then b2 else a2, if sel.testBit 1 then b3 else a3,
     if sel.testBit 2 then b4 else a4, if sel.testBit 2 then b5 else a5,
     if sel.testBit 3 then b6 else a6, if sel.testBit 3 then b7 else a7,
     if sel.testBit 4 then b8 else a8, if sel.testBit 4 then b9 else a9,
     if sel.testBit 5 then b10 else a10, if sel.testBit 5 then b11 else a11,
     if sel.testBit 6 then b12 else a12, if sel.testBit 6 then b13 else a13,
     if sel.testBit 7 then b14 else a14, if sel.testBit 7 then b15 else a15]

theorem binL_eq (R : Rules) (op : VBinOp) (same : Bool) (h : binOk op same = true) (a b : Y) :
    binL (mkAdd R) (mkSub R) op (a.get 0) (a.get 1) (a.get 2) (a.get 3) (a.get 4) (a.get 5) (a.get 6) (a.get 7)
      (a.get 8) (a.get 9) (a.get 10) (a.get 11) (a.get 12) (a.get 13) (a.get 14) (a.get 15)
      (b.get 0) (b.get 1) (b.get 2) (b.get 3) (b.get 4) (b.get 5) (b.get 6) (b.get 7)
      (b.get 8) (b.get 9) (b.get 10) (b.get 11) (b.get 12) (b.get 13) (b.get 14) (b.get 15) =
    Y.ofFn (binW R op a b) := by
  cases op <;> first | rfl | exact absurd h Bool.false_ne_true

theorem shiftL_eq (op : XShiftOp) (n : Nat) (h : shiftOk op n = true) (a : Y) :
    shiftL op (a.get 0) (a.get 1) (a.get 2) (a.get 3) (a.get 4) (a.get 5) (a.get 6) (a.get 7)
      (a.get 8) (a.get 9) (a.get 10) (a.get 11) (a.get 12) (a.get 13) (a.get 14) (a.get 15) = Y.ofFn (shiftW op a) := by
  cases op <;> first | rfl | exact absurd h Bool.false_ne_true

theorem blendL_eq (sel : Nat) (a b : Y) :
    blendL sel (a.get 0) (a.get 1) (a.get 2) (a.get 3) (a.get 4) (a.get 5) (a.get 6) (a.get 7)
      (a.get 8) (a.get 9) (a.get 10) (a.get 11) (a.get 12) (a.get 13) (a.get 14) (a.get 15)
      (b.get 0) (b.get 1) (b.get 2) (b.get 3) (b.get 4) (b.get 5) (b.get 6) (b.get 7)
      (b.get 8) (b.get 9) (b.get 10) (b.get 11) (b.get 12) (b.get 13) (b.get 14) (b.get 15) =
    Y.ofFn (blendW sel a b) := rfl

/-! ## The table of zetas

`St.step` drops the quadwords before an entry of the table, from its head
for every instruction that reads one: most of the run of `NTT⁻¹`, whose
entries are the last of the table. `drop4 ws k` is the table from quadword
`4 k` on, from `drop4 ws (k - 1)`: the kernel evaluates each of these once
for all the instructions of a run (it remembers the value of a term). -/

/-- `ws.drop (4 * k)`, by fours. -/
def drop4 (ws : List (BitVec 64)) : Nat → List (BitVec 64)
  | 0 => ws
  | k + 1 => (drop4 ws k).drop 4

theorem drop4_eq (ws : List (BitVec 64)) (k : Nat) : drop4 ws k = ws.drop (4 * k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [drop4, ih, List.drop_drop, Nat.mul_succ]

theorem drop4_drop (ws : List (BitVec 64)) (n : Nat) : (drop4 ws (n / 4)).drop (n % 4) = ws.drop n := by
  rw [drop4_eq, List.drop_drop, Nat.div_add_mod]

/-! ## The machine -/

/-- `step` (for `St.step R rs`), with the zetas from `zt`, the words of a
binary operation, a shift or a blend written out from those of the registers
it reads, and the table read by `drop4`. -/
def St.stepF (zt : Nat → Nat) (R : Rules) (step : St → Instr → Option St) (σ : St) : Instr → Option St
  | .vop (.vbin op .l256 d a b) =>
    if binOk op (a == b) then
      some (σ.set d ((σ.reg b).app16 ((σ.reg a).app16 (binL (mkAddZ zt R) (mkSubZ zt R) op))))
    else none
  | .vop (.vshift op .l256 d a n) =>
    if shiftOk op n.toNat then some (σ.set d ((σ.reg a).app16 (shiftL op))) else none
  | .vop (.vpblendd .l256 d a b sel) =>
    some (σ.set d ((σ.reg b).app16 ((σ.reg a).app16 (blendL sel.toNat))))
  | .vmovdquTbl d m name ws =>
    if m.base = .r8 ∧ m.index = none ∧ name = tblName ∧ 0 ≤ m.disp ∧ m.disp.toNat % 8 = 0 ∧
        m.disp.toNat / 8 + 4 ≤ ws.length ∧ m.disp.toNat < 2 ^ 32 then
      match (drop4 ws (m.disp.toNat / 8 / 4)).drop (m.disp.toNat / 8 % 4) with
      | a :: b :: c :: e :: _ => some (σ.set d (Y.ofFn fun i => tblW [a, b, c, e] (i / 4) (i % 4)))
      | _ => none
    else none
  | i => step σ i

theorem St.stepF_eq (R : Rules) (rs : List Rg) (σ : St) (i : Instr) :
    σ.stepF zmTab R (St.step R rs) i = σ.step R rs i := by
  unfold St.stepF
  split
  · next op d a b =>
    split
    · rename_i h
      rw [Y.app16_eq, Y.app16_eq, mkAddZ_eq, mkSubZ_eq, binL_eq R op _ h]
      exact (ite_eq_left (c := binOk op (a == b) = true) h).symm
    · rename_i h
      exact (ite_eq_right (c := binOk op (a == b) = true) h).symm
  · next op d a n =>
    split
    · rename_i h
      rw [Y.app16_eq, shiftL_eq op _ h]
      exact (ite_eq_left (c := shiftOk op n.toNat = true) h).symm
    · rename_i h
      exact (ite_eq_right (c := shiftOk op n.toNat = true) h).symm
  · rw [Y.app16_eq, Y.app16_eq, blendL_eq]
    rfl
  · rw [drop4_drop]
    rfl
  · rfl

/-- `St.run` by `St.stepF`. -/
def St.runF (zt : Nat → Nat) (R : Rules) (step : St → Instr → Option St) (σ : St) : List Instr → Option St
  | [] => some σ
  | i :: is => (σ.stepF zt R step i).bind fun σ' => σ'.runF zt R step is

theorem St.runF_eq (R : Rules) (rs : List Rg) (σ : St) (is : List Instr) :
    σ.runF zmTab R (St.step R rs) is = σ.run R rs is := by
  induction is generalizing σ with
  | nil => rfl
  | cons i is ih =>
    rw [St.runF, St.run, St.stepF_eq]
    exact congrArg _ (funext ih)

end VG.Proof.MlKem.X86_64.NttR
