import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Scrypt.Spec
import VerifiedGarbage.Impl.Scrypt.X86.Salsa

/-!
# The Salsa20/8 Core on x86 (32-bit), with SSE2: the rounds

The sixteen words are in `xmm0, …, xmm3`, in one of three arrangements
(`Arr`): the rows of the matrix (`rowIdx`, as loaded), its columns starting
from the diagonal (`ci`, for the column round) or its rows starting from the
diagonal (`ri`, for the row round). `vstep_ok` executes one line on each
doubleword, `vhalf_ok` a quarter round on each; `col_get` and `row_get` say
that the column and row rounds of the specification are quarter rounds on
those words, and `doubleRound_ok` composes them. `toDiag_ok` and
`fromDiag_ok` move between the rows and the columns.
-/

namespace VG.Proof.Scrypt.X86

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt (stepN stepN_get)

/-! ## Doublewords -/

theorem shuf39 (x : BitVec 128) :
    shufDwords x 0x39 = ofDwords (dword x 1) (dword x 2) (dword x 3) (dword x 0) := rfl
theorem shuf4e (x : BitVec 128) :
    shufDwords x 0x4e = ofDwords (dword x 2) (dword x 3) (dword x 0) (dword x 1) := rfl
theorem shuf93 (x : BitVec 128) :
    shufDwords x 0x93 = ofDwords (dword x 3) (dword x 0) (dword x 1) (dword x 2) := rfl

/-- A rotation as two shifts, XORed. -/
theorem shl_xor_shr (x : BitVec 32) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x <<< k ^^^ x >>> (32 - k) = x.rotateLeft k := by
  rw [← shl_or_shr x hk hk']
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  by_cases h : m < k
  · simp [h]
  · rw [BitVec.getLsbD_of_ge x (32 - k + m) (by omega)]
    simp

/-! ## One line, and a quarter round, on each doubleword -/

theorem toNat_ofNat8 {n : Nat} (h : n < 256) : (BitVec.ofNat 8 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; omega

theorem vstep_ok {x y z : XReg} {n : Nat} (hn : 0 < n) (hn' : n < 32) (hx4 : x ≠ .xmm4)
    (hx5 : x ≠ .xmm5) (hz4 : z ≠ .xmm4) (s : State) :
    WP isa (.block (vstep x y z n)) s fun s' =>
      (∀ i, i < 4 → dword (s'.xmm x) i =
        dword (s.xmm x) i ^^^ (dword (s.xmm y) i + dword (s.xmm z) i).rotateLeft n) ∧
      (∀ r, r ≠ x → r ≠ .xmm4 → r ≠ .xmm5 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [vstep, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun r h0 h4 h5 => ?_, trivial, trivial, trivial, trivial⟩
  · have h5x : ¬ XReg.xmm5 = x := fun h => hx5 h.symm
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hx4, RegUpd.xmm_setXmm_of_ne _ _ hx5,
      RegUpd.xmm_setXmm_of_ne _ _ hz4, RegUpd.xmm_setXmm_of_ne _ _ h5x,
      RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm5 = .xmm4 by decide),
      RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm4 = .xmm5 by decide), eval_movdqa]
    have e₁ : (BitVec.ofNat 8 n).toNat = n := toNat_ofNat8 (by omega)
    have e₂ : (BitVec.ofNat 8 (32 - n)).toNat = 32 - n := toNat_ofNat8 (by omega)
    rw [dword_pxor, dword_pxor, dword_pslld _ (BitVec.ofNat 8 n) (by rw [e₁]; omega) hi,
      dword_psrld _ (BitVec.ofNat 8 (32 - n)) (by rw [e₂]; omega) hi, dword_paddd _ _ hi, e₁, e₂,
      BitVec.xor_assoc, shl_xor_shr _ hn hn']
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h0, RegUpd.xmm_setXmm_of_ne _ _ h4,
      RegUpd.xmm_setXmm_of_ne _ _ h5]

/-- A quarter round of Salsa20 (RFC 7914 §3) on `a, b, c, d`. -/
def qr (a b c d : Word) : Word × Word × Word × Word :=
  let b := b ^^^ (a + d).rotateLeft 7
  let c := c ^^^ (b + a).rotateLeft 9
  let d := d ^^^ (c + b).rotateLeft 13
  let a := a ^^^ (d + c).rotateLeft 18
  (a, b, c, d)

theorem vhalf_ok {b c d : XReg} (hb4 : b ≠ .xmm4) (hb5 : b ≠ .xmm5) (hc4 : c ≠ .xmm4)
    (hc5 : c ≠ .xmm5) (hd4 : d ≠ .xmm4) (hd5 : d ≠ .xmm5) (hb0 : b ≠ .xmm0) (hc0 : c ≠ .xmm0)
    (hd0 : d ≠ .xmm0) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (s : State) :
    WP isa (.block (vhalf b c d)) s fun s' =>
      (∀ i, i < 4 →
        dword (s'.xmm .xmm0) i =
          (qr (dword (s.xmm .xmm0) i) (dword (s.xmm b) i) (dword (s.xmm c) i) (dword (s.xmm d) i)).1 ∧
        dword (s'.xmm b) i =
          (qr (dword (s.xmm .xmm0) i) (dword (s.xmm b) i) (dword (s.xmm c) i) (dword (s.xmm d) i)).2.1 ∧
        dword (s'.xmm c) i =
          (qr (dword (s.xmm .xmm0) i) (dword (s.xmm b) i) (dword (s.xmm c) i) (dword (s.xmm d) i)).2.2.1 ∧
        dword (s'.xmm d) i =
          (qr (dword (s.xmm .xmm0) i) (dword (s.xmm b) i) (dword (s.xmm c) i) (dword (s.xmm d) i)).2.2.2) ∧
      (∀ r, r ≠ .xmm0 → r ≠ b → r ≠ c → r ≠ d → r ≠ .xmm4 → r ≠ .xmm5 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [vhalf, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (vstep_ok (x := b) (y := .xmm0) (z := d) (n := 7) (by decide) (by decide) hb4 hb5 hd4 s)
    fun s₁ ⟨x₁, o₁, g₁, m₁, r₁, w₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vstep_ok (x := c) (y := b) (z := .xmm0) (n := 9) (by decide) (by decide) hc4 hc5
    (by decide) s₁) fun s₂ ⟨x₂, o₂, g₂, m₂, r₂, w₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vstep_ok (x := d) (y := c) (z := b) (n := 13) (by decide) (by decide) hd4 hd5 hb4 s₂)
    fun s₃ ⟨x₃, o₃, g₃, m₃, r₃, w₃⟩ => ?_
  refine WP.mono (vstep_ok (x := .xmm0) (y := d) (z := c) (n := 18) (by decide) (by decide) (by decide)
    (by decide) hc4 s₃) fun s₄ ⟨x₄, o₄, g₄, m₄, r₄, w₄⟩ => ?_
  have va1 : s₁.xmm .xmm0 = s.xmm .xmm0 := o₁ _ (Ne.symm hb0) (by decide) (by decide)
  have vc1 : s₁.xmm c = s.xmm c := o₁ _ (Ne.symm hbc) hc4 hc5
  have vd1 : s₁.xmm d = s.xmm d := o₁ _ (Ne.symm hbd) hd4 hd5
  have va2 : s₂.xmm .xmm0 = s₁.xmm .xmm0 := o₂ _ (Ne.symm hc0) (by decide) (by decide)
  have vb2 : s₂.xmm b = s₁.xmm b := o₂ _ hbc hb4 hb5
  have vd2 : s₂.xmm d = s₁.xmm d := o₂ _ (Ne.symm hcd) hd4 hd5
  have va3 : s₃.xmm .xmm0 = s₂.xmm .xmm0 := o₃ _ (Ne.symm hd0) (by decide) (by decide)
  have vb3 : s₃.xmm b = s₂.xmm b := o₃ _ hbd hb4 hb5
  have vc3 : s₃.xmm c = s₂.xmm c := o₃ _ hcd hc4 hc5
  have vb4 : s₄.xmm b = s₃.xmm b := o₄ _ hb0 hb4 hb5
  have vc4 : s₄.xmm c = s₃.xmm c := o₄ _ hc0 hc4 hc5
  have vd4 : s₄.xmm d = s₃.xmm d := o₄ _ hd0 hd4 hd5
  refine ⟨fun i hi => ?_, fun r h0 hb hc hd h4 h5 => ?_, by rw [g₄, g₃, g₂, g₁], by rw [m₄, m₃, m₂, m₁],
    by rw [r₄, r₃, r₂, r₁], by rw [w₄, w₃, w₂, w₁]⟩
  · have a4 := x₄ i hi
    have d3 := x₃ i hi
    have c2 := x₂ i hi
    have b1 := x₁ i hi
    simp only [qr, a4, d3, c2, b1, va1, vc1, vd1, va2, vb2, vd2, va3, vb3, vc3, vb4, vc4, vd4, and_self]
  · rw [o₄ r h0 h4 h5, o₃ r hd h4 h5, o₂ r hc h4 h5, o₁ r hb h4 h5]

/-! ## Arrangements of the words -/

/-- Word `4 k + q` (row `k`) in doubleword `q` of `xmm k`. -/
def rowIdx (k q : Nat) : Nat := 4 * k + q

/-- Column `q`, from its diagonal word: word `5 q + 4 k` (modulo 16). -/
def ci (k q : Nat) : Nat := (5 * q + 4 * k) % 16

/-- Row `q`, from its diagonal word, with `xmm3, xmm2, xmm1` holding the
words after it: word `4 q + (q + 4 - k) % 4`. -/
def ri (k q : Nat) : Nat := 4 * q + (q + (4 - k)) % 4

/-- The words `v` in `xmm0, …, xmm3`, word `f k q` in doubleword `q` of `xmm k`. -/
structure Arr (f : Nat → Nat → Nat) (v : Vector Word 16) (s : State) : Prop where
  r0 : ∀ q, q < 4 → dword (s.xmm .xmm0) q = v[f 0 q]!
  r1 : ∀ q, q < 4 → dword (s.xmm .xmm1) q = v[f 1 q]!
  r2 : ∀ q, q < 4 → dword (s.xmm .xmm2) q = v[f 2 q]!
  r3 : ∀ q, q < 4 → dword (s.xmm .xmm3) q = v[f 3 q]!

/-- The rows of `v` in `xmm0, xmm1, xmm2, xmm4`, as `fromDiag` leaves them. -/
structure Out (v : Vector Word 16) (s : State) : Prop where
  r0 : ∀ q, q < 4 → dword (s.xmm .xmm0) q = v[q]!
  r1 : ∀ q, q < 4 → dword (s.xmm .xmm1) q = v[4 + q]!
  r2 : ∀ q, q < 4 → dword (s.xmm .xmm2) q = v[8 + q]!
  r3 : ∀ q, q < 4 → dword (s.xmm .xmm4) q = v[12 + q]!

theorem arr_of {f : Nat → Nat → Nat} {v : Vector Word 16} {s : State}
    (h : ∀ i, i < 4 → dword (s.xmm .xmm0) i = v[f 0 i]! ∧ dword (s.xmm .xmm1) i = v[f 1 i]! ∧
      dword (s.xmm .xmm2) i = v[f 2 i]! ∧ dword (s.xmm .xmm3) i = v[f 3 i]!) : Arr f v s :=
  ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2.1, fun i hi => (h i hi).2.2.1,
    fun i hi => (h i hi).2.2.2⟩

/-! ## The column and row rounds of the specification -/

/-- The lines of the column round. -/
def colLines : List (Nat × Nat × Nat × Nat) := [
  (4, 0, 12, 7), (8, 4, 0, 9), (12, 8, 4, 13), (0, 12, 8, 18),
  (9, 5, 1, 7), (13, 9, 5, 9), (1, 13, 9, 13), (5, 1, 13, 18),
  (14, 10, 6, 7), (2, 14, 10, 9), (6, 2, 14, 13), (10, 6, 2, 18),
  (3, 15, 11, 7), (7, 3, 15, 9), (11, 7, 3, 13), (15, 11, 7, 18)]

/-- The lines of the row round. -/
def rowLines : List (Nat × Nat × Nat × Nat) := [
  (1, 0, 3, 7), (2, 1, 0, 9), (3, 2, 1, 13), (0, 3, 2, 18),
  (6, 5, 4, 7), (7, 6, 5, 9), (4, 7, 6, 13), (5, 4, 7, 18),
  (11, 10, 9, 7), (8, 11, 10, 9), (9, 8, 11, 13), (10, 9, 8, 18),
  (12, 15, 14, 7), (13, 12, 15, 9), (14, 13, 12, 13), (15, 14, 13, 18)]

def lineRun (l : List (Nat × Nat × Nat × Nat)) (v : Vector Word 16) : Vector Word 16 :=
  l.foldl (fun x (i, j, k, n) => stepN x i j k n) v

theorem doubleRound_eq (v : Vector Word 16) :
    Spec.Scrypt.doubleRound v = lineRun rowLines (lineRun colLines v) := rfl

theorem stepN_get! (x : Vector Word 16) {i j k : Nat} (n : Nat) (hi : i < 16) (hj : j < 16)
    (hk : k < 16) (m : Nat) (hm : m < 16) :
    (stepN x i j k n)[m]! = if i = m then x[i]! ^^^ (x[j]! + x[k]!).rotateLeft n else x[m]! := by
  rw [getElem!_pos _ m hm, getElem!_pos _ i hi, getElem!_pos _ j hj, getElem!_pos _ k hk,
    getElem!_pos _ m hm, stepN_get x n hi hj hk m hm]

theorem col_get (v : Vector Word 16) {q : Nat} (hq : q < 4) :
    (lineRun colLines v)[ci 0 q]! = (qr v[ci 0 q]! v[ci 1 q]! v[ci 2 q]! v[ci 3 q]!).1 ∧
    (lineRun colLines v)[ci 1 q]! = (qr v[ci 0 q]! v[ci 1 q]! v[ci 2 q]! v[ci 3 q]!).2.1 ∧
    (lineRun colLines v)[ci 2 q]! = (qr v[ci 0 q]! v[ci 1 q]! v[ci 2 q]! v[ci 3 q]!).2.2.1 ∧
    (lineRun colLines v)[ci 3 q]! = (qr v[ci 0 q]! v[ci 1 q]! v[ci 2 q]! v[ci 3 q]!).2.2.2 := by
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [lineRun, colLines, List.foldl_cons, List.foldl_nil, stepN_get!, ci, qr,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem row_get (v : Vector Word 16) {q : Nat} (hq : q < 4) :
    (lineRun rowLines v)[ri 0 q]! = (qr v[ri 0 q]! v[ri 3 q]! v[ri 2 q]! v[ri 1 q]!).1 ∧
    (lineRun rowLines v)[ri 3 q]! = (qr v[ri 0 q]! v[ri 3 q]! v[ri 2 q]! v[ri 1 q]!).2.1 ∧
    (lineRun rowLines v)[ri 2 q]! = (qr v[ri 0 q]! v[ri 3 q]! v[ri 2 q]! v[ri 1 q]!).2.2.1 ∧
    (lineRun rowLines v)[ri 1 q]! = (qr v[ri 0 q]! v[ri 3 q]! v[ri 2 q]! v[ri 1 q]!).2.2.2 := by
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [lineRun, rowLines, List.foldl_cons, List.foldl_nil, stepN_get!, ri, qr,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, and_self]

/-! ## Moving the words between the registers' doublewords -/

/-- Executes register-only shuffles, keeping each register's value as four
doublewords of the registers on entry. -/
local macro "shuf_tac" : tactic =>
  `(tactic| (apply WP.of_runBlock
             simp only [toRows, toCols, toDiag, fromDiag, transpose, shuf, xb, List.cons_append,
               List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
               RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
               RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
               eval_movdqa, shuf39, shuf4e, shuf93, punpckldq_eq, punpckhdq_eq, punpcklqdq_eq,
               punpckhqdq_eq, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
               Option.some.injEq, exists_eq_left']))

/-- Evaluates one doubleword of the result of `shuf_tac`. -/
local macro "lane_tac" : tactic =>
  `(tactic| simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
    eval_movdqa, shuf39, shuf4e, shuf93, punpckldq_eq, punpckhdq_eq, punpcklqdq_eq, punpckhqdq_eq,
    dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3])

theorem toRows_ok {v : Vector Word 16} {s : State} (h : Arr ci v s) :
    WP isa (.block toRows) s fun s' => Arr ri v s' ∧ (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 →
      s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  shuf_tac
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩, fun r h1 h2 h3 => ?_,
    trivial, trivial, trivial, trivial⟩
  rotate_right
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3]
  all_goals rcases cases4 hq with rfl | rfl | rfl | rfl
  all_goals lane_tac
  all_goals first | exact h.r0 _ (by decide) | exact h.r1 _ (by decide) | exact h.r2 _ (by decide) | exact h.r3 _ (by decide)

theorem toCols_ok {v : Vector Word 16} {s : State} (h : Arr ri v s) :
    WP isa (.block toCols) s fun s' => Arr ci v s' ∧ (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 →
      s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  shuf_tac
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩, fun r h1 h2 h3 => ?_,
    trivial, trivial, trivial, trivial⟩
  rotate_right
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3]
  all_goals rcases cases4 hq with rfl | rfl | rfl | rfl
  all_goals lane_tac
  all_goals first | exact h.r0 _ (by decide) | exact h.r1 _ (by decide) | exact h.r2 _ (by decide) | exact h.r3 _ (by decide)

theorem toDiag_ok {v : Vector Word 16} {s : State} (h : Arr rowIdx v s) :
    WP isa (.block toDiag) s fun s' => Arr ci v s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  shuf_tac
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩, trivial, trivial, trivial,
    trivial⟩ <;>
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> lane_tac <;>
  first | exact h.r0 _ (by decide) | exact h.r1 _ (by decide) | exact h.r2 _ (by decide) | exact h.r3 _ (by decide)

theorem fromDiag_ok {v : Vector Word 16} {s : State} (h : Arr ci v s) :
    WP isa (.block fromDiag) s fun s' => Out v s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  shuf_tac
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩, trivial, trivial, trivial,
    trivial⟩ <;>
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> lane_tac <;>
  first | exact h.r0 _ (by decide) | exact h.r1 _ (by decide) | exact h.r2 _ (by decide) | exact h.r3 _ (by decide)

/-! ## The double rounds -/

/-- What the code keeps during the rounds. -/
structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Same.trans {s₁ s₂ s₃ : State} (h₁ : Same s₁ s₂) (h₂ : Same s₂ s₃) : Same s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem colHalf_ok {v : Vector Word 16} {s : State} (h : Arr ci v s) :
    WP isa (.block (vhalf .xmm1 .xmm2 .xmm3)) s fun s' => Arr ci (lineRun colLines v) s' ∧ Same s s' :=
  WP.mono (vhalf_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) s) fun s' ⟨q, _, g, m, r, w⟩ =>
    ⟨arr_of fun i hi => by
      have h0 : dword (s.xmm .xmm0) i = v[ci 0 i]! := h.r0 i hi
      have h1 : dword (s.xmm .xmm1) i = v[ci 1 i]! := h.r1 i hi
      have h2 : dword (s.xmm .xmm2) i = v[ci 2 i]! := h.r2 i hi
      have h3 : dword (s.xmm .xmm3) i = v[ci 3 i]! := h.r3 i hi
      have e := q i hi
      rw [h0, h1, h2, h3] at e
      obtain ⟨c0, c1, c2, c3⟩ := col_get v hi
      exact ⟨e.1.trans c0.symm, e.2.1.trans c1.symm, e.2.2.1.trans c2.symm, e.2.2.2.trans c3.symm⟩, ⟨g, m, r, w⟩⟩

theorem rowHalf_ok {v : Vector Word 16} {s : State} (h : Arr ri v s) :
    WP isa (.block (vhalf .xmm3 .xmm2 .xmm1)) s fun s' => Arr ri (lineRun rowLines v) s' ∧ Same s s' :=
  WP.mono (vhalf_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) s) fun s' ⟨q, _, g, m, r, w⟩ =>
    ⟨arr_of fun i hi => by
      have h0 : dword (s.xmm .xmm0) i = v[ri 0 i]! := h.r0 i hi
      have h1 : dword (s.xmm .xmm1) i = v[ri 1 i]! := h.r1 i hi
      have h2 : dword (s.xmm .xmm2) i = v[ri 2 i]! := h.r2 i hi
      have h3 : dword (s.xmm .xmm3) i = v[ri 3 i]! := h.r3 i hi
      have e := q i hi
      rw [h0, h1, h2, h3] at e
      obtain ⟨c0, c3, c2, c1⟩ := row_get v hi
      exact ⟨e.1.trans c0.symm, e.2.2.2.trans c1.symm, e.2.2.1.trans c2.symm, e.2.1.trans c3.symm⟩, ⟨g, m, r, w⟩⟩

theorem doubleRound_ok {v : Vector Word 16} {s : State} (h : Arr ci v s) :
    WP isa doubleRound s fun s' => Arr ci (Spec.Scrypt.doubleRound v) s' ∧ Same s s' := by
  rw [doubleRound, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (colHalf_ok h) fun s₁ ⟨h₁, e₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (toRows_ok h₁) fun s₂ ⟨h₂, _, g₂, m₂, r₂, w₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowHalf_ok h₂) fun s₃ ⟨h₃, e₃⟩ => ?_
  refine WP.mono (toCols_ok h₃) fun s₄ ⟨h₄, _, g₄, m₄, r₄, w₄⟩ => ?_
  rw [doubleRound_eq]
  exact ⟨h₄, (e₁.trans ⟨g₂, m₂, r₂, w₂⟩).trans (e₃.trans ⟨g₄, m₄, r₄, w₄⟩)⟩

theorem rounds_ok {v : Vector Word 16} {s : State} (h : Arr ci v s) :
    ∀ n, WP isa (rounds n) s fun s' => Arr ci (Nat.repeat Spec.Scrypt.doubleRound n v) s' ∧ Same s s'
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ ⟨h', e'⟩ =>
      WP.mono (doubleRound_ok h') fun _ ⟨h'', e''⟩ => ⟨h'', e'.trans e''⟩)

end VG.Proof.Scrypt.X86
