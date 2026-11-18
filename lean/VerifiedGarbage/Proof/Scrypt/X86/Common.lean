module

public import VerifiedGarbage.Impl.Scrypt.X86.BlockMix
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
public import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Scrypt.Memory
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Impl.Scrypt.X86.Salsa
meta import VerifiedGarbage.Impl.Scrypt.X86.Salsa
import all Init.Data.Nat.Power2.Basic
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Sha256.X86.Compress
public import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Compress
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.X86.Reduce

/-! ### `Scrypt.X86.Salsa`, which this module and modules that import it used -/

section

/-! ### `Scrypt.X86.SalsaRounds`, which only this module used -/

section

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

@[expose] public section

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
  · rw [BitVec.getLsbD_of_ge x (32 - k + m) (by omega_using [h])]
    simp

/-! ## One line, and a quarter round, on each doubleword -/

theorem toNat_ofNat8 {n : Nat} (h : n < 256) : (BitVec.ofNat 8 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; omega_using [h]

theorem vstep_ok {x y z : XReg} {n : Nat} (hn : 0 < n) (hn' : n < 32) (hx4 : x ≠ .xmm4)
    (hx5 : x ≠ .xmm5) (hz4 : z ≠ .xmm4) (s : State) :
    WP isa (.block (vstep x y z n)) s fun s' =>
      (∀ i, i < 4 → dword (s'.xmm x) i =
        dword (s.xmm x) i ^^^ (dword (s.xmm y) i + dword (s.xmm z) i).rotateLeft n) ∧
      (∀ r, r ≠ x → r ≠ .xmm4 → r ≠ .xmm5 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [vstep, xb, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec,
    RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun r h0 h4 h5 => ?_, trivial, trivial, trivial, trivial⟩
  · have h5x : ¬ XReg.xmm5 = x := fun h => hx5 h.symm
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hx4, RegUpd.xmm_setXmm_of_ne _ _ hx5,
      RegUpd.xmm_setXmm_of_ne _ _ hz4, RegUpd.xmm_setXmm_of_ne _ _ h5x,
      RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm5 = .xmm4 by decide),
      RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm4 = .xmm5 by decide), eval_movdqa]
    have e₁ : (BitVec.ofNat 8 n).toNat = n := toNat_ofNat8 (by omega_using [hn'])
    have e₂ : (BitVec.ofNat 8 (32 - n)).toNat = 32 - n := toNat_ofNat8 (by omega_using [])
    rw [dword_pxor, dword_pxor, dword_pslld _ (BitVec.ofNat 8 n) (by rw [e₁]; omega_using [hn']) hi,
      dword_psrld _ (BitVec.ofNat 8 (32 - n)) (by rw [e₂]; omega_using [hn]) hi, dword_paddd _ _ hi, e₁, e₂,
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

theorem toRows_ok {v : Vector Word 16} {s : State} (h : Arr ci v s) :
    WP isa (.block toRows) s fun s' => Arr ri v s' ∧ (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 →
      s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [toRows, shuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec,
    RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, shuf39, shuf4e, shuf93,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩, fun r h1 h2 h3 => ?_,
    trivial, trivial, trivial, trivial⟩
  rotate_right
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3]
  all_goals rcases cases4 hq with rfl | rfl | rfl | rfl
  all_goals simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq,
    not_false_eq_true, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  exacts [h.r0 _ (by decide), h.r0 _ (by decide), h.r0 _ (by decide), h.r0 _ (by decide),
    h.r1 _ (by decide), h.r1 _ (by decide), h.r1 _ (by decide), h.r1 _ (by decide),
    h.r2 _ (by decide), h.r2 _ (by decide), h.r2 _ (by decide), h.r2 _ (by decide),
    h.r3 _ (by decide), h.r3 _ (by decide), h.r3 _ (by decide), h.r3 _ (by decide)]

theorem toCols_ok {v : Vector Word 16} {s : State} (h : Arr ri v s) :
    WP isa (.block toCols) s fun s' => Arr ci v s' ∧ (∀ r, r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 →
      s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [toCols, shuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec,
    RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, shuf39, shuf4e, shuf93,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩, fun r h1 h2 h3 => ?_,
    trivial, trivial, trivial, trivial⟩
  rotate_right
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3]
  all_goals rcases cases4 hq with rfl | rfl | rfl | rfl
  all_goals simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq,
    not_false_eq_true, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  exacts [h.r0 _ (by decide), h.r0 _ (by decide), h.r0 _ (by decide), h.r0 _ (by decide),
    h.r1 _ (by decide), h.r1 _ (by decide), h.r1 _ (by decide), h.r1 _ (by decide),
    h.r2 _ (by decide), h.r2 _ (by decide), h.r2 _ (by decide), h.r2 _ (by decide),
    h.r3 _ (by decide), h.r3 _ (by decide), h.r3 _ (by decide), h.r3 _ (by decide)]

theorem toDiag_ok {v : Vector Word 16} {s : State} (h : Arr rowIdx v s) :
    WP isa (.block toDiag) s fun s' => Arr ci v s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [toDiag, transpose, shuf, xb, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, reduceExec, XOp.exec, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne,
    reduceCtorEq, not_false_eq_true, eval_movdqa, shuf39, shuf4e, shuf93, punpckldq_eq,
    punpckhdq_eq, punpcklqdq_eq, punpckhqdq_eq, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩, trivial, trivial, trivial,
    trivial⟩ <;>
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
      dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  exacts [h.r0 _ (by decide), h.r1 _ (by decide), h.r2 _ (by decide), h.r3 _ (by decide),
    h.r1 _ (by decide), h.r2 _ (by decide), h.r3 _ (by decide), h.r0 _ (by decide),
    h.r2 _ (by decide), h.r3 _ (by decide), h.r0 _ (by decide), h.r1 _ (by decide),
    h.r3 _ (by decide), h.r0 _ (by decide), h.r1 _ (by decide), h.r2 _ (by decide)]

theorem fromDiag_ok {v : Vector Word 16} {s : State} (h : Arr ci v s) :
    WP isa (.block fromDiag) s fun s' => Out v s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [fromDiag, transpose, shuf, xb, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, reduceExec, XOp.exec, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne,
    reduceCtorEq, not_false_eq_true, eval_movdqa, shuf39, shuf4e, shuf93, punpckldq_eq,
    punpckhdq_eq, punpcklqdq_eq, punpckhqdq_eq, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩, trivial, trivial, trivial,
    trivial⟩ <;>
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
      dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  exacts [h.r0 _ (by decide), h.r3 _ (by decide), h.r2 _ (by decide), h.r1 _ (by decide),
    h.r1 _ (by decide), h.r0 _ (by decide), h.r3 _ (by decide), h.r2 _ (by decide),
    h.r2 _ (by decide), h.r1 _ (by decide), h.r0 _ (by decide), h.r3 _ (by decide),
    h.r3 _ (by decide), h.r2 _ (by decide), h.r1 _ (by decide), h.r0 _ (by decide)]

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

end

end

/-!
# The Salsa20/8 Core on x86 (32-bit)

The contracts the proofs of this directory are written against, and the proof of
`vg_salsa20_8`: the rows of `b` are loaded (`load_ok`), put into the diagonal
layout and through the double rounds (`Proof/Scrypt/X86/Common.lean`), put
back, and added to the input, which `b` keeps until then (`addRows_ok`). The
proof is written against a contract under which the code only reads its
arguments (which it does), and moved to the shared contract with
`Verified.narrowTo`.
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.X86 in
/-- X86 (32-bit) contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut
[u32; 16])`, whose arguments are on the stack (cdecl): replaces the 64 bytes at
`b` by their Salsa20/8 Core.

The code may read the arguments (8 bytes above the return address), and read
and write `b` and `scratch` (64 bytes each, the contents of `scratch` on
exit unspecified), which may not overlap each other, the arguments or the
return address, or wrap around the end of the (32-bit) address space. `esp`
and the pointers are public; the data is secret. -/
def salsaX86 : Contract X86.isa where
  pre s :=
    let b : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let scratch : Region := ⟨(arg s 1).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [b, scratch] ∧
    b.Disjoint scratch ∧ args.Disjoint b ∧ args.Disjoint scratch ∧ ret.Disjoint b ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem ((arg s 0).setWidth 64) 64 = salsa (bytesAt s.mem ((arg s 0).setWidth 64) 64)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open VG.X86 in
/-- X86 (32-bit) contract for `vg_scrypt_blockmix(b: *const [u8; 128], r: usize,
y: *mut [u8; 128], ry: usize, scratch: *mut [u32; 32])`, whose arguments are on
the stack (cdecl): if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes
at `b` to `y`.

The code may read the arguments (20 bytes above the return address) and
`b`, and read and write `y` and `scratch` (128 bytes). The written regions
may not overlap each other, `b`, the arguments or the return address; none
of the buffers may overlap the 12 bytes of stack below the return address
(where the code calls `vg_salsa20_8`); nothing may wrap around the end of
the (32-bit) address space. `esp` and the arguments are public; the data is
secret. -/
def blockMixX86 : Contract X86.isa where
  pre s :=
    let r := (arg s 1).toNat
    let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
    let y : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 128⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [b, args] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧ args.Disjoint y ∧ args.Disjoint scratch ∧
    ret.Disjoint y ∧ ret.Disjoint scratch ∧ stack.Disjoint b ∧ stack.Disjoint y ∧
    stack.Disjoint scratch ∧
    (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 128 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    arg s 3 = arg s 1 ∧ 0 < r
  post s s' := let r := (arg s 1).toNat
    bytesAt s'.mem ((arg s 2).setWidth 64) (128 * r) =
      blockMix r (bytesAt s.mem ((arg s 0).setWidth 64) (128 * r))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open VG.X86 in
/-- X86 (32-bit) contract for `vg_scrypt_romix(b: *mut [u8; 128], r: usize, v:
*mut [u8; 128], vlen: usize, scratch: *mut [u8; 128], slen: usize)`, whose
arguments are on the stack (cdecl): if `r > 0`, `vlen = N r` for a power of two
`N`, and `slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix.

The code may read the arguments (24 bytes above the return address), and
read and write `b`, `v` and `scratch`, which may not overlap each other, the
arguments, the return address or the 36 bytes of stack below it (where the
code calls `vg_scrypt_blockmix`), or wrap around the end of the (32-bit)
address space. `esp`, the arguments and the indices `j` of step 3 are
public. -/
def roMixX86 : Contract X86.isa where
  pre s :=
    let r := (arg s 1).toNat
    let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
    let v : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat * 128⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 36, 36⟩
    s.rd = [args] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    args.Disjoint b ∧ args.Disjoint v ∧ args.Disjoint scratch ∧
    ret.Disjoint b ∧ ret.Disjoint v ∧ ret.Disjoint scratch ∧
    stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + (arg s 5).toNat * 128 ≤ 2 ^ 32 ∧ 36 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    0 < r ∧ (arg s 3).toNat % r = 0 ∧ ((arg s 3).toNat / r).isPowerOfTwo ∧ (arg s 5).toNat = r + 2
  post s s' := let r := (arg s 1).toNat
    bytesAt s'.mem ((arg s 0).setWidth 64) (128 * r) =
      roMix r ((arg s 3).toNat / r) (bytesAt s.mem ((arg s 0).setWidth 64) (128 * r))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    roMixIndices (arg s₁ 1).toNat ((arg s₁ 3).toNat / (arg s₁ 1).toNat)
        (bytesAt s₁.mem ((arg s₁ 0).setWidth 64) (128 * (arg s₁ 1).toNat)) =
      roMixIndices (arg s₂ 1).toNat ((arg s₂ 3).toNat / (arg s₂ 1).toNat)
        (bytesAt s₂.mem ((arg s₂ 0).setWidth 64) (128 * (arg s₂ 1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store addr_toNat)
open VG.Proof.Scrypt.Memory (contains_off)

/-! ## Instructions with a memory operand -/

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bP : BitVec 32 := arg s₀ 0
/-- `scratch`. -/
abbrev scP : BitVec 32 := arg s₀ 1
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev sA : Addr := (scP s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, 64⟩
abbrev sR : Region := ⟨sA s₀, 64⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [bR s₀, sR s₀]
  disj : (bR s₀).Disjoint (sR s₀)
  a_b : (argR s₀).Disjoint (bR s₀)
  a_s : (argR s₀).Disjoint (sR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_s : (retR s₀).Disjoint (sR s₀)
  b_fit : (bP s₀).toNat + 64 ≤ 2 ^ 32
  s_fit : (scP s₀).toNat + 64 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem V_get! (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k]! = s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  rw [getElem!_pos (V s₀) k hk, V_get _ hk]

/-- `eax` is `b`, the other general-purpose registers are those on entry,
and so are the permissions. -/
structure Keep (s₀ s : State) : Prop where
  eax : s.gpr .eax = bP s₀
  gpr : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Keep.same {s₀ s s' : State} (h : Keep s₀ s) (e : Same s s') : Keep s₀ s' :=
  ⟨by rw [e.gpr, h.eax], fun r hr => by rw [e.gpr, h.gpr r hr], e.rd.trans h.rd, e.wr.trans h.wr⟩

/-! ## 16-byte loads and stores -/

/-- The general-purpose registers and the permissions are unchanged. -/
structure Regs (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.regs {s₀ s s' : State} (h : Keep s₀ s) (e : Regs s s') : Keep s₀ s' :=
  ⟨by rw [e.gpr, h.eax], fun r hr => by rw [e.gpr, h.gpr r hr], e.rd.trans h.rd, e.wr.trans h.wr⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movdqu d, [m]` -/
theorem wp_ldq {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', Regs s s' → s'.mem = s.mem → s'.xmm d = s.mem.readW a 128 →
      (∀ r, r ≠ d → s'.xmm r = s.xmm r) → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquLoad d m :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := s.setXmm d (s.mem.readW a 128))
    (by simp only [exec, State.load128, ha, hin, ite_true, Option.map_some])
    (k _ ⟨rfl, rfl, rfl⟩ rfl (RegUpd.xmm_setXmm_self _ _ _) fun _ h => RegUpd.xmm_setXmm_of_ne _ _ h)

/-- `movdqu [m], r` -/
theorem wp_stq {r : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', Regs s s' → s'.mem = s.mem.writeW a (s.xmm r) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquStore m r :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := { s with mem := s.mem.writeW a (s.xmm r) })
    (by simp only [exec, State.store128, ha, hout, ite_true]) (k _ ⟨rfl, rfl, rfl⟩ rfl rfl)

/-- `op d, r` on XMM registers. -/
theorem wp_xbin {op : XBinOp} {d r : XReg}
    (k : ∀ s', Regs s s' → s'.mem = s.mem → s'.xmm d = op.eval (s.xmm d) (s.xmm r) →
      (∀ q, q ≠ d → s'.xmm q = s.xmm q) → WP isa (.block is) s' Q) :
    WP isa (.block (xb op d r :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := s.setXmm d (op.eval (s.xmm d) (s.xmm r))) rfl
    (k _ ⟨rfl, rfl, rfl⟩ rfl (RegUpd.xmm_setXmm_self _ _ _) fun _ h => RegUpd.xmm_setXmm_of_ne _ _ h)

end

/-! ## Loading the rows -/

theorem arg_in {s₀ : State} (hp : Pre s₀) {d : Nat} (h1 : 4 ≤ d) (h2 : d + 4 ≤ 12) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  show (addr (s₀.gpr .esp) d - addr (s₀.gpr .esp) 4).toNat + 4 ≤ 8
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith),
    show (s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 d - ((s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by rw [show d = (d - 4) + 4 by omega_arith, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- Where `eax`-relative operands point, and that the code may access them. -/
theorem ea_b {s₀ s : State} (hp : Pre s₀) (h : Keep s₀ s) {d : Nat} (hd : d ≤ 48) :
    s.ea (at_ .eax d) = bA s₀ + BitVec.ofNat 64 d := by
  rw [ea_at, h.eax]; exact addr_eq (by have := hp.b_fit; omega_arith)

theorem out_b16 {s₀ s : State} (hp : Pre s₀) (h : Keep s₀ s) {d : Nat} (hd : d + 16 ≤ 64) :
    InRegions s.wr (bA s₀ + BitVec.ofNat 64 d) 16 := by
  rw [h.wr]; exact ⟨bR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

theorem in_b16 {s₀ s : State} (hp : Pre s₀) (h : Keep s₀ s) {d : Nat} (hd : d + 16 ≤ 64) :
    InRegions (s.rd ++ s.wr) (bA s₀ + BitVec.ofNat 64 d) 16 :=
  let ⟨r, hr, hc⟩ := out_b16 hp h hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- Doubleword `q` of the row at `b + 16 k` is word `4 k + q`. -/
theorem row_word (s₀ : State) {k q : Nat} (hk : k < 4) (hq : q < 4) :
    dword (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (16 * k)) 128) q = (V s₀)[4 * k + q]! := by
  rw [dword_readW _ _ hq, Offset.add_add, V_get! _ (by omega_arith)]
  exact congrArg (fun o => s₀.mem.readW (bA s₀ + BitVec.ofNat 64 o) 32) (by omega_arith)

/-- The pointer and the rows, loaded. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, Keep s₀ s → s.mem = s₀.mem → Arr rowIdx (V s₀) s → WP isa (.block rest) s Q) :
    WP isa (.block (load ++ rest)) s₀ Q := by
  simp only [load, List.cons_append, List.nil_append]
  refine wp_movm (a := addr (s₀.gpr .esp) 4) rfl (arg_in hp (by omega_arith) (by omega_arith)) fun s₁ u₁ => ?_
  obtain k₁ : Keep s₀ s₁ := ⟨by rw [u₁.gpr]; rfl, fun r h => u₁.other r h, u₁.rd, u₁.wr⟩
  refine wp_ldq (ea_b hp k₁ (d := 0) (by omega_arith)) (in_b16 hp k₁ (by omega_arith)) fun s₂ R₂ m₂ x₂ o₂ => ?_
  obtain k₂ := k₁.regs R₂
  refine wp_ldq (ea_b hp k₂ (d := 16) (by omega_arith)) (in_b16 hp k₂ (by omega_arith)) fun s₃ R₃ m₃ x₃ o₃ => ?_
  obtain k₃ := k₂.regs R₃
  refine wp_ldq (ea_b hp k₃ (d := 32) (by omega_arith)) (in_b16 hp k₃ (by omega_arith)) fun s₄ R₄ m₄ x₄ o₄ => ?_
  obtain k₄ := k₃.regs R₄
  refine wp_ldq (ea_b hp k₄ (d := 48) (by omega_arith)) (in_b16 hp k₄ (by omega_arith)) fun s₅ R₅ m₅ x₅ o₅ => ?_
  obtain k₅ := k₄.regs R₅
  have e₁ : s₁.mem = s₀.mem := u₁.mem
  refine k s₅ k₅ (by rw [m₅, m₄, m₃, m₂, e₁]) ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [o₅ .xmm0 (by decide), o₄ .xmm0 (by decide), o₃ .xmm0 (by decide), x₂, e₁]
    exact row_word s₀ (k := 0) (by omega_arith) hq
  · rw [o₅ .xmm1 (by decide), o₄ .xmm1 (by decide), x₃, m₂, e₁]
    exact row_word s₀ (k := 1) (by omega_arith) hq
  · rw [o₅ .xmm2 (by decide), x₄, m₃, m₂, e₁]
    exact row_word s₀ (k := 2) (by omega_arith) hq
  · rw [x₅, m₄, m₃, m₂, e₁]
    exact row_word s₀ (k := 3) (by omega_arith) hq

/-! ## Adding the input -/

/-- Word `j` after four 16-byte stores at `p`, `p + 16`, `p + 32` and `p + 48`. -/
theorem rows_read (m : Mem) (p : Addr) (X₀ X₁ X₂ X₃ : BitVec 128) {j : Nat} (hj : j < 16) :
    ((((m.writeW (p + BitVec.ofNat 64 0) X₀).writeW (p + BitVec.ofNat 64 16) X₁).writeW
      (p + BitVec.ofNat 64 32) X₂).writeW (p + BitVec.ofNat 64 48) X₃).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      dword (if j < 4 then X₀ else if j < 8 then X₁ else if j < 12 then X₂ else X₃) (j % 4) := by
  obtain hq : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases (show j < 4 ∨ (4 ≤ j ∧ j < 8) ∨ (8 ≤ j ∧ j < 12) ∨ 12 ≤ j by omega_arith) with h | h | h | h
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      ← Offset.add_add_eq p (show 0 + 4 * (j % 4) = 4 * j by omega_arith), readW_writeW128 _ _ _ hq,
      ite_eq_left h]
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      ← Offset.add_add_eq p (show 16 + 4 * (j % 4) = 4 * j by omega_arith), readW_writeW128 _ _ _ hq,
      ite_eq_right (by omega_arith), ite_eq_left h.2]
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      ← Offset.add_add_eq p (show 32 + 4 * (j % 4) = 4 * j by omega_arith), readW_writeW128 _ _ _ hq,
      ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left h.2]
  · rw [← Offset.add_add_eq p (show 48 + 4 * (j % 4) = 4 * j by omega_arith), readW_writeW128 _ _ _ hq,
      ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

/-- Doubleword `q` of the sum of row `k` of the result and of the input. -/
theorem sum_word {s₀ s : State} {R : Vector Word 16} {x : XReg} {k q : Nat} (hk : k < 4) (hq : q < 4)
    (hx : dword (s.xmm x) q = R[4 * k + q]!) :
    dword (XBinOp.eval .paddd (s.xmm x) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (16 * k)) 128)) q =
      R[4 * k + q]! + (V s₀)[4 * k + q]! := by
  rw [dword_paddd _ _ hq, hx, row_word s₀ hk hq]

theorem addRows_ok {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {s : State} (hk : Keep s₀ s)
    (hm : s.mem = s₀.mem) (h : Out R s) :
    WP isa (.block addRows) s fun s' => Keep s₀ s' ∧
      ∀ j < 16, s'.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j]! + (V s₀)[j]! := by
  unfold addRows
  refine wp_ldq (ea_b hp hk (d := 0) (by omega_arith)) (in_b16 hp hk (by omega_arith)) fun s₁ R₁ m₁ x₁ o₁ => ?_
  obtain k₁ := hk.regs R₁
  refine wp_ldq (ea_b hp k₁ (d := 16) (by omega_arith)) (in_b16 hp k₁ (by omega_arith)) fun s₂ R₂ m₂ x₂ o₂ => ?_
  obtain k₂ := k₁.regs R₂
  refine wp_ldq (ea_b hp k₂ (d := 32) (by omega_arith)) (in_b16 hp k₂ (by omega_arith)) fun s₃ R₃ m₃ x₃ o₃ => ?_
  obtain k₃ := k₂.regs R₃
  refine wp_ldq (ea_b hp k₃ (d := 48) (by omega_arith)) (in_b16 hp k₃ (by omega_arith)) fun s₄ R₄ m₄ x₄ o₄ => ?_
  obtain k₄ := k₃.regs R₄
  refine wp_xbin fun s₅ R₅ m₅ x₅ o₅ => wp_xbin fun s₆ R₆ m₆ x₆ o₆ => wp_xbin fun s₇ R₇ m₇ x₇ o₇ =>
    wp_xbin fun s₈ R₈ m₈ x₈ o₈ => ?_
  obtain k₈ := (((k₄.regs R₅).regs R₆).regs R₇).regs R₈
  refine wp_stq (ea_b hp k₈ (d := 0) (by omega_arith)) (out_b16 hp k₈ (by omega_arith)) fun s₉ R₉ m₉ x₉ => ?_
  obtain k₉ := k₈.regs R₉
  refine wp_stq (ea_b hp k₉ (d := 16) (by omega_arith)) (out_b16 hp k₉ (by omega_arith)) fun s₁₀ R₁₀ m₁₀ x₁₀ => ?_
  obtain k₁₀ := k₉.regs R₁₀
  refine wp_stq (ea_b hp k₁₀ (d := 32) (by omega_arith)) (out_b16 hp k₁₀ (by omega_arith)) fun s₁₁ R₁₁ m₁₁ x₁₁ => ?_
  obtain k₁₁ := k₁₀.regs R₁₁
  refine wp_stq (ea_b hp k₁₁ (d := 48) (by omega_arith)) (out_b16 hp k₁₁ (by omega_arith)) fun s₁₂ R₁₂ m₁₂ x₁₂ => ?_
  refine WP.block_nil ⟨k₁₁.regs R₁₂, fun j hj => ?_⟩
  -- The rows stored, as sums of the loaded rows and those of the result.
  obtain l₀ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  obtain y₀ : s₈.xmm .xmm0 = XBinOp.eval .paddd (s.xmm .xmm0) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 0) 128) := by
    rw [o₈ .xmm0 (by decide), o₇ .xmm0 (by decide), o₆ .xmm0 (by decide), x₅, o₄ .xmm0 (by
      decide), o₃ .xmm0 (by decide), o₂ .xmm0 (by decide), o₁ .xmm0 (by decide), o₄ .xmm3 (by
      decide), o₃ .xmm3 (by decide), o₂ .xmm3 (by decide), x₁, hm]
  obtain y₁ : s₉.xmm .xmm1 = XBinOp.eval .paddd (s.xmm .xmm1) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 16) 128) := by
    rw [x₉, o₈ .xmm1 (by decide), o₇ .xmm1 (by decide), x₆, o₅ .xmm1 (by decide), o₄ .xmm1 (by
      decide), o₃ .xmm1 (by decide), o₂ .xmm1 (by decide), o₁ .xmm1 (by decide), o₅ .xmm5 (by
      decide), o₄ .xmm5 (by decide), o₃ .xmm5 (by decide), x₂, m₁, hm]
  obtain y₂ : s₁₀.xmm .xmm2 = XBinOp.eval .paddd (s.xmm .xmm2) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 32) 128) := by
    rw [x₁₀, x₉, o₈ .xmm2 (by decide), x₇, o₆ .xmm2 (by decide), o₅ .xmm2 (by decide), o₄ .xmm2
      (by decide), o₃ .xmm2 (by decide), o₂ .xmm2 (by decide), o₁ .xmm2 (by decide), o₆ .xmm6
      (by decide), o₅ .xmm6 (by decide), o₄ .xmm6 (by decide), x₃, m₂, m₁, hm]
  obtain y₃ : s₁₁.xmm .xmm4 = XBinOp.eval .paddd (s.xmm .xmm4) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 48) 128) := by
    rw [x₁₁, x₁₀, x₉, x₈, o₇ .xmm4 (by decide), o₆ .xmm4 (by decide), o₅ .xmm4 (by decide), o₄
      .xmm4 (by decide), o₃ .xmm4 (by decide), o₂ .xmm4 (by decide), o₁ .xmm4 (by decide), o₇
      .xmm7 (by decide), o₆ .xmm7 (by decide), o₅ .xmm7 (by decide), x₄, m₃, m₂, m₁, hm]
  rw [m₁₂, m₁₁, m₁₀, m₉, m₈, m₇, m₆, m₅, l₀, y₃, y₂, y₁, y₀, rows_read _ _ _ _ _ _ hj]
  obtain hq : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases (show j < 4 ∨ (4 ≤ j ∧ j < 8) ∨ (8 ≤ j ∧ j < 12) ∨ 12 ≤ j by omega_arith) with c | c | c | c
  · rw [ite_eq_left c]
    refine (sum_word (k := 0) (by decide) hq ((h.r0 _ hq).trans
      (congrArg (fun i => R[i]!) (by omega_arith)))).trans (congrArg (fun i => R[i]! + (V s₀)[i]!) (by omega_arith))
  · rw [ite_eq_right (by omega_arith), ite_eq_left c.2]
    refine (sum_word (k := 1) (by decide) hq ((h.r1 _ hq).trans
      (congrArg (fun i => R[i]!) (by omega_arith)))).trans (congrArg (fun i => R[i]! + (V s₀)[i]!) (by omega_arith))
  · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left c.2]
    refine (sum_word (k := 2) (by decide) hq ((h.r2 _ hq).trans
      (congrArg (fun i => R[i]!) (by omega_arith)))).trans (congrArg (fun i => R[i]! + (V s₀)[i]!) (by omega_arith))
  · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
    refine (sum_word (k := 3) (by decide) hq ((h.r3 _ hq).trans
      (congrArg (fun i => R[i]!) (by omega_arith)))).trans (congrArg (fun i => R[i]! + (V s₀)[i]!) (by omega_arith))

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega_arith)]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j < 16, m.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j]! + (V s₀)[j]!) :
    Spec.Scrypt.bytesAt m (bA s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, h j hj, getElem!_pos _ j hj, getElem!_pos _ j hj]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' => Keep s₀ s' ∧ Proof.Scrypt.salsaX86.post s₀ s' := by
  refine WP.seq (load_ok hp fun s₁ k₁ m₁ a₁ => ?_)
  refine WP.mono (toDiag_ok a₁) fun s₂ ⟨a₂, g₂, m₂, r₂, w₂⟩ => ?_
  obtain k₂ := k₁.same ⟨g₂, m₂, r₂, w₂⟩
  refine WP.seq (WP.mono (rounds_ok a₂ 4) fun s₃ ⟨a₃, e₃⟩ => ?_)
  obtain k₃ := k₂.same e₃
  rw [finish, WP.block_append_iff]
  refine WP.mono (fromDiag_ok a₃) fun s₄ ⟨o₄, g₄, m₄, r₄, w₄⟩ => ?_
  refine WP.mono (addRows_ok hp (k₃.same ⟨g₄, m₄, r₄, w₄⟩) (by rw [m₄, e₃.mem, m₂, m₁]) o₄)
    fun s' ⟨k', h'⟩ => ⟨k', ?_⟩
  show Spec.Scrypt.bytesAt s'.mem (bA s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64)
  exact post_of h'

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaX86.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaX86.post s s' := by
  obtain hp := pre_of s hs
  obtain ⟨t, s', he, hk, h₂⟩ := correct hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, ?_⟩, h₂⟩
  · refine hk.gpr r ?_; rintro rfl; simp [calleeSaved] at hr
  · obtain ⟨-, -, hf⟩ := Exec.regions he (by decide)
    rw [hp.wr] at hf
    refine hf.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.ret_b, hp.ret_s]

end VG.Proof.Scrypt.X86

end

end

/-!
# scrypt on x86 (32-bit): common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are 32-bit pointers as addresses, `mul`, the
64-byte exclusive-or, and saving and restoring registers.
-/

@[expose] public section

namespace VG.Proof.Scrypt.X86

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_movm wp_store)
open VG.Proof.Scrypt.Memory (sub_off xorBytes_length bytesAt_length bytesAt_add
  bytesAt_writeBytes_sep)

/-! ## 32-bit pointers -/

theorem toNat_add32 {p : BitVec 32} {o : Nat} (h : p.toNat + o < 2 ^ 32) :
    (p + BitVec.ofNat 32 o).toNat = p.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith),
    Nat.mod_eq_of_lt h]

theorem add32 (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + BitVec.ofNat 32 j = p + BitVec.ofNat 32 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A register plus a small constant, as the code writes it. -/
theorem add32_lit (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + (OfNat.ofNat j : BitVec 32) =
      p + BitVec.ofNat 32 (o + (OfNat.ofNat j : Nat)) :=
  add32 p o j

theorem sub32 (p : BitVec 32) {o : Nat} (h : 64 ≤ o) :
    p + BitVec.ofNat 32 o - 64 = p + BitVec.ofNat 32 (o - 64) := by
  rw [show o = (o - 64) + 64 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_toNat32 (x : BitVec 32) : x = BitVec.ofNat 32 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ofNat_pred32 {k : Nat} (h : 1 ≤ k) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega_arith, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

/-- `[p + o]`, for a pointer `p` into a region that does not wrap around. -/
theorem addr_add {p : BitVec 32} {o : Nat} (h : p.toNat + o < 2 ^ 32) :
    (p + BitVec.ofNat 32 o).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 o := by
  have := addr_eq (x := p) (k := o) h
  exact this

theorem addr_zero (p : BitVec 32) : addr p 0 = p.setWidth 64 := by
  simp [addr]

/-- `and d, r` -/
theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-! ## `mul` -/

/-- `mul r`: `eax` is the low half of `eax * r`; `edx` and the flags change too. -/
theorem wp_mul {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (k : ∀ s', s'.gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) →
      (∀ q, q ≠ .eax → q ≠ .edx → s'.gpr q = s.gpr q) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.mul r :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (by simp [execMul, State.setReg])
    (fun q h₁ h₂ => by simp [execMul, State.setReg, State.setFlags, h₁, h₂]) rfl rfl rfl)

/-- `timesR m`: `eax = m r`, for the word `r` at `[esp + 8]`. -/
theorem timesR_ok {m : BitVec 32} {s : State} {r : BitVec 32}
    (hr : s.mem.readW (addr (s.gpr .esp) 8) 32 = r) (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .eax = BitVec.ofNat 32 (r.toNat * m.toNat) →
      (∀ q, q ≠ .eax → q ≠ .ecx → q ≠ .edx → s'.gpr q = s.gpr q) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (timesR m ++ rest)) s Q := by
  refine wp_movm (a := addr (s.gpr .esp) 8) rfl hin fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  refine wp_mul fun s₃ e₃ o₃ m₃ rd₃ wr₃ => k s₃ ?_ (fun q h1 h2 h3 => ?_) (by rw [m₃, u₂.mem, u₁.mem])
    (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
  · rw [e₃, u₂.other _ (by decide), u₁.gpr, hr, u₂.gpr]
  · rw [o₃ q h1 h3, u₂.other q h2, u₁.other q h1]

/-! ## Blocks of bytes -/

theorem writeW_xor128 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 128 ^^^ m'.readW b 128) =
      writeBytes m d (xorBytes (bytesAt m' a 16) (bytesAt m' b 16)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (128 : Nat) / 8 = 16 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    Proof.Sha256.Stream.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁,
    Mem.extractLsb'_read _ _ h₁]

/-- Sixteen more bytes of `[d] ← [x] xor [y]`. -/
theorem xor_mem16 (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 16 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 16 * n⟩ ⟨x, 16 * n⟩) (hdy : Region.Disjoint ⟨d, 16 * n⟩ ⟨y, 16 * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).writeW
      (d + BitVec.ofNat 64 (16 * k))
      ((writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).readW
          (x + BitVec.ofNat 64 (16 * k)) 128 ^^^
        (writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).readW
          (y + BitVec.ofNat 64 (16 * k)) 128) =
      writeBytes m d (xorBytes (bytesAt m x (16 * (k + 1))) (bytesAt m y (16 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length = 16 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (16 * k), 16⟩
      ⟨d, (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega_arith) (by omega_arith))).sub_right
      (Region.sub_prefix (by omega_arith))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (16 * k), 16⟩
      ⟨d, (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega_arith) (by omega_arith))).sub_right
      (Region.sub_prefix (by omega_arith))
  rw [writeW_xor128, bytesAt_writeBytes_sep _ _ sx (by omega_arith),
    bytesAt_writeBytes_sep _ _ sy (by omega_arith)]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (16 * k)) 16)
    (bytesAt m (y + BitVec.ofNat 64 (16 * k)) 16))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega_arith)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-! ## The 64-byte exclusive-or -/

/-- The first `n` sixteen-byte blocks of `[dst] ← [x] xor [src]`, for 64-byte
blocks at `d`, `x`, `y`, where `d` overlaps neither of the others. The code
uses `xmm0` and `xmm1`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .eax) (hx : xR ≠ .eax) (hs : sR ≠ .eax)
    {d x y : BitVec 32} (fd : d.toNat + 64 ≤ 2 ^ 32) (fx : x.toNat + 64 ≤ 2 ^ 32)
    (fy : y.toNat + 64 ≤ 2 ^ 32)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨x.setWidth 64, 64⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨y.setWidth 64, 64⟩) :
    ∀ n ≤ 4, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 4, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ k < 4, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ k < 4, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (d.setWidth 64)
        (xorBytes (bytesAt s.mem (x.setWidth 64) (16 * n)) (bytesAt s.mem (y.setWidth 64) (16 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_arith) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_ldq (a := x.setWidth 64 + BitVec.ofNat 64 (16 * n))
      (by rw [ea_at, g₁ _ hx, gx]; exact addr_eq (by omega_arith)) (by rw [rd₁, wr₁]; exact hinx n (by omega_arith))
      fun s₂ R₂ m₂ x₂ _ => ?_
    refine wp_ldq (a := y.setWidth 64 + BitVec.ofNat 64 (16 * n))
      (by rw [ea_at, R₂.gpr, g₁ _ hs, gy]; exact addr_eq (by omega_arith))
      (by rw [R₂.rd, R₂.wr, rd₁, wr₁]; exact hiny n (by omega_arith)) fun s₃ R₃ m₃ x₃ o₃ => ?_
    refine wp_xbin fun s₄ R₄ m₄ x₄ _ => ?_
    refine wp_stq (a := d.setWidth 64 + BitVec.ofNat 64 (16 * n))
      (by rw [ea_at, R₄.gpr, R₃.gpr, R₂.gpr, g₁ _ hd, gd]; exact addr_eq (by omega_arith))
      (by rw [R₄.wr, R₃.wr, R₂.wr, wr₁]; exact hout n (by omega_arith))
      fun s₅ R₅ m₅ _ => k s₅ (fun r h => by rw [R₅.gpr, R₄.gpr, R₃.gpr, R₂.gpr, g₁ r h])
        (by rw [R₅.rd, R₄.rd, R₃.rd, R₂.rd, rd₁]) (by rw [R₅.wr, R₄.wr, R₃.wr, R₂.wr, wr₁]) ?_
    rw [m₅, x₄, o₃ .xmm0 (by decide), x₂, x₃, m₄, m₃, m₂, m₁]
    exact xor_mem16 s.mem (n := 4) (by omega_arith) (by omega_arith) hdx hdy

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_arith, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by
    show s'.zf.map (!·) = _; rw [hz]; rfl
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, hi'⟩

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [ofNat_pred32 (by omega_arith), Nat.sub_sub]

theorem dec_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (k + 1 = n) := by
  rw [dec_count hk, Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega_arith)]
  exact decide_eq_decide.mpr (by omega_arith)

end VG.Proof.Scrypt.X86
