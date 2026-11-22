module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Two straight-line XMM programs compute the same, on x86 (32-bit)

Code whose instruction order and registers are chosen for speed (the rounds
of several blocks interleaved, every value in the register that is free
first) computes what the same instructions do one block after the other, in
registers chosen for the proof. `equiv p P Q outs` checks that of two
blocks `P` and `Q`, without knowing what either computes: it runs both from
the same registers and memory with every value a *node*, an instruction
applied to the nodes of its operands (`aesenclast`, the shuffles and the
bit operations are not interpreted), numbered in one table, so that a value
both programs compute has one number; and compares the numbers the two
leave in the registers `outs` pairs and in the bytes they store. A copy
(`movdqa`) gives its source's number, so copies, the order of instructions
that do not depend on each other, and the registers' names do not matter;
nothing else is equated (`pxor a, b` and `pxor b, a` are two nodes).

The code followed is `movdqa` and every other instruction of two XMM
registers, the shifts by a constant, `pshufd`, `pshuflw`, `pshufhw` and
`palignr`; the loads of a table an instruction carries (a constant, by its
value); and, with the registers and lengths of `Params`,

* loads and stores of 16 bytes at `[mreg + o]`, a *buffer* of `mlen` bytes,
  with `o` a multiple of 16, the stores within `[slo, shi)`: a load gives
  what the program stored there, or what the buffer held at the start;
  and loads of 8 bytes there (`movq`) of what was not stored;
* loads of 16 or 8 bytes at `[kreg + o]`, the *keys*, `klen` bytes apart
  from `[mreg + slo, mreg + shi)` (`Pre.sep`), which the program does not
  write.

`equiv_run`: from a state of `Pre p`, both blocks run, to states with the
same memory and, for each pair of `outs`, the same value in `P`'s register
of the pair as in `Q`'s; each state is the one they start in but for the
XMM registers and memory. `equiv_wp`: so a postcondition of `P` that only
reads those is one of `Q`.

The kernel evaluates `equiv` (`lit_decide`): a node is a number (its
operation and its operands' numbers packed, `mk`), found in the table by a
walk that compares numbers (`find`).
-/

@[expose] public section

namespace VG.X86.SseEquiv

open VG VG.X86

/-! ## Nodes -/

/-- The node of a value the program starts with: its kind (0 a register, 1
and 2 the buffer's 16 or 8 bytes at an offset, 3 and 4 the keys', 5 a
constant) and which. -/
def leaf (t x : Nat) : Nat := t + 16 * x

/-- The node of an instruction: its kind (6 an instruction of two
registers, 7 a shift, 8 to 10 the shuffles, 11 `palignr`), the operation or
its immediate, and its operands' numbers (or a shift's count). -/
def mk (t x a b : Nat) : Nat := t + 16 * (x + 256 * (a + 65536 * b))

def binOf (n : Nat) : XBinOp :=
  ([.movdqa, .paddd, .pxor, .por, .pand, .pandn, .punpckldq, .punpckhdq, .punpcklqdq, .punpckhqdq, .pshufb,
    .sha256msg1, .sha256msg2, .aesenc, .aesenclast, .paddq, .sha1msg1, .sha1msg2, .sha1nexte, .aesdec,
    .aesdeclast, .aesimc] : List XBinOp).getD n .movdqa

theorem binOf_idx (op : XBinOp) : binOf op.ctorIdx = op := by cases op <;> rfl

theorem bin_lt (op : XBinOp) : op.ctorIdx < 256 := by cases op <;> decide

def shiftOf (n : Nat) : XShiftOp :=
  ([.pslld, .psrld, .psllq, .psrlq, .pslldq, .psrldq] : List XShiftOp).getD n .pslld

theorem shiftOf_idx (op : XShiftOp) : shiftOf op.ctorIdx = op := by cases op <;> rfl

theorem shift_lt (op : XShiftOp) : op.ctorIdx < 256 := by cases op <;> decide

/-- The values a program starts with: register `k`'s, the buffer's 16 and
8 bytes at an offset, and the keys'. -/
structure Env where
  reg : Nat → BitVec 128
  mem : Nat → BitVec 128
  memq : Nat → BitVec 128
  key : Nat → BitVec 128
  keyq : Nat → BitVec 128

/-- A node's value by its kind `t` and the rest `y` of its number, with `v`
the values of the nodes by their numbers. -/
def sel (E : Env) (v : Nat → BitVec 128) (t y : Nat) : BitVec 128 :=
  match t with
  | 0 => E.reg y
  | 1 => E.mem y
  | 2 => E.memq y
  | 3 => E.key y
  | 4 => E.keyq y
  | 5 => BitVec.ofNat 128 y
  | 6 => (binOf (y % 256)).eval (v (y / 256 % 65536)) (v (y / 16777216))
  | 7 => (shiftOf (y % 256)).eval (v (y / 256 % 65536)) (BitVec.ofNat 8 (y / 16777216))
  | 8 => shufDwords (v (y / 256 % 65536)) (BitVec.ofNat 8 (y % 256))
  | 9 => shufLowWords (v (y / 256 % 65536)) (BitVec.ofNat 8 (y % 256))
  | 10 => shufHighWords (v (y / 256 % 65536)) (BitVec.ofNat 8 (y % 256))
  | 11 => alignRight (v (y / 256 % 65536)) (v (y / 16777216)) (BitVec.ofNat 8 (y % 256))
  | _ => 0

/-- A node's value. -/
def evalK (E : Env) (v : Nat → BitVec 128) (k : Nat) : BitVec 128 := sel E v (k % 16) (k / 16)

theorem evalK_leaf (E : Env) (v : Nat → BitVec 128) {t : Nat} (ht : t < 16) (x : Nat) :
    evalK E v (leaf t x) = sel E v t x := by
  unfold evalK leaf
  rw [show (t + 16 * x) % 16 = t by omega_using [ht], show (t + 16 * x) / 16 = x by omega_using [ht]]

theorem evalK_mk (E : Env) (v : Nat → BitVec 128) {t : Nat} (ht : t < 16) (x a b : Nat) :
    evalK E v (mk t x a b) = sel E v t (x + 256 * (a + 65536 * b)) :=
  evalK_leaf E v ht _

section
variable {x a b : Nat} (hx : x < 256) (ha : a < 65536)
include hx ha

theorem y_x : (x + 256 * (a + 65536 * b)) % 256 = x := by omega_using [hx]
theorem y_a : (x + 256 * (a + 65536 * b)) / 256 % 65536 = a := by omega_using [hx, ha]
theorem y_b : (x + 256 * (a + 65536 * b)) / 16777216 = b := by omega_using [hx, ha]

end

/-- A node's value depends on those of the nodes before number `n` only. -/
def Local (k n : Nat) : Prop :=
  ∀ (E : Env) (v v' : Nat → BitVec 128), (∀ i < n, v i = v' i) → evalK E v k = evalK E v' k

theorem Local.mono {k n m : Nat} (h : Local k n) (hn : n ≤ m) : Local k m :=
  fun E v v' hv => h E v v' fun i hi => hv i (Nat.lt_of_lt_of_le hi hn)

theorem local_leaf {t : Nat} (ht : t < 6) (x n : Nat) : Local (leaf t x) n := fun E v v' _ => by
  rw [evalK_leaf E v (by omega_using [ht]), evalK_leaf E v' (by omega_using [ht])]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega_using [ht]) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A node of the nodes `a` and `b`. -/
theorem local_mk {t x a b n : Nat} (ht : t < 16) (hx : x < 256) (ha : a < 65536) (han : a < n)
    (hb : b < n ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10) : Local (mk t x a b) n := fun E v v' hv => by
  rw [evalK_mk E v ht, evalK_mk E v' ht]
  have e1 := y_x (b := b) hx ha
  have e2 := y_a (b := b) hx ha
  have e3 := y_b (b := b) hx ha
  have va := hv a han
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
      (12 ≤ t ∧ t < 16) by omega_using [ht]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have vb := hv b (by omega_using [hb])
    show (binOf _).eval (v _) (v _) = (binOf _).eval (v' _) (v' _)
    rw [e2, e3, va, vb]
  · show (shiftOf _).eval (v _) _ = (shiftOf _).eval (v' _) _
    rw [e2, va]
  · show shufDwords (v _) _ = shufDwords (v' _) _
    rw [e2, va]
  · show shufLowWords (v _) _ = shufLowWords (v' _) _
    rw [e2, va]
  · show shufHighWords (v _) _ = shufHighWords (v' _) _
    rw [e2, va]
  · have vb := hv b (by omega_using [hb])
    show alignRight (v _) (v _) _ = alignRight (v' _) (v' _) _
    rw [e2, e3, va, vb]
  · rcases (show t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 by omega_using [h]) with rfl | rfl | rfl | rfl <;> rfl

/-! ## The table of nodes -/

/-- The value of number `i` among the values `vs`, the newest first: the
value of number 0 is the last. -/
def nth : List (BitVec 128) → Nat → BitVec 128
  | [], _ => 0
  | v :: vs, i => if i = vs.length then v else nth vs i

theorem nth_self (v : BitVec 128) (vs : List (BitVec 128)) : nth (v :: vs) vs.length = v := by
  rw [nth, ite_eq_left rfl]

theorem nth_cons {v : BitVec 128} {vs : List (BitVec 128)} {i : Nat} (h : i < vs.length) :
    nth (v :: vs) i = nth vs i := by
  rw [nth, ite_eq_right (Nat.ne_of_lt h)]

theorem nth_append (l : List (BitVec 128)) {vs : List (BitVec 128)} {i : Nat} (h : i < vs.length) :
    nth (l ++ vs) i = nth vs i := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.cons_append, nth_cons (by rw [List.length_append]; omega_using [h]), ih]

/-- The values of the nodes of a table, the newest first. -/
def vals (E : Env) : List Nat → List (BitVec 128)
  | [] => []
  | k :: t => evalK E (nth (vals E t)) k :: vals E t

theorem vals_length (E : Env) (t : List Nat) : (vals E t).length = t.length := by
  induction t with
  | nil => rfl
  | cons k t ih => rw [vals, List.length_cons, List.length_cons, ih]

theorem vals_append (E : Env) (l t : List Nat) : ∃ l', vals E (l ++ t) = l' ++ vals E t := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons k l ih =>
    obtain ⟨l', e⟩ := ih
    exact ⟨evalK E (nth (vals E (l ++ t))) k :: l', by rw [List.cons_append, vals, e, List.cons_append]⟩

/-- The value of the node of number `i` of the table `t`. -/
def val (E : Env) (t : List Nat) (i : Nat) : BitVec 128 := nth (vals E t) i

/-- A longer table gives the nodes it had the values they had. -/
theorem val_append (E : Env) (l : List Nat) {t : List Nat} {i : Nat} (h : i < t.length) :
    val E (l ++ t) i = val E t i := by
  obtain ⟨l', e⟩ := vals_append E l t
  rw [val, e, nth_append l' (by rw [vals_length]; exact h)]; rfl

theorem val_new (E : Env) (k : Nat) (t : List Nat) : val E (k :: t) t.length = evalK E (val E t) k := by
  rw [val, vals, ← vals_length E t, nth_self]; rfl

/-- Every node of the table is of nodes before it. -/
def Wf : List Nat → Prop
  | [] => True
  | k :: t => Local k t.length ∧ Wf t

theorem Wf.append {l t : List Nat} (h : Wf (l ++ t)) : Wf t := by
  induction l with
  | nil => exact h
  | cons k l ih => exact ih h.2

/-- `k n`, with the number `n` evaluated. -/
def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (motive := fun _ => α) (Nat.succ n) (k n) (fun m => k m)

theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := rfl

/-- The number of the node `k` in a table of `n` nodes, if it is there. -/
def find (k : Nat) : List Nat → Nat → Option Nat
  | [], _ => none
  | k' :: t, n => forceNat (n - 1) fun m => if Nat.beq k' k = true then some m else find k t m

theorem find_some {k : Nat} : ∀ {t : List Nat} {i : Nat}, find k t t.length = some i →
    ∃ t₁ t₂, t = t₁ ++ k :: t₂ ∧ i = t₂.length
  | [], _, h => by cases h
  | k' :: t, i, h => by
    rw [find, forceNat_eq, List.length_cons, Nat.add_sub_cancel] at h
    by_cases e : Nat.beq k' k = true
    · rw [ite_eq_left e] at h
      cases h
      exact ⟨[], t, by rw [Nat.eq_of_beq_eq_true e]; rfl, rfl⟩
    · rw [ite_eq_right e] at h
      obtain ⟨t₁, t₂, rfl, rfl⟩ := find_some h
      exact ⟨k' :: t₁, t₂, rfl, rfl⟩

/-- A node found in the table has there the value it has of the table's
nodes. -/
theorem find_val (E : Env) {k : Nat} {t : List Nat} {i : Nat} (hw : Wf t) (h : find k t t.length = some i) :
    i < t.length ∧ val E t i = evalK E (val E t) k := by
  obtain ⟨t₁, t₂, rfl, rfl⟩ := find_some h
  have hl : t₂.length < (t₁ ++ k :: t₂).length := by
    rw [List.length_append, List.length_cons]; omega_arith
  refine ⟨hl, ?_⟩
  rw [val_append E t₁ (show t₂.length < (k :: t₂).length by rw [List.length_cons]; omega_arith), val_new]
  refine (hw.append).1 E _ _ fun j hj => ?_
  rw [show t₁ ++ k :: t₂ = (t₁ ++ [k]) ++ t₂ by rw [List.append_assoc]; rfl, val_append E _ hj]

end VG.X86.SseEquiv
