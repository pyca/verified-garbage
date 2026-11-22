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

theorem y_x {x a b : Nat} (hx : x < 256) : (x + 256 * (a + 65536 * b)) % 256 = x := by omega_using [hx]
theorem y_a {x a b : Nat} (hx : x < 256) (ha : a < 65536) : (x + 256 * (a + 65536 * b)) / 256 % 65536 = a := by
  omega_using [hx, ha]
theorem y_b {x a b : Nat} (hx : x < 256) (ha : a < 65536) : (x + 256 * (a + 65536 * b)) / 16777216 = b := by
  omega_using [hx, ha]

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

/-- The node `k` has number `i` in the table. -/
def Has (t : List Nat) (i k : Nat) : Prop := ∃ t₁ t₂, t = t₁ ++ k :: t₂ ∧ i = t₂.length

theorem Has.new (k : Nat) (t : List Nat) : Has (k :: t) t.length k := ⟨[], t, rfl, rfl⟩

theorem Has.cons {t : List Nat} {i k : Nat} (h : Has t i k) (k' : Nat) : Has (k' :: t) i k := by
  obtain ⟨t₁, t₂, rfl, rfl⟩ := h
  exact ⟨k' :: t₁, t₂, rfl, rfl⟩

/-- A node of the table has there the value it has of the table's nodes. -/
theorem Has.val (E : Env) {k : Nat} {t : List Nat} {i : Nat} (hw : Wf t) (h : Has t i k) :
    i < t.length ∧ val E t i = evalK E (val E t) k := by
  obtain ⟨t₁, t₂, rfl, rfl⟩ := h
  have hl : t₂.length < (t₁ ++ k :: t₂).length := by
    rw [List.length_append, List.length_cons]; omega_arith
  refine ⟨hl, ?_⟩
  rw [val_append E t₁ (show t₂.length < (k :: t₂).length by rw [List.length_cons]; omega_arith), val_new]
  refine (hw.append).1 E _ _ fun j hj => ?_
  rw [show t₁ ++ k :: t₂ = (t₁ ++ [k]) ++ t₂ by rw [List.append_assoc]; rfl, val_append E _ hj]

/-! ## Finding a node

The kernel walks a list at tens of microseconds an element, so the table is
not searched: the nodes' numbers are also in a hash table that is one
number, 8192 slots of 160 bits, a slot `1 + 2 (i + 65536 k)` for the node
`k` of number `i` and 0 when empty. Only what a slot says is used
(`HOk`): where a node is put does not matter to what the check proves. -/

/-- `k n`, with the number `n` evaluated. -/
def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (motive := fun _ => α) (Nat.succ n) (k n) (fun m => k m)

theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := rfl

/-- `2 ^ 160`. -/
def W2 : Nat := 1461501637330902918203684832716283019655932542976

theorem W2_eq : W2 = 2 ^ 160 := by decide

/-- Slot `j` of the hash table `H`. -/
def slot (H j : Nat) : Nat := (H >>> (160 * j)) % W2

/-- `H` with `e` in slot `j`, which was empty. -/
def setSlot (H j e : Nat) : Nat := H ||| (e <<< (160 * j))

theorem slot_testBit (H j b : Nat) : (slot H j).testBit b = (decide (b < 160) && H.testBit (160 * j + b)) := by
  rw [slot, W2_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem testBit_of_lt {e c : Nat} (he : e < W2) (hc : 160 ≤ c) : e.testBit c = false := by
  cases h : e.testBit c
  · rfl
  · have := Nat.ge_two_pow_of_testBit h
    have h2 : 2 ^ 160 ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hc
    rw [W2_eq] at he
    omega_using [this, h2, he]

theorem slot_zero (j : Nat) : slot 0 j = 0 := by
  rw [slot, Nat.zero_shiftRight, Nat.zero_mod]

theorem slot_set_self {H j e : Nat} (he : e < W2) (h0 : slot H j = 0) : slot (setSlot H j e) j = e := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [slot_testBit, setSlot, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hb : b < 160
  · have z : H.testBit (160 * j + b) = false := by
      have := slot_testBit H j b
      rw [h0, Nat.zero_testBit, decide_eq_true hb, Bool.true_and] at this
      exact this.symm
    rw [z, decide_eq_true hb, decide_eq_true (show 160 * j + b ≥ 160 * j by omega_arith), Bool.true_and,
      Bool.true_and, Bool.false_or, Nat.add_sub_cancel_left]
  · rw [decide_eq_false hb, Bool.false_and, testBit_of_lt he (by omega_using [hb])]

theorem slot_set_other {H j j' e : Nat} (he : e < W2) (hj : j' ≠ j) : slot (setSlot H j e) j' = slot H j' := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [slot_testBit, slot_testBit, setSlot, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hb : b < 160
  · rw [decide_eq_true hb, Bool.true_and, Bool.true_and]
    by_cases hl : 160 * j ≤ 160 * j' + b
    · rw [decide_eq_true hl, Bool.true_and, testBit_of_lt he (by omega_using [hl, hj, hb]), Bool.or_false]
    · rw [decide_eq_false hl, Bool.false_and, Bool.or_false]
  · rw [decide_eq_false hb, Bool.false_and, Bool.false_and]

/-- The slot of the node `k` of number `i`. -/
def pack (k i : Nat) : Nat := 1 + 2 * (i + 65536 * k)
def eKey (e : Nat) : Nat := e / 131072
def eId (e : Nat) : Nat := e / 2 % 65536

theorem eKey_pack {k i : Nat} (hi : i < 65536) : eKey (pack k i) = k := by unfold eKey pack; omega_using [hi]
theorem eId_pack {k i : Nat} (hi : i < 65536) : eId (pack k i) = i := by unfold eId pack; omega_using [hi]
theorem pack_ne (k i : Nat) : pack k i ≠ 0 := by unfold pack; omega_arith

/-- Every slot that is not empty is of a node of the table and its number. -/
def HOk (H : Nat) (t : List Nat) : Prop := ∀ j, slot H j ≠ 0 → Has t (eId (slot H j)) (eKey (slot H j))

theorem HOk.zero (t : List Nat) : HOk 0 t := fun j h => absurd (slot_zero j) h

/-- From slot `j`, in at most `fuel` slots: the number of the node `k`
(`inl`), or the first empty slot (`inr`). -/
def probe (H k : Nat) : Nat → Nat → Option (Nat ⊕ Nat)
  | 0, _ => none
  | fuel + 1, j =>
    forceNat (slot H j) fun e =>
      bif Nat.beq e 0 then some (.inr j)
      else bif Nat.beq (eKey e) k then some (.inl (eId e))
      else forceNat ((j + 1) % 8192) fun j' => probe H k fuel j'

theorem probe_found {H k : Nat} {t : List Nat} (hH : HOk H t) : ∀ {fuel j i : Nat},
    probe H k fuel j = some (.inl i) → Has t i k
  | 0, _, _, h => by cases h
  | fuel + 1, j, i, h => by
    rw [probe, forceNat_eq] at h
    cases e0 : Nat.beq (slot H j) 0
    · rw [e0, Bool.cond_false] at h
      cases ek : Nat.beq (eKey (slot H j)) k
      · rw [ek, Bool.cond_false, forceNat_eq] at h
        exact probe_found hH h
      · rw [ek, Bool.cond_true] at h
        cases h
        have := hH j (Nat.ne_of_beq_eq_false e0)
        rwa [Nat.eq_of_beq_eq_true ek] at this
    · rw [e0, Bool.cond_true] at h
      cases h

theorem probe_empty {H k : Nat} : ∀ {fuel j j' : Nat}, probe H k fuel j = some (.inr j') → slot H j' = 0
  | 0, _, _, h => by cases h
  | fuel + 1, j, j', h => by
    rw [probe, forceNat_eq] at h
    cases e0 : Nat.beq (slot H j) 0
    · rw [e0, Bool.cond_false] at h
      cases ek : Nat.beq (eKey (slot H j)) k
      · rw [ek, Bool.cond_false, forceNat_eq] at h
        exact probe_empty h
      · rw [ek, Bool.cond_true] at h
        cases h
    · rw [e0, Bool.cond_true] at h
      cases h
      exact Nat.eq_of_beq_eq_true e0

/-- The table with one more node, in an empty slot. -/
theorem HOk.insert {H j k : Nat} {t : List Nat} (hH : HOk H t) (h0 : slot H j = 0) (he : pack k t.length < W2)
    (hn : t.length < 65536) : HOk (setSlot H j (pack k t.length)) (k :: t) := fun j' hj' => by
  by_cases e : j' = j
  · subst e
    rw [slot_set_self he h0, eId_pack hn, eKey_pack hn]
    exact Has.new k t
  · rw [slot_set_other he e] at hj' ⊢
    exact (hH j' hj').cons k

/-! ## The program's state -/

/-- The numbers of the nodes the eight registers hold. -/
structure Regs where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
  x5 : Nat
  x6 : Nat
  x7 : Nat

def Regs.get : Regs → XReg → Nat
  | ⟨a, _, _, _, _, _, _, _⟩, .xmm0 => a
  | ⟨_, a, _, _, _, _, _, _⟩, .xmm1 => a
  | ⟨_, _, a, _, _, _, _, _⟩, .xmm2 => a
  | ⟨_, _, _, a, _, _, _, _⟩, .xmm3 => a
  | ⟨_, _, _, _, a, _, _, _⟩, .xmm4 => a
  | ⟨_, _, _, _, _, a, _, _⟩, .xmm5 => a
  | ⟨_, _, _, _, _, _, a, _⟩, .xmm6 => a
  | ⟨_, _, _, _, _, _, _, a⟩, .xmm7 => a

def Regs.set : Regs → XReg → Nat → Regs
  | ⟨_, b, c, d, e, f, g, h⟩, .xmm0, v => ⟨v, b, c, d, e, f, g, h⟩
  | ⟨a, _, c, d, e, f, g, h⟩, .xmm1, v => ⟨a, v, c, d, e, f, g, h⟩
  | ⟨a, b, _, d, e, f, g, h⟩, .xmm2, v => ⟨a, b, v, d, e, f, g, h⟩
  | ⟨a, b, c, _, e, f, g, h⟩, .xmm3, v => ⟨a, b, c, v, e, f, g, h⟩
  | ⟨a, b, c, d, _, f, g, h⟩, .xmm4, v => ⟨a, b, c, d, v, f, g, h⟩
  | ⟨a, b, c, d, e, _, g, h⟩, .xmm5, v => ⟨a, b, c, d, e, v, g, h⟩
  | ⟨a, b, c, d, e, f, _, h⟩, .xmm6, v => ⟨a, b, c, d, e, f, v, h⟩
  | ⟨a, b, c, d, e, f, g, _⟩, .xmm7, v => ⟨a, b, c, d, e, f, g, v⟩

theorem Regs.get_set (ρ : Regs) (r r' : XReg) (v : Nat) :
    (ρ.set r v).get r' = if r' = r then v else ρ.get r' := by
  cases ρ; cases r <;> cases r' <;> rfl

/-- The registers at the start: register `k` holds node `k`. -/
def Regs.init : Regs := ⟨0, 1, 2, 3, 4, 5, 6, 7⟩

/-- Register `k`. -/
def xr : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3 | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | _ => .xmm7

/-- The table (its length, its nodes, the newest first, which only the
proofs read, and the hash table of their numbers), the registers' nodes,
and the nodes of what was stored in the buffer, by offset. -/
structure St where
  n : Nat
  tab : List Nat
  h : Nat
  regs : Regs
  cells : List (Nat × Nat)

/-- The start: the registers' nodes. -/
def St.init : St :=
  ⟨8, [leaf 0 7, leaf 0 6, leaf 0 5, leaf 0 4, leaf 0 3, leaf 0 2, leaf 0 1, leaf 0 0], 0, .init, []⟩

/-- `d` holds the node `k`: its number in the table, where it goes if it is
not there (`none` if the hash table has no slot for it within 64 of its
own). The hash table stays the term that made it: the kernel's hash of a
numeral is of its low 64 bits, which are the same for every table. -/
def St.put (σ : St) (d : XReg) (k : Nat) : Option St :=
  match σ with
  | ⟨n, tab, H, regs, cells⟩ =>
    forceNat k fun k =>
      match probe H k 64 (k % 8191) with
      | some (.inl i) => some ⟨n, tab, H, regs.set d i, cells⟩
      | some (.inr j) =>
        forceNat (pack k n) fun e =>
          bif Nat.blt e W2 then forceNat (n + 1) fun n' => some ⟨n', k :: tab, setSlot H j e, regs.set d n, cells⟩
          else none
      | none => none

/-- What was stored at offset `o`. -/
def lookup : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (o', i) :: l, o => if Nat.beq o' o = true then some i else lookup l o

theorem lookup_some : ∀ {l : List (Nat × Nat)} {o i : Nat}, lookup l o = some i → (o, i) ∈ l
  | [], _, _, h => by cases h
  | (o', i') :: l, o, i, h => by
    unfold lookup at h
    by_cases e : Nat.beq o' o = true
    · rw [ite_eq_left e] at h; cases h; rw [Nat.eq_of_beq_eq_true e]; exact List.mem_cons_self
    · rw [ite_eq_right e] at h; exact List.mem_cons_of_mem _ (lookup_some h)

theorem lookup_none : ∀ {l : List (Nat × Nat)} {o : Nat}, lookup l o = none → ∀ c ∈ l, c.1 ≠ o
  | [], _, _, _, hc => by cases hc
  | (o', i') :: l, o, h, c, hc => by
    unfold lookup at h
    by_cases e : Nat.beq o' o = true
    · rw [ite_eq_left e] at h; cases h
    · rw [ite_eq_right e] at h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact fun e' => e (by rw [show o' = o from e']; exact Nat.beq_refl o)
      · exact lookup_none h c hc

/-- The stores, with `i` stored at offset `o`. -/
def setCell (l : List (Nat × Nat)) (o i : Nat) : List (Nat × Nat) := (o, i) :: l.filter fun c => !Nat.beq c.1 o

/-- Every store of `a` is one of `b`. -/
def cellsLe (a b : List (Nat × Nat)) : Bool :=
  a.all fun c => match lookup b c.1 with
    | some i => Nat.beq i c.2
    | none => false

theorem cellsLe_mem {a b : List (Nat × Nat)} (h : cellsLe a b = true) {c : Nat × Nat} (hc : c ∈ a) : c ∈ b := by
  have := List.all_eq_true.mp h c hc
  split at this <;> [rename_i i hi; cases this]
  have e := lookup_some hi
  rwa [Nat.eq_of_beq_eq_true this] at e

/-- The table's base register and name, the buffer's register and length,
the keys', and the bytes of the buffer the stores are within. -/
structure Params where
  tb : Reg
  name : String
  mreg : Reg
  mlen : Nat
  kreg : Reg
  klen : Nat
  slo : Nat
  shi : Nat

/-- What an instruction does to the nodes; `none` for an instruction, or
operands, this does not follow. -/
def step (p : Params) (σ : St) : Instr → Option St
  | .movdquTbl d m n ws =>
    if m.base = p.tb ∧ n = p.name ∧ m.disp % 8 = 0 ∧ m.disp / 8 + 2 ≤ ws.length then
      σ.put d (leaf 5 ((ws.getD (m.disp / 8 + 1) 0).toNat * 18446744073709551616 +
        (ws.getD (m.disp / 8) 0).toNat))
    else none
  | .movdquLoad d m =>
    if m.base = p.mreg then
      if m.disp % 16 = 0 ∧ m.disp + 16 ≤ p.mlen then
        match lookup σ.cells m.disp with
        | some i => some { σ with regs := σ.regs.set d i }
        | none => σ.put d (leaf 1 m.disp)
      else none
    else if m.base = p.kreg ∧ m.disp + 16 ≤ p.klen then σ.put d (leaf 3 m.disp)
    else none
  | .movqLoad d m =>
    if m.base = p.mreg then
      if m.disp % 8 = 0 ∧ m.disp + 8 ≤ p.mlen ∧ lookup σ.cells (m.disp - m.disp % 16) = none then
        σ.put d (leaf 2 m.disp)
      else none
    else if m.base = p.kreg ∧ m.disp + 8 ≤ p.klen then σ.put d (leaf 4 m.disp)
    else none
  | .movdquStore m r =>
    if m.base = p.mreg ∧ m.disp % 16 = 0 ∧ p.slo ≤ m.disp ∧ m.disp + 16 ≤ p.shi then
      some { σ with cells := setCell σ.cells m.disp (σ.regs.get r) }
    else none
  | .xop (.bin .movdqa d r) => some { σ with regs := σ.regs.set d (σ.regs.get r) }
  | .xop (.bin op d r) => σ.put d (mk 6 op.ctorIdx (σ.regs.get d) (σ.regs.get r))
  | .xop (.shift op d n) => σ.put d (mk 7 op.ctorIdx (σ.regs.get d) n.toNat)
  | .xop (.pshufd d r o) => σ.put d (mk 8 o.toNat (σ.regs.get r) 0)
  | .xop (.pshuflw d r o) => σ.put d (mk 9 o.toNat (σ.regs.get r) 0)
  | .xop (.pshufhw d r o) => σ.put d (mk 10 o.toNat (σ.regs.get r) 0)
  | .xop (.palignr d r n) => σ.put d (mk 11 n.toNat (σ.regs.get d) (σ.regs.get r))
  | _ => none

/-- The nodes after a block: at most 65536. -/
def run (p : Params) : St → List Instr → Option St
  | σ, [] => some σ
  | σ, i :: is =>
    if Nat.blt σ.n 65536 = true then
      match step p σ i with
      | some σ' => run p σ' is
      | none => none
    else none

/-- `P` and `Q` are followed, and from the same registers and memory they
leave the same node in `P`'s register and in `Q`'s of each pair of `outs`,
and store the same nodes at the same offsets of the buffer. -/
def equiv (p : Params) (P Q : List Instr) (outs : List (XReg × XReg)) : Bool :=
  match run p .init P with
  | none => false
  | some σ =>
    match run p ⟨σ.n, σ.tab, σ.h, .init, []⟩ Q with
    | none => false
    | some τ =>
      outs.all (fun ab => Nat.beq (σ.regs.get ab.1) (τ.regs.get ab.2)) && cellsLe σ.cells τ.cells &&
        cellsLe τ.cells σ.cells

end VG.X86.SseEquiv
