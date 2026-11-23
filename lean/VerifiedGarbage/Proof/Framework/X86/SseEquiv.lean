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

The kernel evaluates `equiv` (`lit_decide`), about half a millisecond an
instruction: a node is a number (its operation and its operands' numbers
packed, `mk`), found through a hash table that is one number (`probe`), as
are the registers' nodes (`rget`); the arithmetic on its path is `Nat`'s
functions themselves, which the kernel computes without unfolding an
instance.
-/

@[expose] public section

namespace VG.X86.SseEquiv

open VG VG.X86

/-! ## Nodes -/

/-- The node of a value the program starts with: its kind (0 a register, 1
and 2 the buffer's 16 or 8 bytes at an offset, 3 and 4 the keys', 5 a
constant) and which. -/
def leaf (t x : Nat) : Nat := Nat.add t (Nat.mul 16 x)

theorem leaf_eq (t x : Nat) : leaf t x = t + 16 * x := rfl

/-- The node of an instruction: its kind (6 an instruction of two
registers, 7 a shift, 8 to 10 the shuffles, 11 `palignr`), the operation or
its immediate, and its operands' numbers (or a shift's count). -/
def mk (t x a b : Nat) : Nat :=
  Nat.add t (Nat.mul 16 (Nat.add x (Nat.mul 256 (Nat.add a (Nat.mul 65536 b)))))

theorem mk_eq (t x a b : Nat) : mk t x a b = leaf t (x + 256 * (a + 65536 * b)) := rfl

def binOf (n : Nat) : XBinOp :=
  ([.movdqa, .paddd, .pxor, .por, .pand, .pandn, .punpckldq, .punpckhdq, .punpcklqdq, .punpckhqdq, .pshufb,
    .sha256msg1, .sha256msg2, .aesenc, .aesenclast, .paddq, .sha1msg1, .sha1msg2, .sha1nexte, .aesdec,
    .aesdeclast, .aesimc, .paddw, .psubw, .packssdw, .punpcklwd, .punpckhwd] : List XBinOp).getD n .movdqa

theorem binOf_idx (op : XBinOp) : binOf op.ctorIdx = op := by cases op <;> rfl

theorem bin_lt (op : XBinOp) : op.ctorIdx < 256 := by cases op <;> decide

def shiftOf (n : Nat) : XShiftOp :=
  ([.pslld, .psrld, .psllq, .psrlq, .pslldq, .psrldq, .psraw] : List XShiftOp).getD n .pslld

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
  rw [evalK, leaf_eq]
  rw [show (t + 16 * x) % 16 = t by omega_using [ht], show (t + 16 * x) / 16 = x by omega_using [ht]]

theorem evalK_mk (E : Env) (v : Nat → BitVec 128) {t : Nat} (ht : t < 16) (x a b : Nat) :
    evalK E v (mk t x a b) = sel E v t (x + 256 * (a + 65536 * b)) := by
  rw [mk_eq]; exact evalK_leaf E v ht _

theorem y_x {x a b : Nat} (hx : x < 256) : (x + 256 * (a + 65536 * b)) % 256 = x := by omega_using [hx]
theorem y_a {x a b : Nat} (hx : x < 256) (ha : a < 65536) : (x + 256 * (a + 65536 * b)) / 256 % 65536 = a := by
  omega_using [hx, ha]
theorem y_b {x a b : Nat} (hx : x < 256) (ha : a < 65536) : (x + 256 * (a + 65536 * b)) / 16777216 = b := by
  omega_using [hx, ha]

/-- A node's value depends on those of the nodes before number `n` only. -/
def Local (k n : Nat) : Prop :=
  ∀ (E : Env) (v v' : Nat → BitVec 128), (∀ i < n, v i = v' i) → evalK E v k = evalK E v' k

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
number, slots of 160 bits (`Params.hs` of them: an operation on the number
costs the kernel about half a microsecond a kilobyte), a slot
`1 + 2 (i + 65536 k)` for the node `k` of number `i` and 0 when empty. Only
what a slot says is used (`HOk`): where a node is put does not matter to
what the check proves. -/

/-- `k n`, with the number `n` evaluated. -/
def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (motive := fun _ => α) (Nat.succ n) (k n) (fun m => k m)

theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := rfl

/-- `2 ^ 160`. -/
def W2 : Nat := 1461501637330902918203684832716283019655932542976

theorem W2_eq : W2 = 2 ^ 160 := by decide

/-- `2 ^ 160 - 1`. -/
def W1 : Nat := 1461501637330902918203684832716283019655932542975

theorem W1_eq : W1 = 2 ^ 160 - 1 := by decide

/-- Slot `j` of the hash table `H`. -/
def slot (H j : Nat) : Nat := Nat.land (Nat.shiftRight H (Nat.mul 160 j)) W1

theorem slot_eq (H j : Nat) : slot H j = (H >>> (160 * j)) &&& W1 := rfl

/-- `H` with `e` in slot `j`, which was empty. -/
def setSlot (H j e : Nat) : Nat := Nat.lor H (Nat.shiftLeft e (Nat.mul 160 j))

theorem setSlot_eq (H j e : Nat) : setSlot H j e = H ||| (e <<< (160 * j)) := rfl

theorem slot_testBit (H j b : Nat) : (slot H j).testBit b = (decide (b < 160) && H.testBit (160 * j + b)) := by
  rw [slot_eq, W1_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem testBit_of_lt {e c : Nat} (he : e < W2) (hc : 160 ≤ c) : e.testBit c = false := by
  cases h : e.testBit c
  · rfl
  · have := Nat.ge_two_pow_of_testBit h
    have h2 : 2 ^ 160 ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hc
    rw [W2_eq] at he
    omega_using [this, h2, he]

theorem slot_zero (j : Nat) : slot 0 j = 0 := by
  rw [slot_eq, Nat.zero_shiftRight, Nat.zero_and]

theorem slot_set_self {H j e : Nat} (he : e < W2) (h0 : slot H j = 0) : slot (setSlot H j e) j = e := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [slot_testBit, setSlot_eq, Nat.testBit_or, Nat.testBit_shiftLeft]
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
  rw [slot_testBit, slot_testBit, setSlot_eq, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hb : b < 160
  · rw [decide_eq_true hb, Bool.true_and, Bool.true_and]
    by_cases hl : 160 * j ≤ 160 * j' + b
    · rw [decide_eq_true hl, Bool.true_and, testBit_of_lt he (by omega_using [hl, hj, hb]), Bool.or_false]
    · rw [decide_eq_false hl, Bool.false_and, Bool.or_false]
  · rw [decide_eq_false hb, Bool.false_and, Bool.false_and]

/-- The slot of the node `k` of number `i`. -/
def pack (k i : Nat) : Nat := Nat.add 1 (Nat.mul 2 (Nat.add i (Nat.mul 65536 k)))
def eKey (e : Nat) : Nat := Nat.div e 131072
def eId (e : Nat) : Nat := Nat.mod (Nat.div e 2) 65536

theorem pack_eq (k i : Nat) : pack k i = 1 + 2 * (i + 65536 * k) := rfl
theorem eKey_eq (e : Nat) : eKey e = e / 131072 := rfl
theorem eId_eq (e : Nat) : eId e = e / 2 % 65536 := rfl

theorem eKey_pack {k i : Nat} (hi : i < 65536) : eKey (pack k i) = k := by
  rw [eKey_eq, pack_eq]; omega_using [hi]
theorem eId_pack {k i : Nat} (hi : i < 65536) : eId (pack k i) = i := by
  rw [eId_eq, pack_eq]; omega_using [hi]

/-- Every slot that is not empty is of a node of the table and its number. -/
def HOk (H : Nat) (t : List Nat) : Prop := ∀ j, slot H j ≠ 0 → Has t (eId (slot H j)) (eKey (slot H j))

theorem HOk.zero (t : List Nat) : HOk 0 t := fun j h => absurd (slot_zero j) h

/-- From slot `j` of `hs`, in at most `fuel` slots: the number of the node
`k` (`inl`), or the first empty slot (`inr`). -/
def probe (hs H k : Nat) : Nat → Nat → Option (Nat ⊕ Nat)
  | 0, _ => none
  | fuel + 1, j =>
    forceNat (slot H j) fun e =>
      bif Nat.beq e 0 then some (.inr j)
      else bif Nat.beq (eKey e) k then some (.inl (eId e))
      else forceNat (Nat.mod (Nat.succ j) hs) fun j' => probe hs H k fuel j'

theorem probe_found {hs H k : Nat} {t : List Nat} (hH : HOk H t) : ∀ {fuel j i : Nat},
    probe hs H k fuel j = some (.inl i) → Has t i k
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

theorem probe_empty {hs H k : Nat} : ∀ {fuel j j' : Nat}, probe hs H k fuel j = some (.inr j') → slot H j' = 0
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

/-- The number of the node the register `r` holds: the registers' numbers
are one number, 16 bits each (a match on a register costs the kernel a
quarter of a millisecond, two shifts a few microseconds). -/
def rget (R : Nat) (r : XReg) : Nat := Nat.land (Nat.shiftRight R (Nat.mul 16 r.ctorIdx)) 65535

theorem rget_eq (R : Nat) (r : XReg) : rget R r = (R >>> (16 * r.ctorIdx)) &&& 65535 := rfl

/-- The registers with `r` holding the node of number `v`. -/
def rset (R : Nat) (r : XReg) (v : Nat) : Nat :=
  Nat.xor R (Nat.shiftLeft (Nat.xor (rget R r) v) (Nat.mul 16 r.ctorIdx))

theorem rset_eq (R : Nat) (r : XReg) (v : Nat) : rset R r v = R ^^^ ((rget R r ^^^ v) <<< (16 * r.ctorIdx)) := rfl

/-- The registers at the start: register `k` holds node `k`. -/
def rinit : Nat := 0x00070006000500040003000200010000

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
  regs : Nat
  cells : List (Nat × Nat)

/-- The start: the registers' nodes. -/
def St.init : St :=
  ⟨8, [leaf 0 7, leaf 0 6, leaf 0 5, leaf 0 4, leaf 0 3, leaf 0 2, leaf 0 1, leaf 0 0], 0, rinit, []⟩

/-- `d` holds the node `k`: its number in the table, where it goes if it is
not there (`none` if the hash table of `hs` slots has no slot for it within
64 of its own, or the table has 65536 nodes). The hash table stays the term
that made it: the kernel's hash of a numeral is of its low 64 bits, which
are the same for every table. -/
def St.put (hs : Nat) (σ : St) (d : XReg) (k : Nat) : Option St :=
  match σ with
  | ⟨n, tab, H, regs, cells⟩ =>
    forceNat k fun k =>
      match probe hs H k 64 (Nat.mod k hs) with
      | some (.inl i) => forceNat (rset regs d i) fun regs' => some ⟨n, tab, H, regs', cells⟩
      | some (.inr j) =>
        forceNat (pack k n) fun e =>
          bif Nat.blt e W2 && Nat.blt n 65536 then
            forceNat (Nat.succ n) fun n' => forceNat (rset regs d n) fun regs' =>
              some ⟨n', k :: tab, setSlot H j e, regs', cells⟩
          else none
      | none => none

/-- `d` holds the node of number `i`. -/
def St.alias (σ : St) (d : XReg) (i : Nat) : St :=
  match σ with
  | ⟨n, tab, H, regs, cells⟩ => forceNat (rset regs d i) fun regs' => ⟨n, tab, H, regs', cells⟩

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
  /-- The hash table's slots: enough for the nodes of both programs (a
  node that finds no slot within 64 of its own fails the check). -/
  hs : Nat := 2039

/-- What an instruction does to the nodes; `none` for an instruction, or
operands, this does not follow. -/
def step (p : Params) (σ : St) : Instr → Option St
  | .movdquTbl d m n ws =>
    if m.base = p.tb ∧ n = p.name ∧ m.disp % 8 = 0 ∧ m.disp / 8 + 2 ≤ ws.length then
      σ.put p.hs d (leaf 5 (Nat.add (Nat.mul (ws.getD (m.disp / 8 + 1) 0).toNat 18446744073709551616)
        (ws.getD (m.disp / 8) 0).toNat))
    else none
  | .movdquLoad d m =>
    if m.base = p.mreg then
      if m.disp % 16 = 0 ∧ m.disp + 16 ≤ p.mlen then
        match lookup σ.cells m.disp with
        | some i => some (σ.alias d i)
        | none => σ.put p.hs d (leaf 1 m.disp)
      else none
    else if m.base = p.kreg ∧ m.disp + 16 ≤ p.klen then σ.put p.hs d (leaf 3 m.disp)
    else none
  | .movqLoad d m =>
    if m.base = p.mreg then
      if m.disp % 8 = 0 ∧ m.disp + 8 ≤ p.mlen ∧ lookup σ.cells (m.disp - m.disp % 16) = none then
        σ.put p.hs d (leaf 2 m.disp)
      else none
    else if m.base = p.kreg ∧ m.disp + 8 ≤ p.klen then σ.put p.hs d (leaf 4 m.disp)
    else none
  | .movdquStore m r =>
    if m.base = p.mreg ∧ m.disp % 16 = 0 ∧ p.slo ≤ m.disp ∧ m.disp + 16 ≤ p.shi then
      match σ with
      | ⟨n, tab, H, regs, cells⟩ => some ⟨n, tab, H, regs, setCell cells m.disp (rget regs r)⟩
    else none
  | .xop (.bin op d r) =>
    bif Nat.beq op.ctorIdx 0 then some (σ.alias d (rget σ.regs r))
    else σ.put p.hs d (mk 6 op.ctorIdx (rget σ.regs d) (rget σ.regs r))
  | .xop (.shift op d n) => σ.put p.hs d (mk 7 op.ctorIdx (rget σ.regs d) n.toNat)
  | .xop (.pshufd d r o) => σ.put p.hs d (mk 8 o.toNat (rget σ.regs r) 0)
  | .xop (.pshuflw d r o) => σ.put p.hs d (mk 9 o.toNat (rget σ.regs r) 0)
  | .xop (.pshufhw d r o) => σ.put p.hs d (mk 10 o.toNat (rget σ.regs r) 0)
  | .xop (.palignr d r n) => σ.put p.hs d (mk 11 n.toNat (rget σ.regs d) (rget σ.regs r))
  | _ => none

/-- The nodes after a block. -/
def run (p : Params) : St → List Instr → Option St
  | σ, [] => some σ
  | σ, i :: is =>
    match step p σ i with
    | some σ' => run p σ' is
    | none => none

/-- `P` and `Q` are followed, and from the same registers and memory they
leave the same node in `P`'s register and in `Q`'s of each pair of `outs`,
and store the same nodes at the same offsets of the buffer. -/
def equiv (p : Params) (P Q : List Instr) (outs : List (XReg × XReg)) : Bool :=
  match run p .init P with
  | none => false
  | some σ =>
    match run p ⟨σ.n, σ.tab, σ.h, rinit, []⟩ Q with
    | none => false
    | some τ =>
      outs.all (fun ab => Nat.beq (rget σ.regs ab.1) (rget τ.regs ab.2)) && cellsLe σ.cells τ.cells &&
        cellsLe τ.cells σ.cells

/-! ## The registers' numbers -/

theorem rget_testBit (R : Nat) (r : XReg) (b : Nat) :
    (rget R r).testBit b = (decide (b < 16) && R.testBit (16 * r.ctorIdx + b)) := by
  rw [rget_eq, show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem rget_lt (R : Nat) (r : XReg) : rget R r < 65536 := by
  rw [rget_eq]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem testBit_of_lt16 {v c : Nat} (hv : v < 65536) (hc : 16 ≤ c) : v.testBit c = false := by
  cases h : v.testBit c
  · rfl
  · have := Nat.ge_two_pow_of_testBit h
    have h2 : 2 ^ 16 ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) hc
    omega_using [this, h2, hv]

theorem ctorIdx_inj {r r' : XReg} (h : r'.ctorIdx = r.ctorIdx) : r' = r := by
  cases r <;> cases r' <;> first | rfl | cases h

theorem ctorIdx_lt (r : XReg) : r.ctorIdx < 8 := by cases r <;> decide

/-- A register holds what was put there, and the others what they held. -/
theorem rget_rset (R : Nat) (r r' : XReg) {v : Nat} (hv : v < 65536) :
    rget (rset R r v) r' = if r' = r then v else rget R r' := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [rget_testBit, rset_eq, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_xor]
  by_cases hb : b < 16
  · rw [decide_eq_true hb, Bool.true_and]
    by_cases e : r' = r
    · subst e
      rw [ite_eq_left rfl, decide_eq_true (show 16 * r'.ctorIdx + b ≥ 16 * r'.ctorIdx by omega_arith), Bool.true_and,
        Nat.add_sub_cancel_left, rget_testBit, decide_eq_true hb, Bool.true_and]
      cases R.testBit (16 * r'.ctorIdx + b) <;> cases v.testBit b <;> rfl
    · rw [ite_eq_right e, rget_testBit R r' b, decide_eq_true hb, Bool.true_and]
      have hne : r'.ctorIdx ≠ r.ctorIdx := fun h => e (ctorIdx_inj h)
      by_cases hl : 16 * r.ctorIdx ≤ 16 * r'.ctorIdx + b
      · rw [decide_eq_true hl, Bool.true_and, testBit_of_lt16 (rget_lt R r) (by omega_using [hl, hne, hb]),
          testBit_of_lt16 hv (by omega_using [hl, hne, hb])]
        cases R.testBit (16 * r'.ctorIdx + b) <;> rfl
      · rw [decide_eq_false hl, Bool.false_and, Bool.xor_false]
  · rw [decide_eq_false hb, Bool.false_and]
    by_cases e : r' = r
    · rw [ite_eq_left e, testBit_of_lt16 hv (by omega_using [hb])]
    · rw [ite_eq_right e, testBit_of_lt16 (rget_lt R r') (by omega_using [hb])]

theorem rinit_get (r : XReg) : rget rinit r = r.ctorIdx := by cases r <;> rfl

/-! ## A node in a register -/

/-- What `put` gives: a table with at most one more node, in which `k` has
the number that `d` gets, and the value it has of the table's nodes. -/
theorem put_ok {hs : Nat} {σ σ' : St} {d : XReg} {k : Nat} (h : σ.put hs d k = some σ') (hlen : σ.n = σ.tab.length)
    (hw : Wf σ.tab) (hH : HOk σ.h σ.tab) (hk : Local k σ.n) (E : Env) :
    ∃ i l, σ'.tab = l ++ σ.tab ∧ σ'.n = σ'.tab.length ∧ Wf σ'.tab ∧ HOk σ'.h σ'.tab ∧ σ'.regs = rset σ.regs d i ∧
      σ'.cells = σ.cells ∧ i < σ'.n ∧ (σ.n ≤ 65536 → σ'.n ≤ 65536) ∧
      val E σ'.tab i = evalK E (val E σ.tab) k := by
  obtain ⟨n, tab, H, regs, cells⟩ := σ
  have hlen : n = tab.length := hlen
  have hw : Wf tab := hw
  have hH : HOk H tab := hH
  have hk : Local k n := hk
  subst hlen
  unfold St.put at h
  simp only [forceNat_eq] at h
  split at h
  · rename_i i hp
    cases h
    obtain ⟨hi, hv⟩ := (probe_found hH hp).val E hw
    exact ⟨i, [], rfl, rfl, hw, hH, rfl, rfl, hi, fun h => h, hv⟩
  · rename_i j hp
    cases hb : (Nat.blt (pack k tab.length) W2 && Nat.blt tab.length 65536)
    · rw [hb, Bool.cond_false] at h; cases h
    · rw [hb, Bool.cond_true] at h
      cases h
      rw [Bool.and_eq_true] at hb
      have he : pack k tab.length < W2 := Nat.blt_eq.mp hb.1
      have hn : tab.length < 65536 := Nat.blt_eq.mp hb.2
      exact ⟨tab.length, [k], rfl, rfl, ⟨hk, hw⟩, hH.insert (probe_empty hp) he hn, rfl, rfl, Nat.lt_succ_self _,
        fun _ => hn, val_new E k tab⟩
  · cases h

/-! ## What the nodes say of a state -/

/-- The values a state starts with. -/
def envOf (p : Params) (s : State) : Env where
  reg k := s.xmm (xr k)
  mem o := s.mem.readW ((s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 o) 128
  memq o := (0 : BitVec 64) ++ s.mem.readW ((s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 o) 64
  key o := s.mem.readW ((s.gpr p.kreg).setWidth 64 + BitVec.ofNat 64 o) 128
  keyq o := (0 : BitVec 64) ++ s.mem.readW ((s.gpr p.kreg).setWidth 64 + BitVec.ofNat 64 o) 64

/-- What the code needs of the state it starts in: the table's register
holds its address; the buffer and the keys do not wrap around and are
readable, the buffer writable where the stores go, and the keys apart from
there. -/
structure Pre (p : Params) (s : State) : Prop where
  tb : s.gpr p.tb = s.syms p.name
  mfit : (s.gpr p.mreg).toNat + p.mlen ≤ 2 ^ 32
  kfit : (s.gpr p.kreg).toNat + p.klen ≤ 2 ^ 32
  shi : p.shi ≤ p.mlen
  mrd : ∀ o n, o + n ≤ p.mlen → InRegions (s.rd ++ s.wr) (addr (s.gpr p.mreg) o) n
  mwr : ∀ o, p.slo ≤ o → o + 16 ≤ p.shi → InRegions s.wr (addr (s.gpr p.mreg) o) 16
  krd : ∀ o n, o + n ≤ p.klen → InRegions (s.rd ++ s.wr) (addr (s.gpr p.kreg) o) n
  sep : Region.Disjoint ⟨(s.gpr p.kreg).setWidth 64, p.klen⟩
    ⟨(s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 p.slo, p.shi - p.slo⟩

/-- The 16 bytes of a store. -/
def cellR (p : Params) (s₀ : State) (c : Nat × Nat) : Region :=
  ⟨(s₀.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 c.1, 16⟩

/-- The state `s` the nodes `σ` describe, from the state `s₀` the program
starts in: `s₀` but for the XMM registers and memory; every register holds
its node's value; memory is as it was outside the stores, and holds in each
its node's value. -/
structure Inv (p : Params) (s₀ : State) (σ : St) (s : State) : Prop where
  same : ∃ f m, s = { s₀ with xmm := f, mem := m }
  len : σ.n = σ.tab.length
  nle : σ.n ≤ 65536
  wf : Wf σ.tab
  hok : HOk σ.h σ.tab
  regs : ∀ r, rget σ.regs r < σ.n ∧ s.xmm r = val (envOf p s₀) σ.tab (rget σ.regs r)
  frame : Frame (σ.cells.map (cellR p s₀)) s₀.mem s.mem
  cells : ∀ c ∈ σ.cells, c.1 % 16 = 0 ∧ p.slo ≤ c.1 ∧ c.1 + 16 ≤ p.shi ∧ c.2 < σ.n ∧
    s.mem.readW ((s₀.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 c.1) 128 = val (envOf p s₀) σ.tab c.2

section
variable {p : Params} {s₀ s : State} {σ σ' : St}

theorem Inv.gpr (h : Inv p s₀ σ s) : s.gpr = s₀.gpr := by obtain ⟨f, m, rfl⟩ := h.same; rfl
theorem Inv.rd (h : Inv p s₀ σ s) : s.rd = s₀.rd := by obtain ⟨f, m, rfl⟩ := h.same; rfl
theorem Inv.wr (h : Inv p s₀ σ s) : s.wr = s₀.wr := by obtain ⟨f, m, rfl⟩ := h.same; rfl
theorem Inv.syms (h : Inv p s₀ σ s) : s.syms = s₀.syms := by obtain ⟨f, m, rfl⟩ := h.same; rfl

/-- The table of `σ'` is that of `σ` with more nodes. -/
def Ext (σ σ' : St) : Prop := ∃ l, σ'.tab = l ++ σ.tab

theorem Ext.refl (σ : St) : Ext σ σ := ⟨[], rfl⟩

theorem Ext.trans {a b c : St} (h₁ : Ext a b) (h₂ : Ext b c) : Ext a c := by
  obtain ⟨l₁, e₁⟩ := h₁
  obtain ⟨l₂, e₂⟩ := h₂
  exact ⟨l₂ ++ l₁, by rw [e₂, e₁, List.append_assoc]⟩

/-- A register that gets the value of the node `k`. -/
theorem Inv.put (hI : Inv p s₀ σ s) {d : XReg} {k : Nat} (h : σ.put p.hs d k = some σ') (hk : Local k σ.n)
    {v : BitVec 128} (hv : evalK (envOf p s₀) (val (envOf p s₀) σ.tab) k = v) :
    Inv p s₀ σ' (s.setXmm d v) ∧ Ext σ σ' := by
  obtain ⟨i, l, ht, hl, hw, hh, hr, hc, hi, hn, hval⟩ := put_ok h hI.len hI.wf hI.hok hk (envOf p s₀)
  have hlen : σ.n ≤ σ'.n := by rw [hI.len, hl, ht, List.length_append]; omega_arith
  have i16 : i < 65536 := Nat.lt_of_lt_of_le hi (hn hI.nle)
  have stab : ∀ {j : Nat}, j < σ.n → val (envOf p s₀) σ'.tab j = val (envOf p s₀) σ.tab j := fun hj => by
    rw [ht]; exact val_append _ l (by rw [← hI.len]; exact hj)
  refine ⟨⟨?_, hl, hn hI.nle, hw, hh, fun r => ?_, ?_, fun c hc' => ?_⟩, l, ht⟩
  · obtain ⟨f, m, rfl⟩ := hI.same; exact ⟨_, _, rfl⟩
  · rw [hr, rget_rset _ _ _ i16]
    show _ ∧ (if r = d then v else s.xmm r) = _
    by_cases e : r = d
    · rw [ite_eq_left e, ite_eq_left e, hval, hv]; exact ⟨hi, rfl⟩
    · rw [ite_eq_right e, ite_eq_right e, stab (hI.regs r).1]
      exact ⟨Nat.lt_of_lt_of_le (hI.regs r).1 hlen, (hI.regs r).2⟩
  · rw [hc]; exact hI.frame
  · rw [hc] at hc'
    obtain ⟨a, b, c', e, f⟩ := hI.cells c hc'
    exact ⟨a, b, c', Nat.lt_of_lt_of_le e hlen, by rw [stab e]; exact f⟩

/-- A register that gets the value of a node of the table. -/
theorem Inv.alias (hI : Inv p s₀ σ s) (d : XReg) {i : Nat} (hi : i < σ.n) {v : BitVec 128}
    (hv : val (envOf p s₀) σ.tab i = v) : Inv p s₀ (σ.alias d i) (s.setXmm d v) ∧ Ext σ (σ.alias d i) := by
  obtain ⟨n, tab, H, regs, cells⟩ := σ
  have i16 : i < 65536 := Nat.lt_of_lt_of_le hi hI.nle
  refine ⟨⟨?_, hI.len, hI.nle, hI.wf, hI.hok, fun r => ?_, hI.frame, hI.cells⟩, [], rfl⟩
  · obtain ⟨f, m, rfl⟩ := hI.same; exact ⟨_, _, rfl⟩
  · show rget (rset regs d i) r < n ∧ (if r = d then v else s.xmm r) = val _ tab (rget (rset regs d i) r)
    rw [rget_rset _ _ _ i16]
    by_cases e : r = d
    · rw [ite_eq_left e, ite_eq_left e]; exact ⟨hi, hv.symm⟩
    · rw [ite_eq_right e, ite_eq_right e]; exact hI.regs r

end

/-! ## The instructions' nodes -/

section
variable (E : Env) (v : Nat → BitVec 128) {a : Nat} (ha : a < 65536)
include ha

theorem evalK_bin (op : XBinOp) (b : Nat) : evalK E v (mk 6 op.ctorIdx a b) = op.eval (v a) (v b) := by
  rw [evalK_mk E v (by decide)]
  show (binOf _).eval (v _) (v _) = _
  rw [y_x (bin_lt op), y_a (bin_lt op) ha, y_b (bin_lt op) ha, binOf_idx]

theorem evalK_shift (op : XShiftOp) (n : BitVec 8) : evalK E v (mk 7 op.ctorIdx a n.toNat) = op.eval (v a) n := by
  rw [evalK_mk E v (by decide)]
  show (shiftOf _).eval (v _) (BitVec.ofNat 8 _) = _
  rw [y_x (shift_lt op), y_a (shift_lt op) ha, y_b (shift_lt op) ha, shiftOf_idx, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem evalK_pshufd (o : BitVec 8) : evalK E v (mk 8 o.toNat a 0) = shufDwords (v a) o := by
  rw [evalK_mk E v (by decide)]
  show shufDwords (v _) (BitVec.ofNat 8 _) = _
  rw [y_x o.isLt, y_a o.isLt ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem evalK_pshuflw (o : BitVec 8) : evalK E v (mk 9 o.toNat a 0) = shufLowWords (v a) o := by
  rw [evalK_mk E v (by decide)]
  show shufLowWords (v _) (BitVec.ofNat 8 _) = _
  rw [y_x o.isLt, y_a o.isLt ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem evalK_pshufhw (o : BitVec 8) : evalK E v (mk 10 o.toNat a 0) = shufHighWords (v a) o := by
  rw [evalK_mk E v (by decide)]
  show shufHighWords (v _) (BitVec.ofNat 8 _) = _
  rw [y_x o.isLt, y_a o.isLt ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem evalK_palignr (n : BitVec 8) (b : Nat) :
    evalK E v (mk 11 n.toNat a b) = alignRight (v a) (v b) n := by
  rw [evalK_mk E v (by decide)]
  show alignRight (v _) (v _) (BitVec.ofNat 8 _) = _
  rw [y_x n.isLt, y_a n.isLt ha, y_b n.isLt ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end

/-- The 16 bytes of a table an instruction loads, by their value. -/
theorem cst_eq (hi lo : BitVec 64) :
    BitVec.ofNat 128 (Nat.add (Nat.mul hi.toNat 18446744073709551616) lo.toNat) = hi ++ lo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_append_eq_mul_add]
  have h₁ := hi.isLt
  have h₂ := lo.isLt
  show (hi.toNat * 18446744073709551616 + lo.toNat) % 2 ^ 128 = hi.toNat * 2 ^ 64 + lo.toNat
  omega_using [h₁, h₂]

/-! ## Soundness -/

section
variable {p : Params} {s₀ s : State} {σ σ' : St}

/-- An instruction `step` follows runs, and leaves what the nodes say. -/
theorem step_ok (hp : Pre p s₀) {i : Instr} (hI : Inv p s₀ σ s) (hs : step p σ i = some σ') :
    ∃ s', exec i s = some s' ∧ Inv p s₀ σ' s' ∧ Ext σ σ' := by
  have hg := hI.gpr
  have hrd := hI.rd
  have hwr := hI.wr
  have hsy := hI.syms
  have mf := hp.mfit
  have kf := hp.kfit
  have hsh := hp.shi
  have lt16 : ∀ {j : Nat}, j < σ.n → j < 65536 := fun hj => Nat.lt_of_lt_of_le hj hI.nle
  -- what was not stored is what it was
  have apart : ∀ {o n : Nat}, o + n ≤ p.mlen → n ≤ 16 → (∀ c ∈ σ.cells, c.1 % 16 = 0 → o + n ≤ c.1 ∨ c.1 + 16 ≤ o) →
      ∀ r' ∈ σ.cells.map (cellR p s₀),
        Region.Disjoint ⟨(s₀.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 o, n⟩ r' := fun {o n} ho hn h r' hr' => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨c16, -, cshi, -, -⟩ := hI.cells c hc
    exact Offset.disjoint _ (h c hc c16) (by omega_using [mf, ho]) (by omega_using [mf, cshi, hsh])
  have keys : ∀ {o n : Nat}, o + n ≤ p.klen → ∀ r' ∈ σ.cells.map (cellR p s₀),
      Region.Disjoint ⟨(s₀.gpr p.kreg).setWidth 64, p.klen⟩ r' := fun {o n} _ r' hr' => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨-, cslo, cshi, -, -⟩ := hI.cells c hc
    exact hp.sep.sub_right (Offset.sub _ cslo (by omega_using [cslo, cshi]))
  unfold step at hs
  split at hs
  · -- a table's 16 bytes
    rename_i d m n ws
    split at hs <;> [rename_i hc; cases hs]
    obtain ⟨hb, hn, h8, hl⟩ := hc
    refine ⟨s.setXmm d (ws.getD (m.disp / 8 + 1) 0 ++ ws.getD (m.disp / 8) 0), ?_,
      hI.put hs (local_leaf (by decide) _ _) ?_⟩
    · show (if s.gpr m.base = s.syms n ∧ m.disp % 8 = 0 ∧ m.disp / 8 + 2 ≤ ws.length then _ else none) = _
      rw [ite_eq_left ⟨by rw [hb, hn, hg, hsy]; exact hp.tb, h8, hl⟩]
    · rw [evalK_leaf _ _ (by decide)]
      exact cst_eq _ _
  · -- a load of 16 bytes
    rename_i d m
    split at hs
    · rename_i hb
      split at hs <;> [rename_i hc; cases hs]
      obtain ⟨h16, hl⟩ := hc
      have ha : s.ea m = (s₀.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 m.disp := by
        show addr (s.gpr m.base) m.disp = _
        rw [hb, hg, addr_eq (by omega_using [mf, hl])]
      have hex : exec (.movdquLoad d m) s = some (s.setXmm d (s.mem.readW (s.ea m) 128)) := by
        show (s.load128 (s.ea m)).map _ = _
        rw [State.load128, ite_eq_left (by
          show InRegions _ (addr (s.gpr m.base) m.disp) 16
          rw [hb, hg, hrd, hwr]; exact hp.mrd _ _ hl)]
        rfl
      split at hs
      · rename_i i hi
        cases hs
        obtain ⟨-, -, -, hin, hval⟩ := hI.cells _ (lookup_some hi)
        exact ⟨_, hex, hI.alias d hin (by rw [ha]; exact hval.symm)⟩
      · rename_i hnone
        refine ⟨_, hex, hI.put hs (local_leaf (by decide) _ _) ?_⟩
        rw [evalK_leaf _ _ (by decide), ha]
        exact (hI.frame.readW (r := ⟨_, 16⟩) (Region.contains_self _ 16) (apart hl (Nat.le_refl _)
          fun c hc c16 => by have := lookup_none hnone c hc; omega_using [c16, h16, this]) (by decide)).symm
    · split at hs <;> [rename_i hc; cases hs]
      obtain ⟨hb, hl⟩ := hc
      have ha : s.ea m = (s₀.gpr p.kreg).setWidth 64 + BitVec.ofNat 64 m.disp := by
        show addr (s.gpr m.base) m.disp = _
        rw [hb, hg, addr_eq (by omega_using [kf, hl])]
      refine ⟨s.setXmm d (s.mem.readW (s.ea m) 128), ?_, hI.put hs (local_leaf (by decide) _ _) ?_⟩
      · show (s.load128 (s.ea m)).map _ = _
        rw [State.load128, ite_eq_left (by
          show InRegions _ (addr (s.gpr m.base) m.disp) 16
          rw [hb, hg, hrd, hwr]; exact hp.krd _ _ hl)]
        rfl
      · rw [evalK_leaf _ _ (by decide), ha]
        exact (hI.frame.readW (r := ⟨_, p.klen⟩) (Offset.contains_base _ hl (by omega_using [kf, hl])) (keys hl)
          (by decide)).symm
  · -- a load of 8 bytes
    rename_i d m
    split at hs
    · rename_i hb
      split at hs <;> [rename_i hc; cases hs]
      obtain ⟨h8, hl, hnone⟩ := hc
      have ha : s.ea m = (s₀.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 m.disp := by
        show addr (s.gpr m.base) m.disp = _
        rw [hb, hg, addr_eq (by omega_using [mf, hl])]
      refine ⟨s.setXmm d ((0 : BitVec 64) ++ s.mem.readW (s.ea m) 64), ?_,
        hI.put hs (local_leaf (by decide) _ _) ?_⟩
      · show (s.load64 (s.ea m)).map _ = _
        rw [State.load64, ite_eq_left (by
          show InRegions _ (addr (s.gpr m.base) m.disp) 8
          rw [hb, hg, hrd, hwr]; exact hp.mrd _ _ hl)]
        rfl
      · rw [evalK_leaf _ _ (by decide), ha]
        exact congrArg (fun x => (0 : BitVec 64) ++ x) (hI.frame.readW (r := ⟨_, 8⟩) (Region.contains_self _ 8)
          (apart hl (by decide) fun c hc c16 => by have := lookup_none hnone c hc; omega_using [c16, h8, this])
          (by decide)).symm
    · split at hs <;> [rename_i hc; cases hs]
      obtain ⟨hb, hl⟩ := hc
      have ha : s.ea m = (s₀.gpr p.kreg).setWidth 64 + BitVec.ofNat 64 m.disp := by
        show addr (s.gpr m.base) m.disp = _
        rw [hb, hg, addr_eq (by omega_using [kf, hl])]
      refine ⟨s.setXmm d ((0 : BitVec 64) ++ s.mem.readW (s.ea m) 64), ?_,
        hI.put hs (local_leaf (by decide) _ _) ?_⟩
      · show (s.load64 (s.ea m)).map _ = _
        rw [State.load64, ite_eq_left (by
          show InRegions _ (addr (s.gpr m.base) m.disp) 8
          rw [hb, hg, hrd, hwr]; exact hp.krd _ _ hl)]
        rfl
      · rw [evalK_leaf _ _ (by decide), ha]
        exact congrArg (fun x => (0 : BitVec 64) ++ x) (hI.frame.readW (r := ⟨_, p.klen⟩)
          (Offset.contains_base _ hl (by omega_using [kf, hl])) (keys hl) (by decide)).symm
  · -- a store
    rename_i m r
    split at hs <;> [rename_i hc; cases hs]
    obtain ⟨hb, h16, hlo, hhi⟩ := hc
    obtain ⟨n, tab, H, regs, cells⟩ := σ
    cases hs
    have ha : s.ea m = (s₀.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 m.disp := by
      show addr (s.gpr m.base) m.disp = _
      rw [hb, hg, addr_eq (by omega_using [mf, hhi, hsh])]
    have f1 : Frame [cellR p s₀ (m.disp, rget regs r)] s.mem (s.mem.writeW (s.ea m) (s.xmm r)) := by
      rw [ha]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
    refine ⟨{ s with mem := s.mem.writeW (s.ea m) (s.xmm r) }, ?_, ⟨?_, hI.len, hI.nle, hI.wf, hI.hok, hI.regs, ?_,
      fun c hc => ?_⟩, Ext.refl _⟩
    · show s.store128 (s.ea m) (s.xmm r) = _
      rw [State.store128, ite_eq_left (by
        show InRegions _ (addr (s.gpr m.base) m.disp) 16
        rw [hb, hg, hwr]; exact hp.mwr _ hlo hhi)]
    · obtain ⟨f, m', rfl⟩ := hI.same; exact ⟨_, _, rfl⟩
    · show Frame (cellR p s₀ (m.disp, rget regs r) :: _) s₀.mem (s.mem.writeW (s.ea m) (s.xmm r))
      rw [ha]
      refine (hI.frame.sub fun r' hr' => ?_).writeW List.mem_cons_self _ (Region.contains_self _ 16)
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr'
      by_cases e : c.1 = m.disp
      · exact ⟨_, List.mem_cons_self, by show Region.Sub ⟨_ + BitVec.ofNat 64 c.1, 16⟩ _; rw [e]; exact fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by
          show (!Nat.beq c.1 m.disp) = true
          cases hq : Nat.beq c.1 m.disp
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hq) e⟩, rfl⟩), fun _ h => h⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨h16, hlo, hhi, (hI.regs r).1, ?_⟩
        show (s.mem.writeW (s.ea m) (s.xmm r)).readW _ 128 = _
        rw [← ha, Mem.readW_writeW_self _ _ 16 _ (by decide)]
        exact (hI.regs r).2
      · obtain ⟨hc, hne⟩ := List.mem_filter.mp hc
        have hne : c.1 ≠ m.disp := by
          intro e; rw [e, Nat.beq_refl] at hne; cases hne
        obtain ⟨c16, cslo, cshi, cn, cv⟩ := hI.cells c hc
        refine ⟨c16, cslo, cshi, cn, ?_⟩
        show (s.mem.writeW (s.ea m) (s.xmm r)).readW _ 128 = _
        rw [f1.readW (r := ⟨_, 16⟩) (Region.contains_self _ 16) (fun r' hr' => by
          rw [List.mem_singleton.mp hr']
          exact Offset.disjoint _ (by omega_using [c16, h16, hne]) (by omega_using [mf, cshi, hsh])
            (by omega_using [mf, hhi, hsh])) (by decide)]
        exact cv
  · -- an instruction of two registers
    rename_i op d r
    cases hz : Nat.beq op.ctorIdx 0
    · rw [hz, Bool.cond_false] at hs
      have ha := (hI.regs d).1
      refine ⟨s.setXmm d (op.eval (s.xmm d) (s.xmm r)), rfl,
        hI.put hs (local_mk (by decide) (bin_lt op) (lt16 ha) ha (.inl (hI.regs r).1)) ?_⟩
      rw [evalK_bin _ _ (lt16 ha), ← (hI.regs d).2, ← (hI.regs r).2]
    · rw [hz, Bool.cond_true] at hs
      cases hs
      have e : op = .movdqa := by cases op <;> first | rfl | cases hz
      subst e
      exact ⟨s.setXmm d (s.xmm r), rfl, hI.alias d (hI.regs r).1 (hI.regs r).2.symm⟩
  · rename_i op d n
    have ha := (hI.regs d).1
    refine ⟨s.setXmm d (op.eval (s.xmm d) n), rfl,
      hI.put hs (local_mk (by decide) (shift_lt op) (lt16 ha) ha (.inr (.inl rfl))) ?_⟩
    rw [evalK_shift _ _ (lt16 ha), ← (hI.regs d).2]
  · rename_i d r o
    have ha := (hI.regs r).1
    refine ⟨s.setXmm d (shufDwords (s.xmm r) o), rfl,
      hI.put hs (local_mk (by decide) o.isLt (lt16 ha) ha (.inr (.inr (.inl rfl)))) ?_⟩
    rw [evalK_pshufd _ _ (lt16 ha), ← (hI.regs r).2]
  · rename_i d r o
    have ha := (hI.regs r).1
    refine ⟨s.setXmm d (shufLowWords (s.xmm r) o), rfl,
      hI.put hs (local_mk (by decide) o.isLt (lt16 ha) ha (.inr (.inr (.inr (.inl rfl))))) ?_⟩
    rw [evalK_pshuflw _ _ (lt16 ha), ← (hI.regs r).2]
  · rename_i d r o
    have ha := (hI.regs r).1
    refine ⟨s.setXmm d (shufHighWords (s.xmm r) o), rfl,
      hI.put hs (local_mk (by decide) o.isLt (lt16 ha) ha (.inr (.inr (.inr (.inr rfl))))) ?_⟩
    rw [evalK_pshufhw _ _ (lt16 ha), ← (hI.regs r).2]
  · rename_i d r n
    have ha := (hI.regs d).1
    refine ⟨s.setXmm d (alignRight (s.xmm d) (s.xmm r) n), rfl,
      hI.put hs (local_mk (by decide) n.isLt (lt16 ha) ha (.inl (hI.regs r).1)) ?_⟩
    rw [evalK_palignr _ _ (lt16 ha), ← (hI.regs d).2, ← (hI.regs r).2]
  · cases hs

/-- A block `run` follows runs, and leaves what the nodes say. -/
theorem run_ok (hp : Pre p s₀) : ∀ {is : List Instr} {σ σ' : St} {s : State}, Inv p s₀ σ s → run p σ is = some σ' →
    ∃ s', runBlock isa is s = some s' ∧ Inv p s₀ σ' s' ∧ Ext σ σ'
  | [], σ, σ', s, hI, h => by cases h; exact ⟨s, rfl, hI, Ext.refl _⟩
  | i :: is, σ, σ', s, hI, h => by
    unfold run at h
    split at h <;> [rename_i τ hτ; cases h]
    obtain ⟨s₁, he, hI₁, x₁⟩ := step_ok hp hI hτ
    obtain ⟨s', hr, hI', x'⟩ := run_ok hp hI₁ h
    exact ⟨s', by show (exec i s).bind (runBlock isa is) = _; rw [he]; exact hr, hI', x₁.trans x'⟩

end

theorem inv_init (p : Params) (s : State) : Inv p s St.init s := by
  refine ⟨⟨s.xmm, s.mem, rfl⟩, rfl, by decide, ?_, HOk.zero _, fun r => ?_, Frame.refl _ _, fun c hc => by cases hc⟩
  · exact ⟨local_leaf (by decide) _ _, local_leaf (by decide) _ _, local_leaf (by decide) _ _,
      local_leaf (by decide) _ _, local_leaf (by decide) _ _, local_leaf (by decide) _ _, local_leaf (by decide) _ _,
      local_leaf (by decide) _ _, trivial⟩
  · show rget rinit r < 8 ∧ s.xmm r = val (envOf p s) St.init.tab (rget rinit r)
    rw [rinit_get]
    exact ⟨ctorIdx_lt r, by cases r <;> rfl⟩

/-- From a state of `Pre p`, two blocks that `equiv` equates both run, to
states with the same memory and the same values in the registers `outs`
pairs; each is the state they start in but for the XMM registers and
memory. -/
theorem equiv_run {p : Params} {s : State} {P Q : List Instr} {outs : List (XReg × XReg)}
    (h : equiv p P Q outs = true) (hp : Pre p s) :
    ∃ sP sQ, runBlock isa P s = some sP ∧ runBlock isa Q s = some sQ ∧ sQ.mem = sP.mem ∧
      (∀ ab ∈ outs, sQ.xmm ab.2 = sP.xmm ab.1) ∧ (∃ f m, sP = { s with xmm := f, mem := m }) ∧
      ∃ f m, sQ = { s with xmm := f, mem := m } := by
  unfold equiv at h
  split at h <;> [cases h; rename_i σ hσ]
  split at h <;> [cases h; rename_i τ hτ]
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨ho, hc₁⟩, hc₂⟩ := h
  obtain ⟨sP, rP, iP, xP⟩ := run_ok hp (inv_init p s) hσ
  have i0 : Inv p s ⟨σ.n, σ.tab, σ.h, rinit, []⟩ s := by
    obtain ⟨l, hl⟩ := xP
    refine ⟨⟨s.xmm, s.mem, rfl⟩, iP.len, iP.nle, iP.wf, iP.hok, fun r => ?_, Frame.refl _ _,
      fun c hc => by cases hc⟩
    have h8 : rget rinit r < St.init.tab.length := by rw [rinit_get]; exact ctorIdx_lt r
    refine ⟨?_, ?_⟩
    · show rget rinit r < σ.n
      rw [iP.len, hl, List.length_append]; omega_using [h8]
    · show s.xmm r = val _ σ.tab (rget rinit r)
      rw [hl, val_append _ l h8]
      exact ((inv_init p s).regs r).2
  obtain ⟨sQ, rQ, iQ, xQ⟩ := run_ok hp i0 hτ
  have stab : ∀ {j : Nat}, j < σ.n → val (envOf p s) τ.tab j = val (envOf p s) σ.tab j := fun hj => by
    obtain ⟨l, hl⟩ := xQ
    rw [hl]; exact val_append _ l (by rw [← iP.len]; exact hj)
  refine ⟨sP, sQ, rP, rQ, ?_, fun ab hab => ?_, iP.same, iQ.same⟩
  · funext x
    by_cases hx : ∃ c ∈ σ.cells, (cellR p s c).Contains x 1
    · obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨-, -, -, cn, vP⟩ := iP.cells c hc
      obtain ⟨-, -, -, -, vQ⟩ := iQ.cells c (cellsLe_mem hc₁ hc)
      have e : sQ.mem.readW ((s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 c.1) 128 =
          sP.mem.readW ((s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 c.1) 128 := by rw [vQ, vP, stab cn]
      have hk : (x - ((s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 c.1)).toNat < 16 := by
        have : (x - ((s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 c.1)).toNat + 1 ≤ 16 := hcx
        omega_using [this]
      have hx' : x = (s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 c.1 +
          BitVec.ofNat 64 (x - ((s.gpr p.mreg).setWidth 64 + BitVec.ofNat 64 c.1)).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      rw [hx', ← byte_readW sQ.mem _ (w := 128) (by omega_using [hk]),
        ← byte_readW sP.mem _ (w := 128) (by omega_using [hk]), e]
    · have nP : ∀ r ∈ σ.cells.map (cellR p s), ¬ r.Contains x 1 := fun r hr hc => by
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hr
        exact hx ⟨c, hc', hc⟩
      have nQ : ∀ r ∈ τ.cells.map (cellR p s), ¬ r.Contains x 1 := fun r hr hc => by
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hr
        exact hx ⟨c, cellsLe_mem hc₂ hc', hc⟩
      rw [iQ.frame x nQ, iP.frame x nP]
  · have e := Nat.eq_of_beq_eq_true (List.all_eq_true.mp ho ab hab)
    rw [(iQ.regs ab.2).2, (iP.regs ab.1).2, ← e, stab (iP.regs ab.1).1]

/-- What holds of the state `P` ends in, and of every state with its memory
and its values in the registers `outs` pairs, holds of the state `Q` ends
in. -/
theorem equiv_wp {p : Params} {s : State} {P Q : List Instr} {outs : List (XReg × XReg)}
    (h : equiv p P Q outs = true) (hp : Pre p s) {R : State → Prop}
    (hP : WP isa (.block P) s fun sP => ∀ sQ : State, sQ.mem = sP.mem → (∀ ab ∈ outs, sQ.xmm ab.2 = sP.xmm ab.1) →
      (∃ f m, sQ = { s with xmm := f, mem := m }) → R sQ) : WP isa (.block Q) s R := by
  obtain ⟨sP, sQ, rP, rQ, hm, hx, -, hQ⟩ := equiv_run h hp
  obtain ⟨sP', rP', hR⟩ := Interleave.runBlock_of_WP hP
  rw [rP] at rP'
  cases rP'
  exact WP.of_runBlock ⟨sQ, rQ, hR sQ hm hx hQ⟩

end VG.X86.SseEquiv
