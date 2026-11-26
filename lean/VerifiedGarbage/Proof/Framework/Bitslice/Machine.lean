module

public import VerifiedGarbage.Proof.Framework.Bitslice.Dom
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Straight-line code over an abstract domain, for the kernel

Each ISA's evaluator of straight-line code (`Framework/<ISA>/Straight.lean`)
keeps the abstract values of the registers and slots as functions, which the
proofs about it read easily and the kernel does not: a function updated at
every write is followed again for every read, and what it holds is a term in
everything before it. `run` is an evaluator for the kernel to run:

* registers and slots are in a tree by the bits of their number (`Trie`), in
  which a read or a write is a few steps;
* what an instruction does is an `Op`, whose operations on values are closed
  terms, so that the kernel decodes an instruction it has met before by
  looking it up;
* every state is evaluated before the next instruction: the values by the
  operations (`seqN`), the trees by writing them in continuation-passing
  style (`Trie.set`);
* everything is a recursor or one of the operations on `Nat` that the kernel
  evaluates natively.

`run_sound` says that `run` is `eval`, on functions, which an ISA's evaluator
relates to its own.
-/

@[expose] public section

namespace VG.Bitslice.Machine

/-- `k n`, after evaluating `n`. What `k` is given is the term `n`, whose value
the kernel remembers, not the numeral: the kernel's hash of a numeral is of
its low 64 bits, so terms that hold different wide numerals are often one
bucket of its tables. -/
noncomputable def seqN {β : Type} (n : Nat) (k : Nat → β) : β :=
  Bool.rec (motive := fun _ => (Nat → β) → Nat → β) (fun k n => k n) (fun k n => k n) (Nat.beq n 0) k n

theorem seqN_eq {β : Type} (n : Nat) (k : Nat → β) : seqN n k = k n := by
  unfold seqN; cases Nat.beq n 0 <;> rfl

theorem bool_rec_ble {β : Type} (x y : β) (m n : Nat) :
    Bool.rec (motive := fun _ => β) x y (Nat.ble m n) = if m ≤ n then y else x := by
  by_cases h : m ≤ n
  · rw [Nat.ble_eq.mpr h, ite_eq_left h]
  · rw [show Nat.ble m n = false from Bool.eq_false_iff.mpr fun hb => h (Nat.ble_eq.mp hb),
      ite_eq_right h]

theorem bool_rec_beq {β : Type} (x y : β) (m n : Nat) :
    Bool.rec (motive := fun _ => β) x y (Nat.beq m n) = if m = n then y else x := by
  by_cases h : m = n
  · rw [Nat.beq_eq.mpr h, ite_eq_left h]
  · rw [show Nat.beq m n = false from Bool.eq_false_iff.mpr fun hb => h (Nat.beq_eq.mp hb),
      ite_eq_right h]

/-- An equality test that the kernel evaluates. -/
class KEq (α : Type) where
  eq : α → α → Bool
  eq_iff : ∀ {a b : α}, eq a b = true ↔ a = b

instance (priority := low) {α : Type} [DecidableEq α] : KEq α := ⟨fun a b => decide (a = b), decide_eq_true_iff⟩

noncomputable instance : KEq (Nat × Nat) where
  eq a b := Bool.rec false (Nat.beq a.2 b.2) (Nat.beq a.1 b.1)
  eq_iff {a b} := by
    rw [bool_rec_beq]
    by_cases h : a.1 = b.1
    · rw [ite_eq_left h, Nat.beq_eq]; exact ⟨Prod.ext h, fun e => e ▸ rfl⟩
    · rw [ite_eq_right h]; exact ⟨fun e => absurd e Bool.false_ne_true, fun e => absurd (congrArg Prod.fst e) h⟩

/-- `some n`, with `n` evaluated. -/
noncomputable def seqSome (n : Nat) : Option Nat := seqN n some

theorem seqSome_eq (n : Nat) : seqSome n = some n := seqN_eq n some

/-- The registers' numbers. -/
class Idx (R : Type) where
  ix : R → Nat
  ix_inj : ∀ {a b : R}, ix a = ix b → a = b

theorem bool_rec_idx {R : Type} [Idx R] [DecidableEq R] {β : Type} (x y : β) (a b : R) :
    Bool.rec (motive := fun _ => β) x y (Nat.beq (Idx.ix a) (Idx.ix b)) = if a = b then y else x := by
  rw [bool_rec_beq]
  by_cases h : a = b
  · rw [ite_eq_left (congrArg Idx.ix h), ite_eq_left h]
  · rw [ite_eq_right (fun e => h (Idx.ix_inj e)), ite_eq_right h]

/-- Values at natural numbers, in a tree by their bits, lowest first. -/
inductive Trie (V : Type) where
  | leaf (v : Option V)
  | node (l r : Trie V)

namespace Trie
variable {V : Type}

/-- Nothing at the numbers below `2 ^ d`. -/
noncomputable def empty (d : Nat) : Trie V :=
  Nat.rec (motive := fun _ => Trie V) (leaf none) (fun _ t => node t t) d

noncomputable def get (t : Trie V) : Nat → Option V :=
  Trie.rec (motive := fun _ => Nat → Option V) (fun v k => Bool.rec none v (Nat.beq k 0))
    (fun _ _ gl gr k =>
      Bool.rec (gr (Nat.div k 2)) (gl (Nat.div k 2)) (Nat.beq (Nat.mod k 2) 0)) t

/-- `c` of the tree with `v` at `k`; `false` if the tree has no place for `k`. -/
noncomputable def set (t : Trie V) (k : Nat) (v : V) (c : Trie V → Bool) : Bool :=
  Trie.rec (motive := fun _ => Nat → (Trie V → Bool) → Bool)
    (fun _ k c => Bool.rec false (c (leaf (some v))) (Nat.beq k 0))
    (fun l r sl sr k c =>
      Bool.rec (sr (Nat.div k 2) fun r => c (node l r)) (sl (Nat.div k 2) fun l => c (node l r))
        (Nat.beq (Nat.mod k 2) 0)) t k c

theorem get_leaf (v : Option V) (k : Nat) : (leaf v).get k = if k = 0 then v else none :=
  bool_rec_beq none v k 0

theorem get_node (l r : Trie V) (k : Nat) :
    (node l r).get k = if k % 2 = 0 then l.get (k / 2) else r.get (k / 2) :=
  bool_rec_beq (r.get (k / 2)) (l.get (k / 2)) (k % 2) 0

theorem get_empty (d k : Nat) : (empty d : Trie V).get k = none := by
  induction d generalizing k with
  | zero => exact (get_leaf none k).trans (by split <;> rfl)
  | succ d ih => exact (get_node (empty d) (empty d) k).trans (by rw [ih]; split <;> rfl)

theorem set_leaf (u : Option V) (k : Nat) (v : V) (c : Trie V → Bool) :
    (leaf u).set k v c = if k = 0 then c (leaf (some v)) else false :=
  bool_rec_beq false (c (leaf (some v))) k 0

theorem set_node (l r : Trie V) (k : Nat) (v : V) (c : Trie V → Bool) :
    (node l r).set k v c = if k % 2 = 0 then l.set (k / 2) v fun l => c (node l r)
      else r.set (k / 2) v fun r => c (node l r) :=
  bool_rec_beq (r.set (k / 2) v fun r => c (node l r)) (l.set (k / 2) v fun l => c (node l r)) (k % 2) 0

theorem set_true {t : Trie V} {k : Nat} {v : V} {c : Trie V → Bool} (h : t.set k v c = true) :
    ∃ t', c t' = true ∧ ∀ j, t'.get j = if j = k then some v else t.get j := by
  induction t generalizing k c with
  | leaf u =>
    rw [set_leaf] at h
    by_cases hk : k = 0
    · rw [ite_eq_left hk] at h
      exact ⟨leaf (some v), h, fun j => by rw [get_leaf, get_leaf, hk]; split <;> rfl⟩
    · rw [ite_eq_right hk] at h; cases h
  | node l r ihl ihr =>
    rw [set_node] at h
    by_cases hk : k % 2 = 0
    · rw [ite_eq_left hk] at h
      obtain ⟨l', hc, hl⟩ := ihl h
      refine ⟨node l' r, hc, fun j => ?_⟩
      rw [get_node, get_node, hl]
      by_cases hj : j = k
      · subst hj; rw [ite_eq_left hk, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hj]
        by_cases hj2 : j % 2 = 0
        · rw [ite_eq_left hj2, ite_eq_left hj2,
            ite_eq_right (show ¬ j / 2 = k / 2 by omega_using [hk, hj, hj2])]
        · rw [ite_eq_right hj2, ite_eq_right hj2]
    · rw [ite_eq_right hk] at h
      obtain ⟨r', hc, hr⟩ := ihr h
      refine ⟨node l r', hc, fun j => ?_⟩
      rw [get_node, get_node, hr]
      by_cases hj : j = k
      · subst hj; rw [ite_eq_right hk, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hj]
        by_cases hj2 : j % 2 = 0
        · rw [ite_eq_left hj2, ite_eq_left hj2]
        · rw [ite_eq_right hj2, ite_eq_right hj2,
            ite_eq_right (show ¬ j / 2 = k / 2 by omega_using [hk, hj, hj2])]

end Trie

/-- What an instruction does, on register values `V` and slot values `S`. -/
inductive Op (R V S : Type) where
  /-- Not supported. -/
  | bad
  | r0 (v : Option V) (d : R)
  | r1 (f : V → Option V) (d n : R)
  | r2 (f : V → V → Option V) (d n m : R)
  /-- From a slot. -/
  | ld (f : S → Option V) (d : R) (k : Nat)
  /-- From a register and a slot. -/
  | rs (f : V → S → Option V) (d n : R) (k : Nat)
  /-- Into a slot. -/
  | st (f : V → Option S) (k : Nat) (n : R)

/-! ## Guards -/

namespace Op
variable {R V S : Type} [Idx R]

/-- `t`, if `a ≠ b`. -/
noncomputable def ne (a b : R) (t : Op R V S) : Op R V S :=
  Bool.rec t .bad (Nat.beq (Idx.ix a) (Idx.ix b))

/-- `t`, if `m < n`. -/
noncomputable def lt (m n : Nat) (t : Op R V S) : Op R V S := Bool.rec .bad t (Nat.ble (Nat.succ m) n)

/-- `t`, if `m = n`. -/
noncomputable def eq (m n : Nat) (t : Op R V S) : Op R V S := Bool.rec .bad t (Nat.beq m n)

/-- What an access of word `k` at register `n` does: `slot k` if `n` is
`base` and `k < slots`, or else `ext k` if `n` is the register `x` and
`k < exts`. -/
noncomputable def area {K : Type} [Idx K] (n base : K) (slots : Nat) (x : K) (exts k : Nat)
    (slot ext : Nat → Op R V S) : Op R V S :=
  Bool.rec (Bool.rec .bad (lt k exts (ext k)) (Nat.beq (Idx.ix n) (Idx.ix x)))
    (Bool.rec (Bool.rec .bad (lt k exts (ext k)) (Nat.beq (Idx.ix n) (Idx.ix x))) (slot k)
      (Nat.ble (Nat.succ k) slots))
    (Nat.beq (Idx.ix n) (Idx.ix base))

/-- `t`, if `d` is neither of the base registers. -/
noncomputable def dst (b x d : R) (t : Op R V S) : Op R V S := ne d b (ne d x t)

variable [DecidableEq R]

theorem ne_eq (a b : R) (t : Op R V S) : ne a b t = if a = b then .bad else t := bool_rec_idx ..

omit [Idx R] [DecidableEq R] in
theorem lt_eq (m n : Nat) (t : Op R V S) : lt m n t = if m < n then t else .bad := bool_rec_ble ..

omit [Idx R] [DecidableEq R] in
theorem eq_eq (m n : Nat) (t : Op R V S) : eq m n t = if m = n then t else .bad := bool_rec_beq ..

omit [Idx R] [DecidableEq R] in
theorem area_eq {K : Type} [Idx K] [DecidableEq K] (n base : K) (slots : Nat) (x : K) (exts k : Nat)
    (slot ext : Nat → Op R V S) :
    area n base slots x exts k slot ext =
      if n = base ∧ k < slots then slot k else if n = x ∧ k < exts then ext k else .bad := by
  have e : Bool.rec (motive := fun _ => Op R V S) .bad (lt k exts (ext k))
      (Nat.beq (Idx.ix n) (Idx.ix x)) = if n = x ∧ k < exts then ext k else .bad := by
    rw [bool_rec_idx, lt_eq]
    by_cases h : n = x <;> by_cases h' : k < exts <;> simp only [h, h', and_self, and_false, false_and, ite_true, ite_false]
  rw [area, e, bool_rec_idx, bool_rec_ble]
  generalize (if n = x ∧ k < exts then ext k else .bad : Op R V S) = E
  by_cases h : n = base <;> by_cases h' : Nat.succ k ≤ slots
  · rw [ite_eq_left h, ite_eq_left h', ite_eq_left ⟨h, h'⟩]
  · rw [ite_eq_left h, ite_eq_right h', ite_eq_right (fun h => h' h.2)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]

end Op

variable {I R V S : Type} [Idx R]

/-- The values of the registers and slots, as functions. -/
structure Env (R V S : Type) where
  reg : R → Option V
  slot : Nat → Option S

def Env.setReg (e : Env R V S) (d : R) (v : V) : Env R V S :=
  { e with reg := fun r => if Idx.ix r = Idx.ix d then some v else e.reg r }

def Env.setSlot (e : Env R V S) (k : Nat) (v : S) : Env R V S :=
  { e with slot := fun j => if j = k then some v else e.slot j }

def step (e : Env R V S) : Op R V S → Option (Env R V S)
  | .bad => none
  | .r0 v d => v.map (e.setReg d)
  | .r1 f d n => ((e.reg n).bind f).map (e.setReg d)
  | .r2 f d n m => ((e.reg n).bind fun x => (e.reg m).bind (f x)).map (e.setReg d)
  | .ld f d k => ((e.slot k).bind f).map (e.setReg d)
  | .rs f d n k => ((e.reg n).bind fun x => (e.slot k).bind (f x)).map (e.setReg d)
  | .st f k n => ((e.reg n).bind f).map (e.setSlot k)

def eval (dec : I → Op R V S) : List I → Env R V S → Option (Env R V S)
  | [], e => some e
  | i :: is, e => (step e (dec i)).bind (eval dec is)

/-! ## The kernel's evaluator -/

section
variable (e₀ : Env R V S)

/-- The value of register `r`: the one in the tree, or the initial one. -/
noncomputable def reg (rs : Trie V) (r : R) : Option V :=
  Option.rec (e₀.reg r) (fun v => some v) (rs.get (Idx.ix r))

noncomputable def slot (ss : Trie S) (k : Nat) : Option S :=
  Option.rec (e₀.slot k) (fun v => some v) (ss.get k)

abbrev Next (V S : Type) := Trie V → Trie S → Bool

/-- The next instructions. A definition that the kernel unfolds, so that it
goes from instruction to instruction in its loop, and not by recursion. -/
noncomputable def next (c : Next V S) (rs : Trie V) (ss : Trie S) : Bool := c rs ss

noncomputable def setReg (d : R) (v : Option V) (rs : Trie V) (ss : Trie S) (c : Next V S) : Bool :=
  Option.rec false (fun v => rs.set (Idx.ix d) v fun rs => next c rs ss) v

noncomputable def setSlot (k : Nat) (v : Option S) (rs : Trie V) (ss : Trie S) (c : Next V S) : Bool :=
  Option.rec false (fun v => ss.set k v fun ss => next c rs ss) v

noncomputable def bind {α β : Type} (f : α → Option β) (x : Option α) : Option β :=
  Option.rec none f x

noncomputable def bind2 {α β γ : Type} (f : α → β → Option γ) (x : Option α) (y : Option β) : Option γ :=
  Option.rec none (fun a => Option.rec none (f a) y) x

/-- One instruction, then `c`. -/
noncomputable def stepK (o : Op R V S) : Trie V → Trie S → Next V S → Bool :=
  Op.rec (motive := fun _ => Trie V → Trie S → Next V S → Bool)
    (fun _ _ _ => false)
    (fun v d rs ss c => setReg d v rs ss c)
    (fun f d n rs ss c => setReg d (bind f (reg e₀ rs n)) rs ss c)
    (fun f d n m rs ss c => setReg d (bind2 f (reg e₀ rs n) (reg e₀ rs m)) rs ss c)
    (fun f d k rs ss c => setReg d (bind f (slot e₀ ss k)) rs ss c)
    (fun f d n k rs ss c => setReg d (bind2 f (reg e₀ rs n) (slot e₀ ss k)) rs ss c)
    (fun f k n rs ss c => setSlot k (bind f (reg e₀ rs n)) rs ss c) o

/-- The functions that the trees stand for. -/
noncomputable def env (rs : Trie V) (ss : Trie S) : Env R V S := ⟨reg e₀ rs, slot e₀ ss⟩

noncomputable def runK (dec : I → Op R V S) (post : Env R V S → Bool) (is : List I) : Next V S :=
  List.rec (motive := fun _ => Next V S) (fun rs ss => post (env e₀ rs ss))
    (fun i _ c rs ss => stepK e₀ (dec i) rs ss c) is

/-- Runs the code and checks `post` of what it leaves, with room for
`2 ^ kr` registers and `2 ^ ks` slots. -/
noncomputable def run (kr ks : Nat) (dec : I → Op R V S) (post : Env R V S → Bool) (is : List I) : Bool :=
  runK e₀ dec post is (Trie.empty kr) (Trie.empty ks)

variable {e₀}

/-- `x`, if `b`. -/
noncomputable def guard {α : Type} (b : Bool) (x : Option α) : Option α := Bool.rec none x b

theorem guard_eq {α : Type} (b : Bool) (x : Option α) : guard b x = if b = true then x else none := by
  cases b <;> rfl

theorem bind_eq {α β : Type} (f : α → Option β) (x : Option α) : bind f x = x.bind f := by
  cases x <;> rfl

theorem bind2_eq {α β γ : Type} (f : α → β → Option γ) (x : Option α) (y : Option β) :
    bind2 f x y = x.bind fun a => y.bind (f a) := by
  cases x <;> cases y <;> rfl

theorem setReg_true {d : R} {v : Option V} {rs : Trie V} {ss : Trie S} {c : Next V S}
    (h : setReg d v rs ss c = true) :
    ∃ rs', c rs' ss = true ∧ v.map ((env e₀ rs ss).setReg d) = some (env e₀ rs' ss) := by
  cases v with
  | none => cases h
  | some v =>
    obtain ⟨rs', hc, hg⟩ := Trie.set_true (c := fun rs => next c rs ss) h
    refine ⟨rs', hc, congrArg some ?_⟩
    refine congrArg (fun f => (⟨f, _⟩ : Env R V S)) ?_
    funext r
    show _ = reg e₀ rs' r
    rw [reg, hg]
    split <;> rfl

theorem setSlot_true {k : Nat} {v : Option S} {rs : Trie V} {ss : Trie S} {c : Next V S}
    (h : setSlot k v rs ss c = true) :
    ∃ ss', c rs ss' = true ∧ v.map ((env e₀ rs ss).setSlot k) = some (env e₀ rs ss') := by
  cases v with
  | none => cases h
  | some v =>
    obtain ⟨ss', hc, hg⟩ := Trie.set_true (c := fun ss => next c rs ss) h
    refine ⟨ss', hc, congrArg some ?_⟩
    refine congrArg (fun f => (⟨_, f⟩ : Env R V S)) ?_
    funext j
    show _ = slot e₀ ss' j
    rw [slot, hg]
    split <;> rfl

theorem stepK_true {o : Op R V S} {rs : Trie V} {ss : Trie S} {c : Next V S}
    (h : stepK e₀ o rs ss c = true) :
    ∃ rs' ss', c rs' ss' = true ∧ step (env e₀ rs ss) o = some (env e₀ rs' ss') := by
  cases o with
  | bad => cases h
  | st f k n =>
    obtain ⟨ss', hc, he⟩ := setSlot_true (e₀ := e₀) (k := k) (v := bind f (reg e₀ rs n)) h
    exact ⟨rs, ss', hc, by rw [bind_eq] at he; exact he⟩
  | r0 v d =>
    obtain ⟨rs', hc, he⟩ := setReg_true (e₀ := e₀) (d := d) (v := v) h
    exact ⟨rs', ss, hc, he⟩
  | r1 f d n =>
    obtain ⟨rs', hc, he⟩ := setReg_true (e₀ := e₀) (d := d) (v := bind f (reg e₀ rs n)) h
    exact ⟨rs', ss, hc, by rw [bind_eq] at he; exact he⟩
  | r2 f d n m =>
    obtain ⟨rs', hc, he⟩ :=
      setReg_true (e₀ := e₀) (d := d) (v := bind2 f (reg e₀ rs n) (reg e₀ rs m)) h
    exact ⟨rs', ss, hc, by rw [bind2_eq] at he; exact he⟩
  | ld f d k =>
    obtain ⟨rs', hc, he⟩ := setReg_true (e₀ := e₀) (d := d) (v := bind f (slot e₀ ss k)) h
    exact ⟨rs', ss, hc, by rw [bind_eq] at he; exact he⟩
  | rs f d n k =>
    obtain ⟨rs', hc, he⟩ :=
      setReg_true (e₀ := e₀) (d := d) (v := bind2 f (reg e₀ rs n) (slot e₀ ss k)) h
    exact ⟨rs', ss, hc, by rw [bind2_eq] at he; exact he⟩

theorem runK_true {dec : I → Op R V S} {post : Env R V S → Bool} {is : List I} {rs : Trie V}
    {ss : Trie S} (h : runK e₀ dec post is rs ss = true) :
    ∃ e', eval dec is (env e₀ rs ss) = some e' ∧ post e' = true := by
  induction is generalizing rs ss with
  | nil => exact ⟨_, rfl, h⟩
  | cons i is ih =>
    obtain ⟨rs', ss', hc, he⟩ := stepK_true (o := dec i) (c := runK e₀ dec post is) h
    obtain ⟨e', hv, hp⟩ := ih hc
    exact ⟨e', by rw [eval, he]; exact hv, hp⟩

theorem env_empty (kr ks : Nat) : env e₀ (Trie.empty kr) (Trie.empty ks) = e₀ := by
  cases e₀ with
  | mk r s =>
    refine congr (congrArg Env.mk ?_) ?_ <;> funext j
    · show reg _ (Trie.empty kr) j = _; rw [reg, Trie.get_empty]
    · show slot _ (Trie.empty ks) j = _; rw [slot, Trie.get_empty]

/-! ## Inversion -/

section
variable {e m : Env R V S} {t : Op R V S}

theorem step_ne [DecidableEq R] {a b : R} (h : step e (.ne a b t) = some m) : a ≠ b ∧ step e t = some m := by
  rw [Op.ne_eq] at h
  split at h
  · cases h
  · exact ⟨by assumption, h⟩

theorem step_lt {a b : Nat} (h : step e (.lt a b t) = some m) : a < b ∧ step e t = some m := by
  rw [Op.lt_eq] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem step_eq {a b : Nat} (h : step e (.eq a b t) = some m) : a = b ∧ step e t = some m := by
  rw [Op.eq_eq] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem step_dst [DecidableEq R] {b x d : R} (h : step e (.dst b x d t) = some m) :
    ¬ (d = b ∨ d = x) ∧ step e t = some m := by
  obtain ⟨h1, h⟩ := step_ne h
  obtain ⟨h2, h⟩ := step_ne h
  exact ⟨fun h => h.elim h1 h2, h⟩

omit [Idx R] in
theorem not_dst {b x d : R} {p : Prop} (h : ¬ (d = b ∨ d = x)) (hp : p) :
    ¬ (d = b ∨ d = x ∨ ¬ p) := fun h' => h'.elim (fun e => h (.inl e))
  fun e => e.elim (fun e => h (.inr e)) fun e => e hp

end

theorem run_sound {kr ks : Nat} {dec : I → Op R V S} {post : Env R V S → Bool} {is : List I}
    (h : run e₀ kr ks dec post is = true) :
    ∃ e', eval dec is e₀ = some e' ∧ post e' = true := by
  have := runK_true h
  rwa [env_empty] at this

theorem runK_mono {dec : I → Op R V S} {p q : Env R V S → Bool} (hpq : ∀ e, p e = true → q e = true)
    {is : List I} {rs : Trie V} {ss : Trie S} (h : runK e₀ dec p is rs ss = true) :
    runK e₀ dec q is rs ss = true := by
  have set_mono : ∀ {W : Type} {t : Trie W} {k : Nat} {v : W} {c c' : Trie W → Bool},
      (∀ t, c t = true → c' t = true) → t.set k v c = true → t.set k v c' = true := by
    intro W t k v c c' hc h
    induction t generalizing k c c' with
    | leaf u =>
      rw [Trie.set_leaf] at h ⊢
      split at h
      · rw [ite_eq_left (by assumption)]; exact hc _ h
      · cases h
    | node l r ihl ihr =>
      rw [Trie.set_node] at h ⊢
      split at h
      · rw [ite_eq_left (by assumption)]; exact ihl (fun _ => hc _) h
      · rw [ite_eq_right (by assumption)]; exact ihr (fun _ => hc _) h
  induction is generalizing rs ss with
  | nil => exact hpq _ h
  | cons i is ih =>
    have hr {d : R} {v : Option V} (h : setReg d v rs ss (runK e₀ dec p is) = true) :
        setReg d v rs ss (runK e₀ dec q is) = true := by
      cases v with
      | none => cases h
      | some v => exact set_mono (fun _ h => ih h) h
    have hs {k : Nat} {v : Option S} (h : setSlot k v rs ss (runK e₀ dec p is) = true) :
        setSlot k v rs ss (runK e₀ dec q is) = true := by
      cases v with
      | none => cases h
      | some v => exact set_mono (fun _ h => ih h) h
    change stepK e₀ (dec i) rs ss _ = true at h
    show stepK e₀ (dec i) rs ss _ = true
    cases hd : dec i with
    | bad => rw [hd] at h; cases h
    | st => rw [hd] at h; exact hs h
    | _ => rw [hd] at h; exact hr h

theorem run_mono {kr ks : Nat} {dec : I → Op R V S} {p q : Env R V S → Bool} {is : List I}
    (hpq : ∀ e, p e = true → q e = true) (h : run e₀ kr ks dec p is = true) :
    run e₀ kr ks dec q is = true := runK_mono hpq h

end

/-! ## Registers that may hold a known constant -/

/-- What a register holds: its abstract value, and its concrete one, if known. -/
structure Ent (α : Type) where
  val : Option α
  cst : Option Nat

section
variable {α : Type} {w : Nat}

/-- An abstract value, with no known concrete one. -/
noncomputable def valK (a : Option α) : Option (Ent α) := Option.rec none (fun a => some ⟨some a, none⟩) a

/-- A known constant. -/
noncomputable def cstK (D : Dom α w) (v : Nat) : Option (Ent α) :=
  seqN v fun v => Option.rec (some ⟨none, some v⟩) (fun a => some ⟨some a, some v⟩)
    (D.const (BitVec.ofNat w v))

noncomputable def val1 (f : α → Option α) (x : Ent α) : Option (Ent α) :=
  Option.rec none (fun a => valK (f a)) x.val

noncomputable def val2 (f : α → α → Option α) (x y : Ent α) : Option (Ent α) :=
  Option.rec none (fun a => Option.rec none (fun b => valK (f a b)) y.val) x.val

noncomputable def cst1 (D : Dom α w) (f : Nat → Nat) (x : Ent α) : Option (Ent α) :=
  Option.rec none (fun v => cstK D (f v)) x.cst

noncomputable def cst2 (D : Dom α w) (f : Nat → Nat → Nat) (x y : Ent α) : Option (Ent α) :=
  Option.rec none (fun u => Option.rec none (fun v => cstK D (f u v)) y.cst) x.cst

/-- The value, known if it was. -/
noncomputable def mov1 (D : Dom α w) (x : Ent α) : Option (Ent α) :=
  Option.rec (valK x.val) (fun v => cstK D v) x.cst

theorem valK_eq (a : Option α) : valK a = a.map fun a => ⟨some a, none⟩ := by cases a <;> rfl

theorem cstK_eq (D : Dom α w) (v : BitVec w) : cstK D v.toNat = some ⟨D.const v, some v.toNat⟩ := by
  rw [cstK, seqN_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  cases D.const v <;> rfl

end

end VG.Bitslice.Machine
