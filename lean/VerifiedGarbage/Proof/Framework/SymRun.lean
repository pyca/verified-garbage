module

public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Symbolic execution of straight-line code over terms, for the kernel

A symbolic run of straight-line code (vector code whose registers hold terms in
what they held before) that keeps the registers' terms as a function, updated at
every write, has the kernel follow every write again at every read. `run` keeps
them in a tree by the bits of the register's number (`Tree`), evaluated at every
write; an instruction is an `Act`, which the kernel finds again for an
instruction it has met. `run_sound` says that `run` is the run on functions
(`exec`), which each machine's own run is (`runs`). What `run` ends in is
compared with what it should be by the kernel's own comparison (`Eq.refl`), not
by a `DecidableEq`: the terms share most of their subterms, and the kernel
compares two terms once.
-/

@[expose] public section

namespace VG.SymRun

variable {I T S : Type}

/-- What an instruction does, to the registers' terms and the rest of the state:
registers by their numbers, the one it writes first. -/
inductive Act (T S : Type) where
  | bad
  | r0 (d : Nat) (f : S → Option T)
  | r1 (d n : Nat) (f : S → T → Option T)
  | r2 (d n m : Nat) (f : S → T → T → Option T)
  | r3 (d n m l : Nat) (f : S → T → T → T → Option T)
  /-- The rest of the state. -/
  | s0 (f : S → Option S)
  | s1 (n : Nat) (f : S → T → Option S)

/-- The registers `g`, with `v` in `d`. -/
def upd (g : Nat → T) (d : Nat) (v : T) : Nat → T := fun r => bif Nat.beq r d then v else g r

/-- `Act` on functions. -/
def Act.app (a : Act T S) (g : Nat → T) (s : S) : Option ((Nat → T) × S) :=
  match a with
  | .bad => none
  | .r0 d f => (f s).map fun v => (upd g d v, s)
  | .r1 d n f => (f s (g n)).map fun v => (upd g d v, s)
  | .r2 d n m f => (f s (g n) (g m)).map fun v => (upd g d v, s)
  | .r3 d n m l f => (f s (g n) (g m) (g l)).map fun v => (upd g d v, s)
  | .s0 f => (f s).map fun s => (g, s)
  | .s1 n f => (f s (g n)).map fun s => (g, s)

/-- The run of a block on functions. -/
def exec (act : I → Act T S) : List I → (Nat → T) → S → Option ((Nat → T) × S)
  | [], g, s => some (g, s)
  | i :: is, g, s => ((act i).app g s).bind fun p => exec act is p.1 p.2

/-- A run of a machine's own, whose step is `act`'s. -/
theorem runs {σ : Type} {act : I → Act T S} {step : σ → I → Option σ} {run : σ → List I → Option σ}
    (mk : (Nat → T) → S → σ) (hs : ∀ g s i, step (mk g s) i = ((act i).app g s).map fun p => mk p.1 p.2)
    (h0 : ∀ a, run a [] = some a) (h1 : ∀ a i is, run a (i :: is) = (step a i).bind fun b => run b is) :
    ∀ (is : List I) (g : Nat → T) (s : S), run (mk g s) is = (exec act is g s).map fun p => mk p.1 p.2
  | [], g, s => h0 _
  | i :: is, g, s => by
    rw [h1, hs, exec]
    cases (act i).app g s with
    | none => rfl
    | some p => exact runs mk hs h0 h1 is p.1 p.2

/-! ## For the kernel -/

/-- Values at the numbers below a power of two, in a tree by their bits, lowest first. -/
inductive Tree (T : Type) where
  | leaf (v : T)
  | node (l r : Tree T)

namespace Tree

/-- `c` of the value at `k`. -/
noncomputable def get {β : Type} (t : Tree T) : Nat → (T → β) → β :=
  Tree.rec (motive := fun _ => Nat → (T → β) → β) (fun v _ c => c v)
    (fun _ _ gl gr k c => Bool.rec (gr (Nat.div k 2) c) (gl (Nat.div k 2) c) (Nat.beq (Nat.mod k 2) 0)) t

/-- `c` of the tree with `v` at `k`. -/
noncomputable def set {β : Type} (t : Tree T) : Nat → T → (Tree T → β) → β :=
  Tree.rec (motive := fun _ => Nat → T → (Tree T → β) → β) (fun _ _ v c => c (leaf v))
    (fun l r sl sr k v c => Bool.rec (sr (Nat.div k 2) v fun r => c (node l r))
      (sl (Nat.div k 2) v fun l => c (node l r)) (Nat.beq (Nat.mod k 2) 0)) t

/-- The tree of `f` at the numbers below `2 ^ d`. -/
noncomputable def ofFn (d : Nat) (f : Nat → T) : Tree T :=
  Nat.rec (motive := fun _ => (Nat → T) → Tree T) (fun f => leaf (f 0))
    (fun _ ih f => node (ih fun k => f (Nat.mul 2 k)) (ih fun k => f (Nat.succ (Nat.mul 2 k)))) d f

/-- A tree of `d` levels, holding `g`. -/
def Holds : Nat → Tree T → (Nat → T) → Prop
  | 0, leaf v, g => v = g 0
  | d + 1, node l r, g => Holds d l (fun k => g (2 * k)) ∧ Holds d r fun k => g (2 * k + 1)
  | _, _, _ => False

theorem holds_ofFn : ∀ (d : Nat) (f : Nat → T), Holds d (ofFn d f) f
  | 0, _ => rfl
  | d + 1, _ => ⟨holds_ofFn d _, holds_ofFn d _⟩

theorem rec_beq {β : Type} (x y : β) (m n : Nat) :
    Bool.rec (motive := fun _ => β) x y (Nat.beq m n) = if m = n then y else x := by
  by_cases h : m = n
  · rw [Nat.beq_eq.mpr h, ite_eq_left h]
  · rw [show Nat.beq m n = false from Bool.eq_false_iff.mpr fun hb => h (Nat.beq_eq.mp hb), ite_eq_right h]

theorem get_eq {β : Type} : ∀ (d : Nat) {t : Tree T} {g : Nat → T}, Holds d t g → ∀ {k : Nat}, k < 2 ^ d →
    ∀ c : T → β, t.get k c = c (g k)
  | 0, leaf v, g, h, k, hk, c => by
    obtain rfl : k = 0 := by omega_using [hk]
    exact congrArg c h
  | d + 1, node l r, g, h, k, hk, c => by
    refine (rec_beq (r.get (k / 2) c) (l.get (k / 2) c) (k % 2) 0).trans ?_
    have h2 : k / 2 < 2 ^ d := by rw [Nat.pow_succ] at hk; omega_using [hk]
    by_cases e : k % 2 = 0
    · rw [ite_eq_left e, get_eq d h.1 h2]
      exact congrArg (fun k => c (g k)) (by omega_using [e])
    · rw [ite_eq_right e, get_eq d h.2 h2]
      exact congrArg (fun k => c (g k)) (by omega_using [e])
  | 0, node .., _, h, _, _, _ | _ + 1, leaf _, _, h, _, _, _ => h.elim

theorem set_eq {β : Type} : ∀ (d : Nat) {t : Tree T} {g : Nat → T}, Holds d t g → ∀ {k : Nat}, k < 2 ^ d →
    ∀ (v : T) (c : Tree T → β), ∃ t', Holds d t' (upd g k v) ∧ t.set k v c = c t'
  | 0, leaf _, g, _, k, hk, v, c => by
    obtain rfl : k = 0 := by omega_using [hk]
    exact ⟨leaf v, rfl, rfl⟩
  | d + 1, node l r, g, h, k, hk, v, c => by
    have h2 : k / 2 < 2 ^ d := by rw [Nat.pow_succ] at hk; omega_using [hk]
    have e0 : (node l r).set k v c = if k % 2 = 0 then l.set (k / 2) v fun l => c (node l r)
        else r.set (k / 2) v fun r => c (node l r) :=
      rec_beq (r.set (k / 2) v fun r => c (node l r)) (l.set (k / 2) v fun l => c (node l r)) (k % 2) 0
    have same (a b : Nat) (hab : a ≠ k) : upd g k v a = g a := by
      rw [upd, show Nat.beq a k = false from Bool.eq_false_iff.mpr fun hb => hab (Nat.beq_eq.mp hb)]; rfl
    have half (b : Nat) (hb : k % 2 = b) :
        (fun j => upd g k v (2 * j + b)) = upd (fun j => g (2 * j + b)) (k / 2) v := by
      funext j
      by_cases hj : j = k / 2
      · rw [upd, upd, Nat.beq_eq.mpr hj, Nat.beq_eq.mpr (show 2 * j + b = k by omega_using [hj, hb])]
      · rw [upd, upd, show Nat.beq j (k / 2) = false from Bool.eq_false_iff.mpr fun hb => hj (Nat.beq_eq.mp hb),
          show Nat.beq (2 * j + b) k = false from Bool.eq_false_iff.mpr fun h => hj (by
            have := Nat.beq_eq.mp h; omega_using [this, hb])]
    have other (b : Nat) (hb : k % 2 ≠ b) (hb2 : b < 2) : (fun j => upd g k v (2 * j + b)) = fun j => g (2 * j + b) := by
      funext j
      rw [upd, show Nat.beq (2 * j + b) k = false from Bool.eq_false_iff.mpr fun h => hb (by
        have := Nat.beq_eq.mp h; omega_using [this, hb2])]
      rfl
    rw [e0]
    by_cases e : k % 2 = 0
    · rw [ite_eq_left e]
      obtain ⟨l', hl, el⟩ := set_eq d h.1 h2 v fun l => c (node l r)
      refine ⟨node l' r, ⟨?_, ?_⟩, el⟩
      · rw [show (fun j => upd g k v (2 * j)) = _ from half 0 e]; exact hl
      · rw [other 1 (by omega_using [e]) (by decide)]; exact h.2
    · rw [ite_eq_right e]
      obtain ⟨r', hr, er⟩ := set_eq d h.2 h2 v fun r => c (node l r)
      refine ⟨node l r', ⟨?_, ?_⟩, er⟩
      · rw [show (fun j => upd g k v (2 * j)) = _ from other 0 e (by decide)]; exact h.1
      · rw [half 1 (by omega_using [e])]; exact hr
  | 0, node .., _, h, _, _, _, _ | _ + 1, leaf _, _, h, _, _, _, _ => h.elim

end Tree

/-- `c` of the tree with `v` at `d`, `v` evaluated by `seq`. -/
noncomputable def put {β : Type} (seq : T → (T → Option β) → Option β) (o : Option T) (t : Tree T) (d : Nat)
    (s : S) (c : Tree T → S → Option β) : Option β :=
  Option.rec none (fun v => seq v fun v => t.set d v fun t => c t s) o

/-- `c` of the state after an instruction. -/
noncomputable def Act.go {β : Type} (seq : T → (T → Option β) → Option β) (a : Act T S) :
    Tree T → S → (Tree T → S → Option β) → Option β :=
  Act.rec (motive := fun _ => Tree T → S → (Tree T → S → Option β) → Option β) (fun _ _ _ => none)
    (fun d f t s c => put seq (f s) t d s c)
    (fun d n f t s c => t.get n fun x => put seq (f s x) t d s c)
    (fun d n m f t s c => t.get n fun x => t.get m fun y => put seq (f s x y) t d s c)
    (fun d n m l f t s c => t.get n fun x => t.get m fun y => t.get l fun z => put seq (f s x y z) t d s c)
    (fun f t s c => Option.rec none (fun s => c t s) (f s))
    (fun n f t s c => t.get n fun x => Option.rec none (fun s => c t s) (f s x)) a

/-- `c` of the state after a block. -/
noncomputable def run {β : Type} (seq : T → (T → Option β) → Option β) (act : I → Act T S) (is : List I) (t : Tree T)
    (s : S) (c : Tree T → S → Option β) : Option β :=
  List.rec (motive := fun _ => Tree T → S → Option β) c (fun i _ ih t s => (act i).go seq t s ih) is t s

/-- The registers an instruction writes and reads are below `n`. -/
def Act.Below (n : Nat) : Act T S → Prop
  | .bad | .s0 _ => True
  | .r0 d _ => d < n
  | .s1 a _ => a < n
  | .r1 d a _ => d < n ∧ a < n
  | .r2 d a b _ => d < n ∧ a < n ∧ b < n
  | .r3 d a b c _ => d < n ∧ a < n ∧ b < n ∧ c < n

theorem put_some {β : Type} {seq : T → (T → Option β) → Option β} (hseq : ∀ v c, seq v c = c v) {n : Nat} {t : Tree T}
    {g : Nat → T} (h : t.Holds n g) {d : Nat} (hd : d < 2 ^ n) {s : S} {c : Tree T → S → Option β} {o : Option T} {b : β}
    (hc : put seq o t d s c = some b) : ∃ v t', o = some v ∧ t'.Holds n (upd g d v) ∧ c t' s = some b := by
  cases o with
  | none => cases hc
  | some v =>
    have hc := (hseq v _).symm.trans hc
    obtain ⟨t', ht, e⟩ := Tree.set_eq n h hd v fun t => c t s
    exact ⟨v, t', rfl, ht, e.symm.trans hc⟩

theorem go_some {β : Type} {seq : T → (T → Option β) → Option β} (hseq : ∀ v c, seq v c = c v) {n : Nat} {t : Tree T}
    {g : Nat → T} (h : t.Holds n g) {s : S} {c : Tree T → S → Option β} {a : Act T S} (ha : a.Below (2 ^ n)) {b : β}
    (hc : a.go seq t s c = some b) :
    ∃ g' s' t', a.app g s = some (g', s') ∧ t'.Holds n g' ∧ c t' s' = some b := by
  cases a with
  | bad => cases hc
  | r0 d f =>
    obtain ⟨v, t', e, ht, hc⟩ := put_some hseq h ha hc
    exact ⟨_, s, t', by rw [Act.app, e]; rfl, ht, hc⟩
  | r1 d a f =>
    obtain ⟨v, t', e, ht, hc⟩ := put_some hseq h ha.1 ((Tree.get_eq n h ha.2 _).symm.trans hc)
    exact ⟨_, s, t', by rw [Act.app, e]; rfl, ht, hc⟩
  | r2 d a b f =>
    obtain ⟨v, t', e, ht, hc⟩ := put_some hseq h ha.1
      ((Tree.get_eq n h ha.2.2 _).symm.trans ((Tree.get_eq n h ha.2.1 _).symm.trans hc))
    exact ⟨_, s, t', by rw [Act.app, e]; rfl, ht, hc⟩
  | r3 d a b l f =>
    obtain ⟨v, t', e, ht, hc⟩ := put_some hseq h ha.1
      ((Tree.get_eq n h ha.2.2.2 _).symm.trans ((Tree.get_eq n h ha.2.2.1 _).symm.trans
        ((Tree.get_eq n h ha.2.1 _).symm.trans hc)))
    exact ⟨_, s, t', by rw [Act.app, e]; rfl, ht, hc⟩
  | s0 f =>
    have hc : Option.rec (motive := fun _ => Option β) none (fun s => c t s) (f s) = some b := hc
    cases e : f s with
    | none => rw [e] at hc; cases hc
    | some s' => rw [e] at hc; exact ⟨g, s', t, by rw [Act.app, e]; rfl, h, hc⟩
  | s1 a f =>
    have hc : Option.rec (motive := fun _ => Option β) none (fun s => c t s) (f s (g a)) = some b :=
      (Tree.get_eq n h ha _).symm.trans hc
    cases e : f s (g a) with
    | none => rw [e] at hc; cases hc
    | some s' => rw [e] at hc; exact ⟨g, s', t, by rw [Act.app, e]; rfl, h, hc⟩

theorem run_sound {β : Type} {seq : T → (T → Option β) → Option β} (hseq : ∀ v c, seq v c = c v) {n : Nat}
    {act : I → Act T S} (hact : ∀ i, (act i).Below (2 ^ n)) {c : Tree T → S → Option β} {b : β} :
    ∀ (is : List I) {t : Tree T} {g : Nat → T} {s : S}, t.Holds n g → run seq act is t s c = some b →
      ∃ g' s' t', exec act is g s = some (g', s') ∧ t'.Holds n g' ∧ c t' s' = some b
  | [], t, g, s, h, hc => ⟨g, s, t, rfl, h, hc⟩
  | i :: is, t, g, s, h, hc => by
    obtain ⟨g₁, s₁, t₁, e, h₁, hc₁⟩ := go_some hseq h (hact i) (c := fun t s => run seq act is t s c) hc
    obtain ⟨g', s', t', e', h', hc'⟩ := run_sound hseq hact is h₁ hc₁
    exact ⟨g', s', t', by rw [exec, e]; exact e', h', hc'⟩

/-- The registers of `L`, and the rest of the state. -/
noncomputable def regs (L : List Nat) (t : Tree T) (s : S) : Option (List T × S) :=
  some (List.rec [] (fun n _ ih => t.get n fun v => v :: ih) L, s)

theorem regs_eq {n : Nat} {t : Tree T} {g : Nat → T} (h : t.Holds n g) {s : S} {L : List Nat} (hL : ∀ r ∈ L, r < 2 ^ n) :
    regs L t s = some (L.map g, s) := by
  refine congrArg (fun l => some (l, s)) ?_
  induction L with
  | nil => rfl
  | cons r L ih =>
    exact (Tree.get_eq n h (hL r List.mem_cons_self) _).trans
      (congrArg (g r :: ·) (ih fun q hq => hL q (List.mem_cons_of_mem _ hq)))

end VG.SymRun
