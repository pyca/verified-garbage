module

public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.ChaCha20.Spec
public import VerifiedGarbage.Impl.ChaCha20.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ChaCha20 block function on RISC-V: the rounds

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/ChaCha20/PPC64LE/Rounds.lean`), but the code runs a round's
four quarter rounds side by side, operation by operation: the rounds are
proven on lines (`qline`, a step of a quarter round), reordered by a checker
that moves a line only past lines on other words (`LSame`), then on single
operations, reordered the same way (`OSame`), each proven once (`op_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64

open VG VG.RISCV64 VG.Impl.ChaCha20.RISCV64 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

/-! ## Lines: a step of a quarter round on the state -/

/-- An index `i < 16` as a `Fin 16`. -/
def fin16 (i : Nat) : Fin 16 := ⟨i % 16, Nat.mod_lt _ (by decide)⟩

/-- A step of a quarter round: `x[a] += x[b]; x[d] = (x[d] ^ x[a]) <<< k`. -/
def qline (x : CState) (a b d k : Nat) : CState :=
  let y := x.set (fin16 a) (x[fin16 a] + x[fin16 b])
  y.set (fin16 d) ((y[fin16 d] ^^^ y[fin16 a]).rotateLeft k)

/-- The lines of a list in turn. -/
abbrev qlines (l : List (Nat × Nat × Nat × Nat)) (v : CState) : CState :=
  l.foldl (fun x (a, b, d, k) => qline x a b d k) v

theorem qline_get (x : CState) {a b d k : Nat} (ha : a < 16) (hb : b < 16) (hd : d < 16) (had : a ≠ d)
    (m : Nat) (hm : m < 16) :
    (qline x a b d k)[m] =
      if d = m then (x[d] ^^^ (x[a] + x[b])).rotateLeft k else if a = m then x[a] + x[b] else x[m] := by
  simp only [qline, fin16, Vector.getElem_set, Fin.getElem_fin, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hd, had, ite_false, ite_true]

/-- A quarter round is its four lines. -/
theorem qround_qlines (v : CState) (x y z w : Fin 16) (hxy : x.1 ≠ y.1) (hxz : x.1 ≠ z.1) (hxw : x.1 ≠ w.1)
    (hyz : y.1 ≠ z.1) (hyw : y.1 ≠ w.1) (hzw : z.1 ≠ w.1) :
    qround v x y z w = qlines [(x.1, y.1, w.1, 16), (z.1, w.1, y.1, 12), (x.1, y.1, w.1, 8), (z.1, w.1, y.1, 7)] v := by
  apply Vector.ext
  intro m hm
  have hx := x.2; have hy := y.2; have hz := z.2; have hw := w.2
  rw [qround_get _ _ _ _ _ m hm]
  have nyz := Ne.symm hyz
  simp only [qlines, List.foldl_cons, List.foldl_nil, qline_get, hx, hy, hz, hw, hxw, nyz, ne_eq,
    not_false_eq_true]
  have := Ne.symm hxy; have := Ne.symm hxz; have := Ne.symm hxw; have := Ne.symm hyw; have := Ne.symm hzw
  by_cases ew : w.1 = m
  · subst ew; simp [quarterRound, *]
  by_cases ez : z.1 = m
  · subst ez; simp [quarterRound, *]
  by_cases ey : y.1 = m
  · subst ey; simp [quarterRound, *]
  by_cases ex : x.1 = m
  · subst ex; simp [quarterRound, *]
  simp [*]

/-- `innerBlock`'s quarter rounds, as lines in the RFC's order. -/
def qrLines (x y z w : Nat) : List (Nat × Nat × Nat × Nat) :=
  [(x, y, w, 16), (z, w, y, 12), (x, y, w, 8), (z, w, y, 7)]

def rfcLines : List (Nat × Nat × Nat × Nat) :=
  qrLines 0 4 8 12 ++ qrLines 1 5 9 13 ++ qrLines 2 6 10 14 ++ qrLines 3 7 11 15 ++
  qrLines 0 5 10 15 ++ qrLines 1 6 11 12 ++ qrLines 2 7 8 13 ++ qrLines 3 4 9 14

theorem innerBlock_rfc (v : CState) : innerBlock v = qlines rfcLines v := by
  simp only [innerBlock, rfcLines, qlines, List.foldl_append]
  rw [qround_qlines _ 0 4 8 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    qround_qlines _ 1 5 9 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    qround_qlines _ 2 6 10 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    qround_qlines _ 3 7 11 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    qround_qlines _ 0 5 10 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    qround_qlines _ 1 6 11 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    qround_qlines _ 2 7 8 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    qround_qlines _ 3 4 9 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- Lines `l` and `l'` touch disjoint words. -/
def LIndep : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Bool
  | (a, b, d, _), (a', b', d', _) =>
    decide (a < 16 ∧ b < 16 ∧ d < 16 ∧ a' < 16 ∧ b' < 16 ∧ d' < 16 ∧ a ≠ d ∧ a' ≠ d' ∧
      a ≠ a' ∧ a ≠ b' ∧ a ≠ d' ∧ b ≠ a' ∧ b ≠ d' ∧ d ≠ a' ∧ d ≠ b' ∧ d ≠ d')

theorem qline_comm {x : CState} {a b d k a' b' d' k' : Nat} (h : LIndep (a, b, d, k) (a', b', d', k') = true) :
    qline (qline x a b d k) a' b' d' k' = qline (qline x a' b' d' k') a b d k := by
  simp only [LIndep, decide_eq_true_eq] at h
  obtain ⟨ha, hb, hd, ha', hb', hd', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  apply Vector.ext
  intro m hm
  have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5; have := Ne.symm h6; have := Ne.symm h7
  have := Ne.symm h8; have := Ne.symm h9; have := Ne.symm h10
  simp only [qline_get, ha, hb, hd, ha', hb', hd', h1, h2, ne_eq, not_false_eq_true]
  by_cases e1 : d = m
  · subst e1; simp [*]
  by_cases e2 : a = m
  · subst e2; simp [*]
  by_cases e3 : d' = m
  · subst e3; simp [*]
  by_cases e4 : a' = m
  · subst e4; simp [*]
  simp [*]

/-- `l` without its first `p`, if every line before it touches other words. -/
def lpull (p : Nat × Nat × Nat × Nat) : List (Nat × Nat × Nat × Nat) → Option (List (Nat × Nat × Nat × Nat))
  | [] => none
  | q :: l => if q = p then some l else if LIndep q p then (lpull p l).map (q :: ·) else none

/-- `l'` runs the lines of `l`, each moved only past lines on other words. -/
def LSame : List (Nat × Nat × Nat × Nat) → List (Nat × Nat × Nat × Nat) → Bool
  | [], [] => true
  | p :: l', l => match lpull p l with
    | some r => LSame l' r
    | none => false
  | [], _ :: _ => false

theorem qlines_cons (p : Nat × Nat × Nat × Nat) (l : List (Nat × Nat × Nat × Nat)) (v : CState) :
    qlines (p :: l) v = qlines l (qline v p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  obtain ⟨a, b, d, k⟩ := p; rfl

theorem lpull_ok {p : Nat × Nat × Nat × Nat} :
    ∀ {l r : List (Nat × Nat × Nat × Nat)}, lpull p l = some r →
      ∀ v, qlines l v = qlines r (qline v p.1 p.2.1 p.2.2.1 p.2.2.2)
  | [], _, h, _ => by simp [lpull] at h
  | q :: l, r, h, v => by
    unfold lpull at h
    by_cases e : q = p
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h; exact qlines_cons _ _ _
    · simp only [e, ite_false] at h
      by_cases hq : LIndep q p = true
      · simp only [hq, ite_true] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [qlines_cons, lpull_ok hr', qlines_cons]
        obtain ⟨a, b, d, k⟩ := q; obtain ⟨a', b', d', k'⟩ := p
        exact congrArg _ (qline_comm hq)
      · simp only [hq, Bool.false_eq_true, ite_false, reduceCtorEq] at h

theorem lsame_ok : ∀ {l' l : List (Nat × Nat × Nat × Nat)}, LSame l' l = true → ∀ v, qlines l' v = qlines l v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [LSame] at h
  | p :: l', l, h, v => by
    unfold LSame at h
    split at h
    · rename_i r hr
      rw [qlines_cons, lpull_ok hr, lsame_ok h]
    · simp at h

/-- A round's lines as the code runs them: each step of its four quarter rounds in turn. -/
def roundLines (qs : List (Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat × Nat) :=
  qs.map (fun (x, y, _, w) => (x, y, w, 16)) ++ qs.map (fun (_, y, z, w) => (z, w, y, 12)) ++
  qs.map (fun (x, y, _, w) => (x, y, w, 8)) ++ qs.map (fun (_, y, z, w) => (z, w, y, 7))

theorem innerBlock_code (v : CState) :
    innerBlock v = qlines (roundLines columns ++ roundLines diagonals) v :=
  (innerBlock_rfc v).trans (lsame_ok (l' := roundLines columns ++ roundLines diagonals) (l := rfcLines)
    (by decide) v).symm

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : Word := x.setWidth 32

/-! ## Where the words are -/

/-- The state `v` is in the registers. -/
def Holds (v : CState) (s : State) : Prop := ∀ k (hk : k < 16), lo (s.gpr (wreg k)) = v[k]

/-- The registers that hold state words, and the temporary. -/
def Words (r : Reg) : Prop := (∃ k < 16, r = wreg k) ∨ r = T

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne_T {k : Nat} (hk : k < 16) : wreg k ≠ T := by
  have key : ∀ k < 16, wreg k ≠ T := by decide
  exact key k hk

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : CState) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

/-! ## The rounds as operations on seventeen slots

The code of a round is a list of single instructions (`Op`), each on the
slots of the sixteen words (0–15) and the temporary (16): one
lemma per kind of operation (`op_ok`), then a fold over the list (`ops_ok`).
The interleaved order of the operations computes what each quarter round's
lines in turn compute (`roundOps_fold`): an operation moves only past
operations on other slots (`OSame`), and a line's five operations are the
line (`lineOps_words`). -/

/-- The register of slot `i`. -/
def sreg (i : Nat) : Reg := if i < 16 then wreg i else T

theorem sreg_inj {i j : Nat} (hi : i < 17) (hj : j < 17) (h : sreg i = sreg j) : i = j := by
  have key : ∀ i < 17, ∀ j < 17, sreg i = sreg j → i = j := by decide
  exact key i hi j hj h

/-- One instruction of a round, on slots. -/
inductive Op
  | add (a b : Nat)
  | xor (d a : Nat)
  | shl (t d k : Nat)
  | shr (d n : Nat)
  | or (d t : Nat)
  deriving DecidableEq

def Op.code : Op → Instr
  | .add a b => .add (sreg a) (sreg a) (sreg b)
  | .xor d a => .logic .xor (sreg d) (sreg d) (sreg a)
  | .shl t d k => .shift .sll .w (sreg t) (sreg d) k
  | .shr d n => .shift .srl .w (sreg d) (sreg d) n
  | .or d t => .logic .or (sreg d) (sreg d) (sreg t)

/-- The slot an operation writes, and those it reads. -/
def Op.dst : Op → Nat
  | .add a _ | .xor a _ | .shl a _ _ | .shr a _ | .or a _ => a
def Op.srcs : Op → List Nat
  | .add a b | .xor a b | .or a b => [a, b]
  | .shl _ d _ | .shr d _ => [d]

/-- The value an operation writes. -/
def Op.val (x : Nat → Word) : Op → Word
  | .add a b => x a + x b
  | .xor d a => x d ^^^ x a
  | .shl _ d k => x d <<< k
  | .shr d n => x d >>> n
  | .or d t => x d ||| x t

def Op.step (x : Nat → Word) (op : Op) : Nat → Word := fun j => if j = op.dst then op.val x else x j

/-- The slots exist and the shifts are below 32. -/
def Op.Valid : Op → Bool
  | .add a b | .xor a b | .or a b => decide (a < 17 ∧ b < 17)
  | .shl t d k => decide (t < 17 ∧ d < 17 ∧ k < 32)
  | .shr d n => decide (d < 17 ∧ n < 32)

theorem Op.val_congr {x y : Nat → Word} (op : Op) (h : ∀ i ∈ op.srcs, x i = y i) : op.val x = op.val y := by
  cases op <;> simp only [Op.srcs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h <;>
    simp only [Op.val, h]

/-- The slots hold `x`. -/
def Holds17 (x : Nat → Word) (s : State) : Prop := ∀ i < 17, lo (s.gpr (sreg i)) = x i

/-- What an operation leaves. -/
structure OpPost (x : Nat → Word) (s s' : State) : Prop where
  holds : Holds17 x s'
  keep : ∀ r, (∀ i < 17, r ≠ sreg i) → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem op_ok (op : Op) (hv : op.Valid = true) {x : Nat → Word} {s : State} (h : Holds17 x s) :
    WP isa (.block [op.code]) s (OpPost (op.step x) s) := by
  have hd : op.dst < 17 := by cases op <;> simp_all [Op.Valid, Op.dst]
  have hs : ∀ i ∈ op.srcs, i < 17 := by cases op <;> simp_all [Op.Valid, Op.srcs]
  -- The instruction writes the value of `op` into its slot's register, and nothing else.
  have hw : ∃ v : BitVec 64, exec op.code s = some (s.write (sreg op.dst) v) ∧ lo v = op.val x := by
    cases op with
    | add a b =>
      exact ⟨_, exec_add, by simp only [lo32_add, h a (hs a (by simp [Op.srcs])), h b (hs b (by simp [Op.srcs])), Op.val]⟩
    | xor d a =>
      exact ⟨_, exec_logic, by
        simp only [lo32_xor, h d (hs d (by simp [Op.srcs])), h a (hs a (by simp [Op.srcs])), Op.val]⟩
    | shl t d k =>
      have hk : k < 32 := by simp_all [Op.Valid]
      exact ⟨_, exec_shift_w hk, by simp only [lo32_sext, h d (hs d (by simp [Op.srcs])), Op.val]⟩
    | shr d n =>
      have hn : n < 32 := by simp_all [Op.Valid]
      exact ⟨_, exec_shift_w hn, by simp only [lo32_sext, h d (hs d (by simp [Op.srcs])), Op.val]⟩
    | or d t =>
      exact ⟨_, exec_logic, by
        simp only [lo32_or, h d (hs d (by simp [Op.srcs])), h t (hs t (by simp [Op.srcs])), Op.val]⟩
  obtain ⟨v, he, hv'⟩ := hw
  apply WP.of_runBlock
  refine ⟨s.write (sreg op.dst) v, by rw [runBlock_cons, he]; rfl, ⟨fun i hi => ?_, fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · by_cases e : i = op.dst
    · subst e; rw [RegUpd.gpr_write_self, hv']; simp only [Op.step, ↓reduceIte]
    · rw [RegUpd.gpr_write_of_ne _ _ (show sreg i ≠ sreg op.dst from fun e' => e (sreg_inj hi hd e')), h i hi]
      simp only [Op.step, e, ↓reduceIte]
  · exact RegUpd.gpr_write_of_ne _ _ fun e => hr _ hd e

/-- The operations of `ops` in turn. -/
def stepAll (x : Nat → Word) (ops : List Op) : Nat → Word := ops.foldl Op.step x

theorem ops_ok : ∀ (ops : List Op), (ops.all Op.Valid) = true → ∀ {x : Nat → Word} {s : State}, Holds17 x s →
    WP isa (.block (ops.map Op.code)) s (OpPost (stepAll x ops) s)
  | [], _, _, s, h => WP.block_nil ⟨h, fun _ _ => rfl, rfl, rfl, rfl⟩
  | op :: ops, hv, x, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hv
    rw [List.map_cons, show op.code :: ops.map Op.code = [op.code] ++ ops.map Op.code from rfl, WP.block_append_iff]
    refine WP.mono (op_ok op hv.1 h) fun s₁ h₁ => WP.mono (ops_ok ops hv.2 h₁.holds) fun s₂ h₂ =>
      ⟨h₂.holds, fun r hr => (h₂.keep r hr).trans (h₁.keep r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
        h₂.wr.trans h₁.wr⟩

/-! ### Reordering operations -/

/-- Two operations on separate slots: neither writes what the other reads or writes. -/
def OIndep (o o' : Op) : Bool :=
  decide (o.dst ≠ o'.dst ∧ o.dst ∉ o'.srcs ∧ o'.dst ∉ o.srcs)

theorem op_comm {x : Nat → Word} {o o' : Op} (h : OIndep o o' = true) :
    Op.step (Op.step x o) o' = Op.step (Op.step x o') o := by
  simp only [OIndep, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have v1 : o'.val (Op.step x o) = o'.val x :=
    o'.val_congr fun i hi => by
      have : i ≠ o.dst := fun e => h2 (e ▸ hi)
      simp only [Op.step, this, ↓reduceIte]
  have v2 : o.val (Op.step x o') = o.val x :=
    o.val_congr fun i hi => by
      have : i ≠ o'.dst := fun e => h3 (e ▸ hi)
      simp only [Op.step, this, ↓reduceIte]
  funext j
  show (if j = o'.dst then o'.val (Op.step x o) else Op.step x o j) =
    (if j = o.dst then o.val (Op.step x o') else Op.step x o' j)
  rw [v1, v2]
  simp only [Op.step]
  by_cases e1 : j = o'.dst <;> by_cases e2 : j = o.dst
  · exact absurd (e2.symm.trans e1) h1
  all_goals simp_all

/-- `l` without its first `o`, if every operation before it is on other slots. -/
def opull (o : Op) : List Op → Option (List Op)
  | [] => none
  | p :: l => if p = o then some l else if OIndep p o then (opull o l).map (p :: ·) else none

/-- `l'` runs the operations of `l`, each moved only past operations on other slots. -/
def OSame : List Op → List Op → Bool
  | [], [] => true
  | o :: l', l => match opull o l with
    | some r => OSame l' r
    | none => false
  | [], _ :: _ => false

theorem opull_ok {o : Op} : ∀ {l r : List Op}, opull o l = some r → ∀ x, stepAll x l = stepAll (Op.step x o) r
  | [], _, h, _ => by simp [opull] at h
  | p :: l, r, h, x => by
    unfold opull at h
    by_cases e : p = o
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h; rfl
    · simp only [e, ite_false] at h
      by_cases hp : OIndep p o = true
      · simp only [hp, ite_true] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
        show stepAll (Op.step x p) l = stepAll (Op.step (Op.step x o) p) r'
        rw [opull_ok hr', op_comm hp]
      · simp only [hp, Bool.false_eq_true, ite_false, reduceCtorEq] at h

theorem osame_ok : ∀ {l' l : List Op}, OSame l' l = true → ∀ x, stepAll x l' = stepAll x l
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [OSame] at h
  | o :: l', l, h, x => by
    unfold OSame at h
    split at h
    · rename_i r hr
      show stepAll (Op.step x o) l' = stepAll x l
      rw [opull_ok hr, osame_ok h]
    · simp at h

/-! ### Lines -/

/-- A line's five operations, through the temporary `t`. -/
def lineOps (t : Nat) : Nat × Nat × Nat × Nat → List Op
  | (a, b, d, k) => [.add a b, .xor d a, .shl t d k, .shr d (32 - k), .or d t]

/-- The words of the slots. -/
def words (x : Nat → Word) : CState := Vector.ofFn fun i => x i.1

theorem lineOps_words (x : Nat → Word) {a b d k t : Nat} (ha : a < 16) (hb : b < 16) (hd : d < 16)
    (had : a ≠ d) (ht : 16 ≤ t) (hk : k < 32) :
    words (stepAll x (lineOps t (a, b, d, k))) = qline (words x) a b d k := by
  apply Vector.ext
  intro m hm
  have hta : t ≠ a := by omega
  have htb : t ≠ b := by omega
  have htd : t ≠ d := by omega
  have hmt : m ≠ t := by omega
  have hda : d ≠ a := Ne.symm had
  rw [qline_get _ ha hb hd had m hm]
  simp only [words, stepAll, lineOps, List.foldl_cons, List.foldl_nil, Op.step, Op.dst, Op.val, Vector.getElem_ofFn]
  by_cases e1 : m = d
  · subst e1
    simp only [hmt, hda, htd, ↓reduceIte]
    rw [← rotl_shifts _ hk, BitVec.or_comm]
  · by_cases e2 : m = a
    · subst e2
      simp only [e1, hmt, ↓reduceIte, Ne.symm e1]
    · simp only [e1, e2, hmt, ↓reduceIte, Ne.symm e1, Ne.symm e2]

/-- The lines in turn, each through the temporary. -/
def linesOps (l : List (Nat × Nat × Nat × Nat)) : List Op := l.flatMap (lineOps 16)

/-- A round's operations as the code runs them. -/
def roundOps (qs : List (Nat × Nat × Nat × Nat)) : List Op :=
  let step (k : Nat) (ls : List (Nat × Nat × Nat)) : List Op :=
    ls.map (fun (a, b, _) => .add a b) ++ ls.map (fun (a, _, d) => .xor d a) ++
    ls.flatMap fun (_, _, d) => [.shl 16 d k, .shr d (32 - k), .or d 16]
  step 16 (qs.map fun (x, y, _, w) => (x, y, w)) ++ step 12 (qs.map fun (_, y, z, w) => (z, w, y)) ++
    step 8 (qs.map fun (x, y, _, w) => (x, y, w)) ++ step 7 (qs.map fun (_, y, z, w) => (z, w, y))

/-- The code of a round is its operations. -/
theorem round4_code (qs : List (Nat × Nat × Nat × Nat)) (h : qs = columns ∨ qs = diagonals) :
    round4 qs = (roundOps qs).map Op.code := by
  rcases h with rfl | rfl <;> decide

/-- The words after the lines in turn. -/
theorem linesOps_words : ∀ (l : List (Nat × Nat × Nat × Nat)) (x : Nat → Word),
    (l.all fun (a, b, d, k) => decide (a < 16 ∧ b < 16 ∧ d < 16 ∧ a ≠ d ∧ k < 32)) = true →
    words (stepAll x (linesOps l)) = qlines l (words x)
  | [], _, _ => rfl
  | (a, b, d, k) :: l, x, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hb, hd, had, hk⟩, hl⟩ := h
    rw [linesOps, List.flatMap_cons, stepAll, List.foldl_append, ← stepAll, ← stepAll, ← linesOps,
      linesOps_words l _ hl, lineOps_words _ ha hb hd had (by omega) hk]
    simp only [qlines, List.foldl_cons]

theorem roundOps_fold (x : Nat → Word) :
    words (stepAll x (roundOps columns ++ roundOps diagonals)) =
      qlines (roundLines columns ++ roundLines diagonals) (words x) := by
  rw [osame_ok (l := linesOps (roundLines columns ++ roundLines diagonals)) (by decide) x]
  exact linesOps_words _ x (by decide)

/-! ### The double round -/

/-- The slots of a state. -/
def slots (s : State) (i : Nat) : Word := lo (s.gpr (sreg i))

theorem sreg_word {k : Nat} (hk : k < 16) : sreg k = wreg k := by simp [sreg, hk]

theorem doubleRound_ok {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (innerBlock v) s₀) := by
  have hw : words (slots s) = v := by
    apply Vector.ext; intro k hk
    simp only [words, Vector.getElem_ofFn, slots, sreg_word hk]
    exact h.holds k hk
  rw [doubleRound, round4_code _ (.inl rfl), round4_code _ (.inr rfl), ← List.map_append]
  refine WP.mono (ops_ok _ (by decide) (x := slots s) fun i _ => rfl) fun s' h' =>
    ⟨fun k hk => ?_, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => ?_⟩
  · have e : stepAll (slots s) (roundOps columns ++ roundOps diagonals) k =
        (qlines (roundLines columns ++ roundLines diagonals) (words (slots s)))[k] := by
      have := congrArg (·[k]'hk) (roundOps_fold (slots s))
      simpa only [words, Vector.getElem_ofFn] using this
    rw [innerBlock_code, ← hw, ← e, ← sreg_word hk]
    exact h'.holds k (by omega)
  · refine (h'.keep r fun i hi e => hr ?_).trans (h.keep r hr)
    by_cases hi16 : i < 16
    · exact .inl ⟨i, hi16, by rw [e, sreg_word hi16]⟩
    · exact .inr (by rw [e]; simp [sreg, hi16])

/-- The counter is separate from the sixteen words and the rotation temporary. -/
theorem counter_not_words : ¬ Words U := by
  rintro (⟨k, hk, e⟩ | e)
  · have key : ∀ k < 16, U ≠ wreg k := by decide
    exact key k hk e
  · exact absurd e (by decide)

theorem rounds_ok {v : CState} {s₀ : State} (h : Holds v s₀) :
    WP isa rounds s₀ fun s =>
      Holds (Nat.repeat innerBlock 10 v) s ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      (∀ r, ¬ Words r → r ≠ U → s.gpr r = s₀.gpr r) := by
  unfold rounds
  apply WP.seq
  have hi : WP isa (.block [.li U 10]) s₀ (· = s₀.write U 10) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_li (show imm12 10 by decide), runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left']
    rfl
  refine hi.mono fun a ea => ?_
  subst ea
  let Inv : Nat → State → Prop := fun n s =>
    0 < n ∧ n ≤ 10 ∧ s.gpr U = BitVec.ofNat 64 n ∧
    Holds (Nat.repeat innerBlock (10 - n) v) s ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    (∀ r, ¬ Words r → r ≠ U → s.gpr r = s₀.gpr r)
  refine WP.loop (M := isa) Inv ?_ 10 (s₀.write U 10) ?_
  · intro n s ⟨hn, hle, hc, hv, hm, hr, hw, hk⟩
    apply WP.seq
    refine (doubleRound_ok (s₀ := s) ⟨hv, rfl, rfl, rfl, fun _ _ => rfl⟩).mono fun b hb => ?_
    have hcb : b.gpr U = BitVec.ofNat 64 n := (hb.keep U counter_not_words).trans hc
    have hd : WP isa (.block [.addi U U (-1)]) b (· = b.write U (b.gpr U - (1#64))) := by
      apply WP.of_runBlock
      simp only [runBlock_cons, exec_addi (show imm12 (-1) by decide), runStep_some, runBlock_nil,
        Option.some.injEq, exists_eq_left']
      rw [show BitVec.ofInt 64 (-1) = -(1#64) from rfl, ← BitVec.sub_eq_add_neg]
    refine hd.mono fun c ec => ?_
    subst ec
    have hcc : (b.write U (b.gpr U - (1#64))).gpr U = BitVec.ofNat 64 (n - 1) := by
      rw [RegUpd.gpr_write_self, hcb]
      exact Offset.ofNat_sub_ofNat (k := n) (d := 1) (by omega)
    have hv' : Holds (Nat.repeat innerBlock (10 - (n - 1)) v) (b.write U (b.gpr U - (1#64))) := by
      rw [show 10 - (n - 1) = (10 - n) + 1 by omega]
      intro k hlt
      rw [RegUpd.gpr_write_of_ne _ _ (fun e => counter_not_words (.inl ⟨k, hlt, e.symm⟩))]
      exact hb.holds k hlt
    have hk' : ∀ r, ¬ Words r → r ≠ U →
        (b.write U (b.gpr U - (1#64))).gpr r = s₀.gpr r := by
      intro r hwr hru
      rw [RegUpd.gpr_write_of_ne _ _ hru, hb.keep r hwr, hk r hwr hru]
    have he := Steps.eval_nonzero_ofNat (b.write U (b.gpr U - (1#64))) U (by omega) hcc
    by_cases hz : n = 1
    · left
      refine ⟨?_, ?_, hb.mem.trans hm, hb.rd.trans hr, hb.wr.trans hw, hk'⟩
      · simpa only [hz, Nat.sub_self, ne_eq, not_true_eq_false, decide_false] using he
      · simpa only [hz, Nat.sub_self, Nat.sub_zero] using hv'
    · right
      refine ⟨?_, n - 1, by omega, by omega, by omega, hcc, hv', hb.mem.trans hm,
        hb.rd.trans hr, hb.wr.trans hw, hk'⟩
      simpa only [decide_eq_true (by omega : n - 1 ≠ 0)] using he
  · refine ⟨by decide, by decide, RegUpd.gpr_write_self .., ?_, rfl, rfl, rfl,
      fun r _ hru => RegUpd.gpr_write_of_ne _ _ hru⟩
    intro k hk
    rw [RegUpd.gpr_write_of_ne _ _ (fun e => counter_not_words (.inl ⟨k, hk, e.symm⟩))]
    exact h k hk

end VG.Proof.ChaCha20.RISCV64
