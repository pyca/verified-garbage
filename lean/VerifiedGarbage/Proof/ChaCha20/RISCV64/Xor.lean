module

import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.ChaCha20.Keystream
meta import VerifiedGarbage.Proof.ChaCha20.Keystream
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Xor
meta import VerifiedGarbage.Impl.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.ChaCha20.Contract
meta import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.WriteBytes
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.ChaCha20.RISCV64
public import VerifiedGarbage.Proof.ChaCha20.Spec
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.ChaCha20
meta import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.ChaCha20.Spec
meta import VerifiedGarbage.Impl.ChaCha20.RISCV64
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.TCB.RISCV64.Isa

/-! ### `ChaCha20.RISCV64.Block`, which this module and modules that import it used -/

section

/-! ### `ChaCha20.RISCV64.Contract`, which this module and modules that import it used -/

section

/-!
# ChaCha20: the RISC-V contract of the block function

**Untrusted**: the contract the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply it
(`Contract.Implies`). The contract of the assembly primitive
`vg_chacha20_block` on RISC-V, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open RISCV64 in
/-- RISC-V contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The code may read `state` (64 bytes) and read and write `buf` (256 bytes;
its first 64 bytes hold the result on exit, and the rest is unspecified).
`buf` may not overlap `state`, and both are 4-byte aligned, as every caller's
are. The pointers are public; the state (key, counter and nonce) is secret. -/
def blockRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 64⟩
    let buf : Region := ⟨s.gpr .a1, 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state ∧
      (s.gpr .a0).toNat % 4 = 0 ∧ (s.gpr .a1).toNat % 4 = 0
  post s s' := stateAt s'.mem (s.gpr .a1) = block (stateAt s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

end

end

/-! ### `ChaCha20.RISCV64.Rounds`, which only this module used -/

section

/-!
# ChaCha20 block function on RISC-V: the rounds

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/ChaCha20/PPC64LE/Block.lean`), but the code runs a round's
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
  have hta : t ≠ a := by omega_using [ha, ht]
  have htb : t ≠ b := by omega_using [hb, ht]
  have htd : t ≠ d := by omega_using [hd, ht]
  have hmt : m ≠ t := by omega_using [ht, hm]
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
      linesOps_words l _ hl, lineOps_words _ ha hb hd had (by omega_using []) hk]
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
    exact h'.holds k (by omega_using [hk])
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
      exact Offset.ofNat_sub_ofNat (k := n) (d := 1) (by omega_using [hn])
    have hv' : Holds (Nat.repeat innerBlock (10 - (n - 1)) v) (b.write U (b.gpr U - (1#64))) := by
      rw [show 10 - (n - 1) = (10 - n) + 1 by omega_using [hn, hle]]
      intro k hlt
      rw [RegUpd.gpr_write_of_ne _ _ (fun e => counter_not_words (.inl ⟨k, hlt, e.symm⟩))]
      exact hb.holds k hlt
    have hk' : ∀ r, ¬ Words r → r ≠ U →
        (b.write U (b.gpr U - (1#64))).gpr r = s₀.gpr r := by
      intro r hwr hru
      rw [RegUpd.gpr_write_of_ne _ _ hru, hb.keep r hwr, hk r hwr hru]
    have he := Steps.eval_nonzero_ofNat (b.write U (b.gpr U - (1#64))) U (by omega_using [hle]) hcc
    by_cases hz : n = 1
    · left
      refine ⟨?_, ?_, hb.mem.trans hm, hb.rd.trans hr, hb.wr.trans hw, hk'⟩
      · simpa only [hz, Nat.sub_self, ne_eq, not_true_eq_false, decide_false] using he
      · simpa only [hz, Nat.sub_self, Nat.sub_zero] using hv'
    · right
      refine ⟨?_, n - 1, by omega_using [hn], by omega_using [hn, hz], by omega_using [hle], hcc, hv', hb.mem.trans hm,
        hb.rd.trans hr, hb.wr.trans hw, hk'⟩
      simpa only [decide_eq_true (by omega_using [hn, hz] : n - 1 ≠ 0)] using he
  · refine ⟨by decide, by decide, RegUpd.gpr_write_self .., ?_, rfl, rfl, rfl,
      fun r _ hru => RegUpd.gpr_write_of_ne _ _ hru⟩
    intro k hk
    rw [RegUpd.gpr_write_of_ne _ _ (fun e => counter_not_words (.inl ⟨k, hk, e.symm⟩))]
    exact h k hk

end VG.Proof.ChaCha20.RISCV64

end

end

/-!
# ChaCha20 block function on RISC-V: the whole function

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/ChaCha20/PPC64LE/Block.lean`), with the state read and the
result written a word at a time (`lwu`, `sw`: both are 4-byte aligned),
and the callee-saved registers saved at `buf + 64` rounded up to a multiple
of 8 (`Proof/Framework/RISCV64/Align.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.RISCV64.Align VG.Impl.ChaCha20.RISCV64
  VG.Impl.Words.RISCV64 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .a0
abbrev buf : Addr := s₀.gpr .a1
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev bufR : Region := ⟨buf s₀, 256⟩
abbrev outR : Region := ⟨buf s₀, 64⟩
/-- How far `buf + 64` is below a multiple of 8. -/
abbrev q : Nat := pad (buf s₀ + BitVec.ofNat 64 64)
/-- Where the callee-saved registers are saved: `buf + 64`, rounded up. -/
abbrev sv : Addr := buf s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (q s₀)
abbrev savR : Region := ⟨buf s₀ + BitVec.ofNat 64 (64 + q s₀), 40⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (st s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

theorem q_lt (s₀ : State) : q s₀ < 8 := pad_lt _

theorem sv_add (s₀ : State) (d : Nat) :
    sv s₀ + BitVec.ofNat 64 d = buf s₀ + BitVec.ofNat 64 (64 + q s₀ + d) := align_add _ _ _

theorem sv_al (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (sv s₀ + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  align_al_add _ hd

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bufR s₀) :=
  Offset.sub_base _ (by have := q_lt s₀; omega_using [this])

theorem outR_sav (s₀ : State) : (outR s₀).Disjoint (savR s₀) :=
  Offset.base_disjoint _ (by omega_using []) (by have := q_lt s₀; omega_using [this])

theorem sav_contains (s₀ : State) {i : Nat} (hi : i < 5) :
    (savR s₀).Contains (sv s₀ + BitVec.ofNat 64 (8 * i)) 8 := by
  have := q_lt s₀
  rw [sv_add]
  exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [this])

theorem outR_sub (s₀ : State) : Region.Sub (outR s₀) (bufR s₀) := Region.sub_prefix (by omega_using [])

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)
  st_al : (st s₀).toNat % 4 = 0
  buf_al : (buf s₀).toNat % 4 = 0

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Word `k` of a 4-byte aligned pointer is 4-byte aligned. -/
theorem al4 {p : Addr} (h : p.toNat % 4 = 0) (k : Nat) : (p + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega_using [h]

/-- `lwu d, off(n)`. -/
theorem loadW_ok {s : State} {d n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block [.load .w d n off]) s
      (· = s.write d ((s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64)) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_load_w ho ha h, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

/-- `sw v, off(n)`. -/
theorem storeW_ok {s : State} {v n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block [.store .w v n off]) s
      (· = { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr v).setWidth 32) }) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_store_w ho ha h, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem out_out {k : Nat} (hk : k < 16) : InRegions s₀.wr (buf s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bufR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_sav {i : Nat} (hi : i < 5) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (sv s₀ + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨bufR s₀, by simp [hp.wr], by
    rw [sv_add]; exact Offset.contains_base _ (by have := q_lt s₀; omega_using [hi, this]) (by have := q_lt s₀; omega_using [hi, this])⟩

theorem out_sav {i : Nat} (hi : i < 5) : InRegions s₀.wr (sv s₀ + BitVec.ofNat 64 (8 * i)) 8 := by
  simpa using hp.in_sav hi []

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  rw [hf.readW (r := stR s₀) (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
    (by simpa using hp.buf_st.symm) (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre

theorem readW_writeW_out (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega_using [h]) (by omega_using [hj]) (by omega_using [hk])) (by decide)

theorem readW_writeW_sav (m : Mem) (p : Addr) (v : BitVec 64) {i j : Nat} (hi : i < 5) (hj : j < 5)
    (h : i ≠ j) :
    (m.writeW (p + BitVec.ofNat 64 (8 * j)) v).readW (p + BitVec.ofNat 64 (8 * i)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * i)) 64 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega_using [h]) (by omega_using [hi]) (by omega_using [hj])) (by decide)

/-! ## Registers -/

theorem wreg_ne {k : Nat} (hk : k < 16) : wreg k ≠ .a0 ∧ wreg k ≠ .a1 ∧ wreg k ≠ U ∧ wreg k ≠ .ra := by
  have key : ∀ k < 16, wreg k ≠ .a0 ∧ wreg k ≠ .a1 ∧ wreg k ≠ U ∧ wreg k ≠ .ra := by decide
  exact key k hk

theorem not_words {r : Reg} (h : ∀ k < 16, r ≠ wreg k) (hT : r ≠ T) : ¬ Words r := by
  rintro (⟨k, hk, e⟩ | e)
  exacts [h k hk e, hT e]

theorem not_words_a0 : ¬ Words .a0 := not_words (fun _ hk e => (wreg_ne hk).1 e.symm) (by decide)
theorem not_words_a1 : ¬ Words .a1 := not_words (fun _ hk e => (wreg_ne hk).2.1 e.symm) (by decide)
theorem not_words_ra : ¬ Words .ra := not_words (fun _ hk e => (wreg_ne hk).2.2.2 e.symm) (by decide)

theorem t0_words : Words .t0 := .inl ⟨0, by decide, rfl⟩

theorem saved_inj {i j : Nat} (hi : i < 5) (hj : j < 5) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 5, ∀ j < 5, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne {i : Nat} (hi : i < 5) : saved i ≠ .t0 ∧ saved i ≠ .a1 := by
  have key : ∀ i < 5, saved i ≠ .t0 ∧ saved i ≠ .a1 := by decide
  exact key i hi

/-- A preserved register is saved, or neither a word register, the
temporary `U` nor `t0`. -/
theorem preserved_cases {r : Reg} (hr : r ∈ preserved) :
    (∃ i < 5, r = saved i) ∨ (¬ Words r ∧ r ≠ U) := by
  have key : ∀ r ∈ preserved, (∃ i < 5, r = saved i) ∨ ((∀ k < 16, r ≠ wreg k) ∧ r ≠ T ∧ r ≠ U) := by
    decide
  rcases key r hr with h | ⟨h, hT, hU⟩
  · exact .inl h
  · exact .inr ⟨not_words h hT, hU⟩

/-! ## Saving the callee-saved registers -/

theorem savePtr_ok {s : State} (h : s.gpr .a1 = buf s) :
    WP isa (.block savePtr) s (· = s.write .t0 (sv s)) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 71 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write,
    Option.some.injEq, exists_eq_left', h]
  rw [align_off_eq _ (off := 64) (by decide) (by decide)]

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  t0 : s.gpr .t0 = sv s₀
  gpr : ∀ r, r ≠ .t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (sv s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 5) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .t0 (8 * n)]) s (SI s₀ (n + 1)) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_store_d (by omega_using [hn]) (by rw [h.t0]; exact sv_al _ (by omega_using []))
    (by rw [h.wr, h.t0]; exact hp.out_sav hn), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.t0, h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ ?_,
    fun i hi => ?_⟩
  · rw [h.t0]; exact sav_contains s₀ hn
  · simp only [h.t0]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [readW_writeW_sav _ _ _ (by omega_arith) hn (by omega_using [hi])]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr _ (saved_ne hn).1]

theorem save_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block save) s₀ (SI s₀ 5) := by
  rw [save, WP.block_append_iff]
  refine WP.mono (savePtr_ok rfl) fun s₁ e => ?_
  subst e
  exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 5 (Nat.le_refl _) _
    ⟨RegUpd.gpr_write_self _ _ _, fun r h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl,
      Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩

/-! ## Loading the state -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → lo (s.gpr (wreg j)) = (V s₀)[j]
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ n s) :
    WP isa (.block [.load .w (wreg n) .a0 (4 * n)]) s (LI s₀ (n + 1)) := by
  have hr0 : s.gpr .a0 = st s₀ := h.keep _ not_words_a0
  refine WP.mono (loadW_ok (by omega_using [hn]) (by rw [hr0]; exact al4 hp.st_al n)
    (by rw [h.rd, h.wr, hr0]; exact hp.in_st hn _)) fun s' e => ?_
  subst e
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * n)) 32 = (V s₀)[n] := by
    rw [h.mem]; exact hp.read_st (Frame.refl _ _) hn
  refine ⟨fun j hj hjn => ?_, h.mem, h.rd, h.wr, fun r hr => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (fun e => absurd (wreg_inj hj hn e) (by omega_using [hjn]))]
      exact h.loaded j hj hjn
    · dsimp only [lo]
      rw [RegUpd.gpr_write_self, lo32_ext, hr0, hv]
  · rw [RegUpd.gpr_write_of_ne _ _ (fun e => hr (.inl ⟨n, hn, e⟩))]
    exact h.keep r hr

/-! ## Adding the input state -/

/-- After finishing words `0 … i - 1`: they are in the output, and words
`i … 15` of the rounds' result `R` are still in their registers. -/
structure FI (s₀ : State) (R : CState) (i : Nat) (s : State) : Prop where
  done : ∀ j (hj : j < 16), j < i →
    s.mem.readW (buf s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j] + (V s₀)[j]
  rest : ∀ j (hj : j < 16), i ≤ j → lo (s.gpr (wreg j)) = R[j]
  frame : Frame [outR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ U → s.gpr r = s₀.gpr r

theorem add_step {s₀ : State} (hp : Pre s₀) {R : CState} {i : Nat} (hi : i < 16)
    {s : State} (h : FI s₀ R i s) :
    WP isa (.block (addWord i)) s (FI s₀ R (i + 1)) := by
  have hr0 : s.gpr .a0 = st s₀ := h.keep _ not_words_a0 (by decide)
  have hr1 : s.gpr .a1 = buf s₀ := h.keep _ not_words_a1 (by decide)
  have hne := wreg_ne hi
  have hv := hp.read_st (h.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bufR s₀, List.mem_singleton_self _, outR_sub s₀⟩) hi
  unfold addWord
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadW_ok (by omega_using [hi]) (by rw [hr0]; exact al4 hp.st_al i)
    (by rw [h.rd, h.wr, hr0]; exact hp.in_st hi _)) fun s₁ e₁ => ?_
  have g₁ : ∀ r, r ≠ T → r ≠ U → s₁.gpr r = s.gpr r := fun r h₁ _ => by
    rw [e₁, RegUpd.gpr_write_of_ne _ _ h₁]
  have t₁ : lo (s₁.gpr T) = (V s₀)[i] := by
    dsimp only [lo]
    rw [e₁, RegUpd.gpr_write_self, lo32_ext, hr0, hv]
  have m₁ : s₁.mem = s.mem := by rw [e₁]; rfl
  have rd₁ : s₁.rd = s.rd := by rw [e₁]; rfl
  have wr₁ : s₁.wr = s.wr := by rw [e₁]; rfl
  rw [List.singleton_append]
  refine Steps.wp_add fun s₂ u₂ => ?_
  have g₂ : ∀ r, r ≠ wreg i → r ≠ T → r ≠ U → s₂.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [u₂.other r h₁, g₁ r h₂ h₃]
  have hw : lo (s₂.gpr (wreg i)) = R[i] + (V s₀)[i] := by
    rw [u₂.gpr]
    have hr := h.rest i hi (Nat.le_refl _)
    dsimp only [lo] at t₁ hr ⊢
    rw [lo32_add, t₁, g₁ _ (wreg_ne_T hi) hne.2.2.1, hr]
  have hr1₂ : s₂.gpr .a1 = buf s₀ := by
    rw [g₂ _ (fun e => hne.2.1 e.symm) (by decide) (by decide), hr1]
  have ho : (outR s₀).Contains (buf s₀ + BitVec.ofNat 64 (4 * i)) 4 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine WP.mono (storeW_ok (by omega_using [hi]) (by rw [hr1₂]; exact al4 hp.buf_al i)
    (by rw [hr1₂, u₂.wr, wr₁, h.wr]; exact hp.out_out hi)) fun s' e => ?_
  subst e
  have hm : s₂.mem.writeW (s₂.gpr .a1 + BitVec.ofNat 64 (4 * i)) ((s₂.gpr (wreg i)).setWidth 32) =
      s.mem.writeW (buf s₀ + BitVec.ofNat 64 (4 * i)) (lo (s₂.gpr (wreg i))) := by
    rw [hr1₂, u₂.mem, m₁]
  refine ⟨fun j hj hji => ?_, fun j hj hij => ?_, ?_, by simp only [u₂.rd, rd₁, h.rd],
    by simp only [u₂.wr, wr₁, h.wr], fun r hr' hU => ?_⟩
  · simp only [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
    · rw [readW_writeW_out _ _ _ hj hi (by omega_using [hji])]; exact h.done j hj hji
    · rw [Mem.readW_writeW_self32, hw]
  · rw [g₂ _ (fun e => absurd (wreg_inj hj hi e) (by omega_using [hij])) (wreg_ne_T hj) (wreg_ne hj).2.2.1]
    exact h.rest j hj (by omega_using [hij])
  · simp only [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ ho
  · show s₂.gpr r = _
    rw [g₂ r (fun e => hr' (.inl ⟨i, hi, e⟩)) (fun e => hr' (.inr e)) hU]
    exact h.keep r hr' hU

/-! ## Restoring the callee-saved registers -/

/-- The first `n` registers are restored, from the state `sB` the
restoring starts in (`t0` pointing at them). -/
structure RI' (s₀ sB : State) (n : Nat) (s : State) : Prop where
  t0 : s.gpr .t0 = sv s₀
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, r ≠ .t0 → (∀ i < 5, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {s₀ sB : State} (hp : Pre s₀)
    (hsav : ∀ i < 5, sB.mem.readW (sv s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 5) {s : State} (h : RI' s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .t0 (8 * n)]) s (RI' s₀ sB (n + 1)) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_load_d (by omega_using [hn]) (by rw [h.t0]; exact sv_al _ (by omega_using []))
    (by rw [h.rd, h.wr, h.t0]; exact hp.in_sav hn _), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun i hi => ?_, fun r h₁ h₂ => ?_, h.mem, h.rd, h.wr⟩
  · rw [RegUpd.gpr_write_of_ne _ _ (saved_ne hn).1.symm, h.t0]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ fun e => absurd (saved_inj (by omega_arith) hn e) (by omega_using [hi])]
      exact h.restored i hi
    · rw [RegUpd.gpr_write_self, h.t0, h.mem, hsav i hn]
  · rw [RegUpd.gpr_write_of_ne _ _ (h₂ n hn)]; exact h.others r h₁ h₂

/-! ## The whole function -/

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

/-- The main part, from the state `s₁` after saving the registers. -/
theorem main_ok {s₁ : State} (hp : Pre s₁) :
    WP isa main s₁ fun s' =>
      (∀ j (hj : j < 16),
        s'.mem.readW (buf s₁ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₁)[j] + (V s₁)[j]) ∧
      Frame [outR s₁] s₁.mem s'.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, ¬ Words r → r ≠ U → s'.gpr r = s₁.gpr r) := by
  have hl₀ : LI s₁ 0 s₁ := ⟨fun _ _ h => absurd h (by omega_using []), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block load) s₁ (LI s₁ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₁) (fun k s hk h => load_step hp hk h) 16 (Nat.le_refl _) s₁ hl₀
  refine WP.seq (WP.mono hload fun s₂ h₂ => ?_)
  have hh₂ : Holds (V s₁) s₂ := fun k hk => h₂.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₂) fun s₃ ⟨hh₃, hm₃, hrd₃, hwr₃, hk₃⟩ => ?_)
  have hf₃ : FI s₁ (Rs s₁) 0 s₃ :=
    ⟨fun _ _ h => absurd h (by omega_using []), fun j hj _ => hh₃ j hj,
      by rw [hm₃, h₂.mem]; exact Frame.refl _ _, hrd₃.trans h₂.rd, hwr₃.trans h₂.wr,
      fun r hr hru => (hk₃ r hr hru).trans (h₂.keep r hr)⟩
  unfold finish
  exact WP.mono (wp_range_flatMap (M := isa) (FI s₁ (Rs s₁)) (fun i s hi h => add_step hp hi h) 16
    (Nat.le_refl _) s₃ hf₃) fun s' h => ⟨fun j hj => h.done j hj hj, h.frame, h.rd, h.wr, h.keep⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      Proof.ChaCha20.blockRISCV64.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ h₁ => ?_)
  have hg : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := h₁.gpr
  have hp₁ : Pre s₁ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [stR, bufR, st, buf, hg .a0 (by decide), hg .a1 (by decide), h₁.rd, h₁.wr] <;>
      first | exact hp.rd | exact hp.wr | exact hp.buf_st | exact hp.st_al | exact hp.buf_al
  have hbuf : buf s₁ = buf s₀ := hg .a1 (by decide)
  have hV : V s₁ = V s₀ := by
    apply Vector.ext
    intro j hj
    simp only [V, stateAt, Vector.getElem_ofFn, st, hg .a0 (by decide)]
    rw [h₁.frame.readW (r := stR s₀) (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (by simpa using Region.Disjoint.sub_right hp.buf_st.symm (savR_sub s₀)) (by decide)]
  refine WP.seq (WP.mono (main_ok hp₁) fun s₃ ⟨hout, hf, hrd, hwr, hk⟩ => ?_)
  have hf' : Frame [outR s₀] s₁.mem s₃.mem := by simpa only [outR, hbuf] using hf
  have hr1 : s₃.gpr .a1 = buf s₀ := by rw [hk _ not_words_a1 (by decide)]; exact hbuf
  have hsav : ∀ i < 5, s₃.mem.readW (sv s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i) :=
    fun i hi => by
      rw [hf'.readW (r := savR s₀) (sav_contains s₀ hi) (by simpa using (outR_sav s₀).symm)
        (by decide)]
      exact h₁.saved i hi
  rw [restore, WP.block_append_iff]
  refine WP.mono (savePtr_ok (s := s₃) rfl) fun s₄ e => ?_
  subst e
  have hsv : sv s₃ = sv s₀ := by simp only [sv, q, buf, hr1]
  have hr₀ : RI' s₀ (s₃.write .t0 (sv s₃)) 0 (s₃.write .t0 (sv s₃)) :=
    ⟨by rw [RegUpd.gpr_write_self, hsv], fun _ h => absurd h (by omega_using []), fun _ _ _ => rfl, rfl,
      by rw [RegUpd.rd_write, hrd, h₁.rd], by rw [RegUpd.wr_write, hwr, h₁.wr]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (RI' s₀ (s₃.write .t0 (sv s₃)))
    (fun k s hk h => restore_step hp (by simpa only [RegUpd.mem_write] using hsav) hk h) 5 (Nat.le_refl _)
    _ hr₀) fun s' h => ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases preserved_cases hr with ⟨i, hi, rfl⟩ | ⟨hw, hU⟩
    · exact h.restored i hi
    · have ht : r ≠ .t0 := fun e => hw (e ▸ t0_words)
      rw [h.others r ht fun i hi e => hw (e ▸ .inr ?_), RegUpd.gpr_write_of_ne _ _ ht, hk r hw hU,
        hg r ht]
      have key : ∀ i < 5, saved i = T ∨ saved i = U ∨ ∃ k < 16, saved i = wreg k := by decide
      rcases key i hi with e' | e' | ⟨k, hk', e'⟩
      · exact e'
      · exact absurd (e.trans e') hU
      · exact absurd (.inl ⟨k, hk', e.trans e'⟩) hw
  · rw [h.others _ (by decide) fun i hi e => ?_, RegUpd.gpr_write_of_ne _ _ (by decide),
      hk _ not_words_ra (by decide), hg _ (by decide)]
    have key : ∀ i < 5, saved i ≠ .ra := by decide
    exact key i hi e.symm
  · show stateAt s'.mem (s₀.gpr .a1) = Spec.ChaCha20.block (stateAt s₀.mem (s₀.gpr .a0))
    rw [h.mem, RegUpd.mem_write]
    have := block_post (m := s₃.mem) (p := buf s₁) (R := Rs s₁) (v := V s₁) hout
    rw [hbuf] at this
    simp only [Rs, hV] at this
    exact this

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 256⟩]

theorem block_verified :
    Verified RISCV64.target Impl.ChaCha20.RISCV64.block Proof.ChaCha20.blockRISCV64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h1, h2]
  · exact ⟨satState, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide⟩

end VG.Proof.ChaCha20.RISCV64

end

end

/-!
# ChaCha20 keystream XOR on RISC-V

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/ChaCha20/PPC64LE/Xor.lean`), with the block counter read and
written a byte at a time and our caller's registers saved at `buf + 256`
rounded up to a multiple of 8.

The source and the destination are either the same buffer or apart
(`XPre.alias`): the loop's invariant says what the destination holds before
the bytes done (`OInv.data`) and that the source after them is intact
(`OInv.src`), which holds in both cases (`src_step`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.RISCV64

/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it.
RISC-V contract for
`vg_chacha20_xor(state: *mut [u32; 16], src: *const u8, len: usize, buf: *mut [u32; 80], dst: *mut u8)`:
writes the `len` bytes at `src` XORed with the first `len` bytes of the
keystream of the state at `state` to the `len` bytes at `dst`.

The code may read `src` (`len` bytes), and read and write `state` (64 bytes;
its contents on exit are unspecified), `dst` (`len` bytes) and `buf` (320
bytes of working space). `dst` is either `src` (in place) or apart from it;
otherwise they may not overlap each other; neither `src` nor `dst` wraps
around the end of the address space; `state` and `buf` are 4-byte aligned,
as every caller's are. The return address is in `ra`, and the code uses no
stack. The pointers and the length are public; the state and the data are
secret. -/
def xorRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 64⟩
    let src : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let buf : Region := ⟨s.gpr .a3, 320⟩
    let dst : Region := ⟨s.gpr .a4, (s.gpr .a2).toNat⟩
    s.rd = [src] ∧ s.wr = [state, dst, buf] ∧
    state.Disjoint src ∧ state.Disjoint dst ∧ state.Disjoint buf ∧ src.Disjoint buf ∧
    dst.Disjoint buf ∧ (s.gpr .a4 = s.gpr .a1 ∨ src.Disjoint dst) ∧
    (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 4 = 0 ∧ (s.gpr .a3).toNat % 4 = 0
  post s s' :=
    bytesAt s'.mem (s.gpr .a4) (s.gpr .a2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
        (keystream (stateAt s.mem (s.gpr .a0)) (s.gpr .a2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.RISCV64.Xor

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.RISCV64.ByteLoad
  VG.Impl.ChaCha20.RISCV64.Xor VG.Impl.Words.RISCV64
open VG.Proof.ChaCha20 (ctr ctr_zero ctr_succ keystream_getD length_keystream bytesAt_xor_to
  serialize_stateAt)
open VG.Proof.ChaCha20.RISCV64 (readW_writeW_out block_verified)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## Arithmetic -/

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- `x >>> 6`, of a number below 2⁶⁴. -/
theorem ofNat_shr6 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 6 = BitVec.ofNat 64 (a / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [h])]

/-- The byte stored by `xor t3, t3, t4; sb t3, …` after two `lbu`s. -/
theorem xor_setWidth (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8) = a ^^^ b := by
  ext i hi; simp

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .a0
/-- The source. -/
abbrev srp : Addr := s₀.gpr .a1
abbrev L : Nat := (s₀.gpr .a2).toNat
abbrev bp : Addr := s₀.gpr .a3
/-- The destination. -/
abbrev dp : Addr := s₀.gpr .a4
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev srR : Region := ⟨srp s₀, L s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
/-- How far `buf + 256` is below a multiple of 8. -/
abbrev q : Nat := pad (bp s₀ + BitVec.ofNat 64 256)
/-- Where our caller's registers are saved: `buf + 256`, rounded up. -/
abbrev sv : Addr := bp s₀ + BitVec.ofNat 64 256 + BitVec.ofNat 64 (q s₀)
abbrev savR : Region := ⟨bp s₀ + BitVec.ofNat 64 (256 + q s₀), 32⟩
/-- The state, the source, the destination and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev X0 (k : Nat) : Byte := s₀.mem (srp s₀ + BitVec.ofNat 64 k)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .a2).isLt

theorem q_lt (s₀ : State) : q s₀ < 8 := pad_lt _

theorem sv_add (s₀ : State) (d : Nat) :
    sv s₀ + BitVec.ofNat 64 d = bp s₀ + BitVec.ofNat 64 (256 + q s₀ + d) := align_add _ _ _

theorem sv_al (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (sv s₀ + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  align_al_add _ hd

theorem sav_contains (s₀ : State) {d : Nat} (hd : d + 8 ≤ 32) :
    (savR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) 8 := by
  have := q_lt s₀
  rw [sv_add]
  exact Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [this])

theorem sav_in (s₀ : State) {d : Nat} (hd : d + 8 ≤ 32) :
    (bR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) 8 := by
  have := q_lt s₀
  rw [sv_add]
  exact Offset.contains_base _ (by omega_using [hd, this]) (by omega_using [hd, this])

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = [srR s₀]
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀]
  st_s : (stR s₀).Disjoint (srR s₀)
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  s_b : (srR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  /-- In place, or apart. -/
  alias : dp s₀ = srp s₀ ∨ (srR s₀).Disjoint (dR s₀)
  snowrap : (srp s₀).toNat + L s₀ ≤ 2 ^ 64
  nowrap : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  st_al : (st s₀).toNat % 4 = 0
  b_al : (bp s₀).toNat % 4 = 0

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorRISCV64.pre s₀) : XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Our caller's `s5`, `s6` and `s7`, and our return address, saved at `sv`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (sv s₀ + BitVec.ofNat 64 0) 64 = s₀.gpr .s5 ∧
  m.readW (sv s₀ + BitVec.ofNat 64 8) 64 = s₀.gpr .s6 ∧
  m.readW (sv s₀ + BitVec.ofNat 64 16) 64 = s₀.gpr .ra ∧
  m.readW (sv s₀ + BitVec.ofNat 64 24) 64 = s₀.gpr .s7

/-- The callee-saved registers the block function writes (and restores). -/
def nvRegs : List Reg := [.s0, .s1, .s2, .s3, .s4]

/-- They hold our caller's values. -/
def NV (s₀ s : State) : Prop := ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r

/-- What the destination holds once the first `n` bytes are done. -/
def Dst (s₀ : State) (n : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < n then X0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k

/-- The source after the first `n` bytes is intact. -/
def Src (s₀ : State) (n : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, n ≤ k → m (srp s₀ + BitVec.ofNat 64 k) = X0 s₀ k

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a1 : s.gpr .a1 = bp s₀
  s5 : s.gpr .s5 = srp s₀ + BitVec.ofNat 64 (P s₀ j)
  s7 : s.gpr .s7 = dp s₀ + BitVec.ofNat 64 (P s₀ j)
  s6 : s.gpr .s6 = BitVec.ofNat 64 (L s₀ - P s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : Dst s₀ (P s₀ j) s.mem
  src : Src s₀ (P s₀ j) s.mem
  saved : Saved s₀ s.mem

/-! ## Memory -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_out m p v (j := i) (k := 12) hi (by omega_using []) (by omega_using [h])

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hd (by decide)

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bp s₀, 256⟩

theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bR s₀) := Region.sub_prefix (by omega_using [])

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bR s₀) :=
  Offset.sub_base _ (by have := q_lt s₀; omega_using [this])

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) :=
  Offset.disjoint_base _ (by omega_using []) (by have := q_lt s₀; omega_using [this])

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hf.readW (sav_contains s₀ (by omega_using [])) hd (by decide), h1],
    by rw [hf.readW (sav_contains s₀ (by omega_using [])) hd (by decide), h2],
    by rw [hf.readW (sav_contains s₀ (by omega_using [])) hd (by decide), h3],
    by rw [hf.readW (sav_contains s₀ (by omega_using [])) hd (by decide), h4]⟩

/-- The destination survives a frame apart from it. -/
theorem Dst.frame {s₀ : State} {n : Nat} {rs : List Region} {m m' : Mem} (h : Dst s₀ n m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) : Dst s₀ n m' := fun k hk => by
  rw [hf.bytes (R := dR s₀) hd (Nat.le_of_lt (L_lt s₀)) hk]; exact h k hk

/-- The source survives a frame apart from it. -/
theorem Src.frame {s₀ : State} {n : Nat} {rs : List Region} {m m' : Mem} (h : Src s₀ n m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (srR s₀).Disjoint r) : Src s₀ n m' := fun k hk hn => by
  rw [hf.bytes (R := srR s₀) hd (Nat.le_of_lt (L_lt s₀)) hk]; exact h k hk hn

/-- A write to the destination that leaves it as `Dst s₀ n'` says leaves the
source after `n'` intact: in place, the destination's bytes after `n'` are
those on entry, which are the source's; apart, the source is outside the
write. -/
theorem src_step {s₀ : State} (hp : XPre s₀) {n n' : Nat} (hn : n ≤ n') {m m' : Mem}
    (hs : Src s₀ n m) (hf : Frame [dR s₀] m m') (hd : Dst s₀ n' m') : Src s₀ n' m' := by
  intro k hk hk'
  rcases hp.alias with he | hdis
  · have := hd k hk
    simp only [show ¬ k < n' by omega_using [hk'], ite_false] at this
    simp only [D0, X0, srp, dp] at this he ⊢
    rw [← he]; exact this
  · rw [hf.bytes (R := srR s₀) (by simpa using hdis) (Nat.le_of_lt (L_lt s₀)) hk]
    exact hs k hk (by omega_using [hn, hk'])

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep p h (by omega_using [hd]) (by omega_using [he])) (by decide)

/-- Distinct bytes of the data are at distinct addresses. -/
theorem data_ne {s₀ : State} {k k' : Nat} (hk : k < L s₀) (hk' : k' < L s₀) (h : k' ≠ k) :
    dp s₀ + BitVec.ofNat 64 k' ≠ dp s₀ + BitVec.ofNat 64 k :=
  Offset.add_ofNat_ne _ (by have := L_lt s₀; omega_using [hk', this]) (by have := L_lt s₀; omega_using [hk, this]) h

/-! ## The prologue -/

theorem savePtr_ok {s : State} (n : Reg) :
    WP isa (.block (savePtr n)) s (· = s.write .t0
      (s.gpr n + BitVec.ofNat 64 256 + BitVec.ofNat 64 (pad (s.gpr n + BitVec.ofNat 64 256)))) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 263 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write,
    Option.some.injEq, exists_eq_left']
  rw [align_off_eq _ (off := 256) (by decide) (by decide)]

theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block (save ++ [mov .s5 .a1, mov .s6 .a2, mov .s7 .a4, mov .a1 .a3])) s₀ (OInv s₀ 0) := by
  obtain o : ∀ d, d + 8 ≤ 32 → InRegions s₀.wr (sv s₀ + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨bR s₀, by simp [hp.wr], sav_in s₀ hd⟩
  rw [save, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a3) fun s₁ e => ?_
  subst e
  obtain t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 0) (by decide) (by rw [t₀]) (sv_al _ (by decide))
    (o 0 (by omega_using [])) fun s₂ g₂ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 8) (by decide) (by rw [g₂.gpr, t₀])
    (sv_al _ (by decide)) (by rw [g₂.wr]; exact o 8 (by omega_using [])) fun s₃ g₃ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 16) (by decide) (by rw [g₃.gpr, g₂.gpr, t₀])
    (sv_al _ (by decide)) (by rw [g₃.wr, g₂.wr]; exact o 16 (by omega_using [])) fun s₄ g₄ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 24) (by decide) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, t₀])
    (sv_al _ (by decide)) (by rw [g₄.wr, g₃.wr, g₂.wr]; exact o 24 (by omega_using [])) fun s₄' g₄' => ?_
  refine wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => wp_mv fun s₆' u₆' => wp_mv fun s₇ u₇ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .t0 → s₄'.gpr r = s₀.gpr r := fun r h => by
    rw [g₄'.gpr, g₄.gpr, g₃.gpr, g₂.gpr, RegUpd.gpr_write_of_ne _ _ h]
  obtain hm : s₇.mem = (((s₀.mem.writeW (sv s₀ + BitVec.ofNat 64 0) (s₀.gpr .s5)).writeW
      (sv s₀ + BitVec.ofNat 64 8) (s₀.gpr .s6)).writeW (sv s₀ + BitVec.ofNat 64 16) (s₀.gpr .ra)).writeW
      (sv s₀ + BitVec.ofNat 64 24) (s₀.gpr .s7) := by
    simp only [u₇.mem, u₆'.mem, u₆.mem, u₅.mem, g₄'.mem, g₄.gpr, g₄.mem, g₃.gpr, g₃.mem, g₂.gpr,
      g₂.mem, RegUpd.gpr_write_of_ne _ _ (show Reg.s5 ≠ .t0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show Reg.s6 ≠ .t0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show Reg.ra ≠ .t0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show Reg.s7 ≠ .t0 by decide)]
    rfl
  obtain hf : Frame [bR s₀] s₀.mem s₇.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sav_in s₀ (by omega_using []))).writeW
      (List.mem_singleton_self _) _ (sav_in s₀ (by omega_using []))).writeW
      (List.mem_singleton_self _) _ (sav_in s₀ (by omega_using []))).writeW
      (List.mem_singleton_self _) _ (sav_in s₀ (by omega_using []))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk _ => ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      g _ (by decide)]
  · rw [u₇.gpr, u₆'.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
  · rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g _ (by decide)]
    simp [P]
  · rw [u₇.other _ (by decide), u₆'.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
    simp [P]
  · rw [u₇.other _ (by decide), u₆'.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g _ (by decide)]
    simp [P]
  · rw [u₇.rd, u₆'.rd, u₆.rd, u₅.rd, g₄'.rd, g₄.rd, g₃.rd, g₂.rd]; rfl
  · rw [u₇.wr, u₆'.wr, u₆.wr, u₅.wr, g₄'.wr, g₄.wr, g₃.wr, g₂.wr]; rfl
  · rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := dR s₀) (by simpa using hp.d_b) (Nat.le_of_lt (L_lt s₀)) hk
  · exact hf.bytes (R := srR s₀) (by simpa using hp.s_b) (Nat.le_of_lt (L_lt s₀)) hk
  · rw [hm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [readW64_off _ _ _ (by omega_using []) (by omega_using []) (by omega_using []),
        readW64_off _ _ _ (by omega_using []) (by omega_using []) (by omega_using []),
        readW64_off _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), Mem.readW_writeW_self64]
    · rw [readW64_off _ _ _ (by omega_using []) (by omega_using []) (by omega_using []),
        readW64_off _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), Mem.readW_writeW_self64]
    · rw [readW64_off _ _ _ (by omega_using []) (by omega_using []) (by omega_using []), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-! ## Calling the block function -/

/-- The registers the block function never writes. -/
def kept : List Reg := [.a0, .a1]

theorem block_keeps : ((instrs Impl.ChaCha20.RISCV64.block).all fun i =>
    kept.all fun r => dstOf i != some r) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem block_keeps_reg {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs Impl.ChaCha20.RISCV64.block, dstOf i ≠ some r := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp block_keeps i hi) r hr
  simpa using this

theorem block_noFrames : Impl.ChaCha20.RISCV64.block.noFrames = true := by decide +kernel

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends OInv s₀ j s where
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem call_ok {s₀ : State} (hp : XPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block) s
      fun s' => AInv s₀ j s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := by
  obtain c0 : s.callEntry.gpr .a0 = st s₀ := (State.callEntry_gpr _ (by decide)).trans h.a0
  obtain c1 : s.callEntry.gpr .a1 = bp s₀ := (State.callEntry_gpr _ (by decide)).trans h.a1
  obtain hwr : s.wr = [stR s₀, dR s₀, bR s₀] := by rw [h.wr, hp.wr]
  obtain hrd : s.rd = [srR s₀] := by rw [h.rd, hp.rd]
  refine WP.call (k := Proof.ChaCha20.blockRISCV64) block_verified.1
    (rd := [stR s₀]) (wr := [b256 s₀]) ?_ ?_ ?_ ?_ block_noFrames
  · simp only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (b256_sub s₀)).symm, hp.st_al, hp.b_al⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_using []⟩
    · exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega_using []⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega_using []⟩
  · intro s₂ hrd₂ hwr₂ _ hf hcs hkeep hpost
    obtain hst : stateAt s₂.mem (st s₀) = stateAt s.mem (st s₀) :=
      stateAt_frame hf (by simpa using hp.st_b.sub_right (b256_sub s₀))
    simp only [Proof.ChaCha20.blockRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, h.cnt] at hpost
    refine ⟨⟨⟨by rw [hkeep .a0 (by decide) (block_keeps_reg (by simp [kept])), h.a0],
      by rw [hkeep .a1 (by decide) (block_keeps_reg (by simp [kept])), h.a1],
      by rw [hcs .s5 (by decide), h.s5],
      by rw [hcs .s7 (by decide), h.s7],
      by rw [hcs .s6 (by decide), h.s6],
      by rw [hrd₂, h.rd], by rw [hwr₂, h.wr], by rw [hst, h.cnt],
      h.data.frame hf (by simpa using hp.d_b.sub_right (b256_sub s₀)),
      h.src.frame hf (by simpa using hp.s_b.sub_right (b256_sub s₀)),
      h.saved.frame hf (by simpa using savR_b256 s₀)⟩, fun t ht => ?_⟩,
      fun r hr => hcs r (by revert r; decide)⟩
    rw [← serialize_stateAt s₂.mem (bp s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  a1 : s.gpr .a1 = bp s₀
  s5 : s.gpr .s5 = srp s₀ + BitVec.ofNat 64 (P s₀ j + i)
  s7 : s.gpr .s7 = dp s₀ + BitVec.ofNat 64 (P s₀ j + i)
  t2 : s.gpr .t2 = bp s₀ + BitVec.ofNat 64 i
  a2 : s.gpr .a2 = BitVec.ofNat 64 (C s₀ j - i)
  s6 : s.gpr .s6 = BitVec.ofNat 64 (L s₀ - P s₀ j - C s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : Dst s₀ (P s₀ j + i) s.mem
  src : Src s₀ (P s₀ j + i) s.mem
  saved : Saved s₀ s.mem
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

def selProg : Prog isa :=
  .seq (.block [.shift .srl .d .t1 .s6 6, mov .a2 .s6])
    (.seq (.ite (.zero .t1) (.block []) (.block [.li .a2 64]))
      (.block [.sub .s6 .s6 .a2, mov .t2 .a1]))

theorem sel_ok {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : AInv s₀ j s) :
    WP isa selProg s (IInv s₀ j 0) := by
  obtain hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  refine WP.seq (wp_srl (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_)
  obtain hr9 : s₂.gpr .t1 = BitVec.ofNat 64 ((L s₀ - P s₀ j) / 64) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.s6, ofNat_shr6 (by omega)]
  obtain hr5 : s₂.gpr .a2 = BitVec.ofNat 64 (L s₀ - P s₀ j) := by
    rw [u₂.gpr, u₁.other _ (by decide), h.s6]
  refine WP.seq (WP.mono (Q := fun s₃ : State => s₃.gpr .a2 = BitVec.ofNat 64 (C s₀ j) ∧
      (∀ r, r ≠ .a2 → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr) ?_
    fun s₃ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite (decide ((L s₀ - P s₀ j) / 64 = 0))
      (eval_zero_ofNat _ _ (by omega_using [hL]) hr9)
      (fun ht => WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hf => wp_li (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
    · simp only [decide_eq_true_eq] at ht
      rw [hr5, show C s₀ j = L s₀ - P s₀ j by omega_using [hC, ht]]
    · simp only [decide_eq_false_iff_not] at hf
      rw [u₃.gpr, show C s₀ j = 64 by omega_using [hC, hf]]
  · refine wp_sub fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ?_
    obtain g : ∀ r, r ≠ .a2 → r ≠ .s6 → r ≠ .t2 → r ≠ .t1 → s₅.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ => by rw [u₅.other r h₃, u₄.other r h₂, f₂ r h₁, u₂.other r h₁, u₁.other r h₄]
    obtain gm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, f₃, u₂.mem, u₁.mem]
    refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide), h.a0],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.a1],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.s5, Nat.add_zero],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.s7, Nat.add_zero],
      by rw [u₅.gpr, u₄.other _ (by decide), f₂ _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.a1]; simp,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), f₁, Nat.sub_zero],
      by rw [u₅.other _ (by decide), u₄.gpr, f₂ _ (by decide), f₁, u₂.other _ (by decide),
        u₁.other _ (by decide), h.s6, sub_ofNat (by omega_using [hC])],
      by rw [u₅.rd, u₄.rd, f₄, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, f₅, u₂.wr, u₁.wr, h.wr],
      by rw [gm, h.cnt], by rw [gm, Nat.add_zero]; exact h.data, by rw [gm, Nat.add_zero]; exact h.src,
      by rw [gm]; exact h.saved, fun t ht => by rw [gm]; exact h.ks t ht⟩

/-! ## One byte -/

def xorBody : List Instr :=
  [.load .b .t3 .s5 0, .load .b .t4 .t2 0, .logic .xor .t3 .t3 .t4, .store .b .t3 .s7 0,
    .addi .s5 .s5 1, .addi .s7 .s7 1, .addi .t2 .t2 1, .addi .a2 .a2 (-1)]

theorem xorLoop_eq : xorLoop = .loop (.block xorBody) (.nonzero .a2) := rfl

/-- `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega_using [hj]

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  obtain hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by omega_using [hi, hC]), hP, show (64 * j + i) / 64 = j by omega_using [hi, hC],
    show (64 * j + i) % 64 = i by omega_using [hi, hC]]

theorem xor_step {s₀ : State} (hp : XPre s₀) {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j)
    {s : State} (h : IInv s₀ j i s) : WP isa (.block xorBody) s (IInv s₀ j (i + 1)) := by
  obtain hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  obtain hk : P s₀ j + i < L s₀ := by omega_using [hi, hC]
  obtain cs : (srR s₀).Contains (srp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hi, hL, hC])
  obtain cd : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hi, hL, hC])
  obtain cb : (bR s₀).Contains (bp s₀ + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega_using [hi, hC]) (by omega_using [hi, hC])
  obtain i₁ : InRegions (s.rd ++ s.wr) (srp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨srR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cs⟩
  obtain i₂ : InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  obtain o₁ : InRegions s.wr (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.wr, hp.wr], cd⟩
  unfold xorBody
  refine wp_lbu (a := srp s₀ + BitVec.ofNat 64 (P s₀ j + i)) (by decide)
    (by rw [h.s5]; exact BitVec.add_zero _) i₁ fun s₁ u₁ => ?_
  refine wp_lbu (a := bp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), h.t2]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sb (a := dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s7]
        exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o₁) fun s₄ g₄ => ?_
  refine wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₅' u₅' => wp_addi (by decide)
    fun s₆ u₆ => wp_subi (imm := 1) (by decide) fun s₇ u₇ => WP.block_nil ?_
  obtain hv : (s₃.gpr .t3).setWidth 8 =
      X0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, xor_setWidth, h.src _ hk (Nat.le_refl _),
      h.ks i (by omega_using [hi, hC]), ks_eq hj hi]
  obtain hm : s₇.mem = s.mem.writeW (dp s₀ + BitVec.ofNat 64 (P s₀ j + i))
      (X0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0) := by
    rw [u₇.mem, u₆.mem, u₅'.mem, u₅.mem, g₄.mem, hv, u₃.mem, u₂.mem, u₁.mem]
  obtain hfd : Frame [dR s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  obtain g : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .s5 → r ≠ .s7 → r ≠ .t2 → r ≠ .a2 → s₇.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₃' h₄ h₅ => by
      rw [u₇.other r h₅, u₆.other r h₄, u₅'.other r h₃', u₅.other r h₃, g₄.gpr, u₃.other r h₁,
        u₂.other r h₂, u₁.other r h₁]
  obtain hd : Dst s₀ (P s₀ j + (i + 1)) s₇.mem := fun k hk' => by
    rw [hm, WriteBytes.writeW8_apply]
    by_cases he : k = P s₀ j + i
    · subst he; simp
    · simp only [data_ne hk hk' he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < P s₀ j + i
      · simp [h₁, show k < P s₀ j + (i + 1) by omega_using [h₁]]
      · simp [h₁, show ¬ k < P s₀ j + (i + 1) by omega_using [he, h₁]]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.a0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.a1], ?_, ?_, ?_,
    ?_,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide),
      g₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s6],
    by rw [u₇.rd, u₆.rd, u₅'.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅'.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [stateAt_frame hfd (by simpa using hp.st_d), h.cnt], hd,
    src_step hp (by omega_using []) h.src hfd hd,
    h.saved.frame hfd (by simpa using (hp.d_b.sub_right (savR_sub s₀)).symm), fun t ht => ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.other _ (by decide), u₅.gpr, g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s5, add_ofNat,
      Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.gpr, u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s7, add_ofNat,
      Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅'.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.t2, add_ofNat]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.a2, sub_ofNat (by omega_using [hi]),
      Nat.sub_sub]
  · rw [hfd.bytes (R := bR s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega_using [])
      (show t < 320 by omega_using [ht])]
    exact h.ks t ht

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) : WP isa xorLoop s (IInv s₀ j (C s₀ j)) := by
  obtain hpos : 0 < C s₀ j := by simp only [C]; omega_using [hj]
  obtain hC : C s₀ j ≤ 64 := by simp only [C]; omega_using []
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = C s₀ j - i ∧ i < C s₀ j ∧ IInv s₀ j i s
  obtain hstep : ∀ n s, Inv n s → WP isa (.block xorBody) s (fun s' =>
      (isa.eval (.nonzero .a2) s' = some false ∧ IInv s₀ j (C s₀ j) s') ∨
      (isa.eval (.nonzero .a2) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (xor_step hp hj hi hI) fun s' h' => ?_
    obtain hz := eval_nonzero_ofNat s' .a2 (by omega_using [hC]) h'.a2
    by_cases hl : i + 1 = C s₀ j
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
    · exact .inr ⟨by rw [hz]; simp; omega_using [hi, hl], C s₀ j - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, hl], h'⟩
  exact WP.loop (M := isa) Inv hstep (C s₀ j) s ⟨0, by simp, hpos, h⟩

/-! ## A whole block, a doubleword at a time -/

/-- Byte `j` of a doubleword of the source XORed with one of the keystream,
stored to the destination. -/
theorem xor8_at (m : Mem) (d x b : Addr) {j : Nat} (hj : j < 8) :
    (m.writeW d (m.readW x 64 ^^^ m.readW b 64)) (d + BitVec.ofNat 64 j) =
      m (x + BitVec.ofNat 64 j) ^^^ m (b + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat d (show j < 2 ^ 64 by omega_using [hj]),
    show j < 64 / 8 by omega_using [hj], ite_true]
  rw [← Mem.extractLsb'_read m x (n := 8) hj, ← Mem.extractLsb'_read m b (n := 8) hj]
  simp only [Mem.readW]
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_xor]

/-- The low three bits of an OR are zero only if each operand's are. -/
theorem low3 {x y z w : BitVec 64} (h : (x ||| y ||| z ||| w) &&& BitVec.ofInt 64 7 = 0) :
    x.toNat % 8 = 0 ∧ y.toNat % 8 = 0 ∧ z.toNat % 8 = 0 ∧ w.toNat % 8 = 0 := by
  obtain e := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or,
    Nat.or_mod_two_pow, Nat.or_mod_two_pow, Nat.or_mod_two_pow, show (0 : BitVec 64).toNat = 0 from rfl,
    Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff] at e
  exact ⟨e.1.1.1, e.1.1.2, e.1.2, e.2⟩

/-- An 8-byte aligned address plus a multiple of 8. -/
theorem al8 {p : Addr} (h : p.toNat % 8 = 0) {i : Nat} (hi : i % 8 = 0) :
    (p + BitVec.ofNat 64 i).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega_using [h, hi]

/-- `IInv` survives a write of `t3`. -/
theorem IInv.t3 {s₀ : State} {j i : Nat} {s s' : State} {v : BitVec 64} (h : IInv s₀ j i s)
    (u : Upd s s' .t3 v) : IInv s₀ j i s' :=
  ⟨by rw [u.other _ (by decide), h.a0], by rw [u.other _ (by decide), h.a1],
    by rw [u.other _ (by decide), h.s5], by rw [u.other _ (by decide), h.s7],
    by rw [u.other _ (by decide), h.t2],
    by rw [u.other _ (by decide), h.a2], by rw [u.other _ (by decide), h.s6],
    by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem, h.cnt],
    by rw [u.mem]; exact h.data, by rw [u.mem]; exact h.src, by rw [u.mem]; exact h.saved,
    fun t ht => by rw [u.mem, h.ks t ht]⟩

def xorWBody : List Instr :=
  [.load .d .t3 .s5 0, .load .d .t4 .t2 0, .logic .xor .t3 .t3 .t4, .store .d .t3 .s7 0,
    .addi .s5 .s5 8, .addi .s7 .s7 8, .addi .t2 .t2 8, .addi .a2 .a2 (-8)]

theorem xorWide_eq : xorWide = .loop (.block xorWBody) (.nonzero .a2) := rfl

theorem xorW_step {s₀ : State} (hp : XPre s₀) {j i : Nat} (hj : P s₀ j < L s₀) (hi : i + 8 ≤ C s₀ j)
    (ax : (srp s₀ + BitVec.ofNat 64 (P s₀ j + i)).toNat % 8 = 0)
    (ad : (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)).toNat % 8 = 0)
    (ab : (bp s₀ + BitVec.ofNat 64 i).toNat % 8 = 0)
    {s : State} (h : IInv s₀ j i s) : WP isa (.block xorWBody) s (IInv s₀ j (i + 8)) := by
  obtain hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  obtain hk : P s₀ j + i + 8 ≤ L s₀ := by omega_using [hi, hC]
  have nw := hp.nowrap
  have snw := hp.snowrap
  generalize hxA : srp s₀ + BitVec.ofNat 64 (P s₀ j + i) = xA at ax
  generalize hdA : dp s₀ + BitVec.ofNat 64 (P s₀ j + i) = dA at ad
  generalize hbA : bp s₀ + BitVec.ofNat 64 i = bA at ab
  obtain cx : (srR s₀).Contains xA 8 := by rw [← hxA]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hi, hL, hC])
  obtain cd : (dR s₀).Contains dA 8 := by rw [← hdA]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hi, hL, hC])
  obtain cb : (bR s₀).Contains bA 8 := by rw [← hbA]; exact Offset.contains_base _ (by omega_using [hi, hC]) (by omega_using [hi, hC])
  obtain i₁ : InRegions (s.rd ++ s.wr) xA 8 := ⟨srR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cx⟩
  obtain i₂ : InRegions (s.rd ++ s.wr) bA 8 := ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  obtain o₁ : InRegions s.wr dA 8 := ⟨dR s₀, by simp [h.wr, hp.wr], cd⟩
  unfold xorWBody
  refine wp_ld (a := xA) (by decide) (by rw [h.s5, hxA]; exact BitVec.add_zero _) ax i₁ fun s₁ u₁ => ?_
  refine wp_ld (a := bA) (by decide) (by rw [u₁.other _ (by decide), h.t2, hbA]; exact BitVec.add_zero _)
    ab (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sd (a := dA) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s7, hdA]
        exact BitVec.add_zero _) ad
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o₁) fun s₄ g₄ => ?_
  refine wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₅' u₅' => wp_addi (by decide)
    fun s₆ u₆ => wp_subi (imm := 8) (by decide) fun s₇ u₇ => WP.block_nil ?_
  obtain hm : s₇.mem = s.mem.writeW dA (s.mem.readW xA 64 ^^^ s.mem.readW bA 64) := by
    rw [u₇.mem, u₆.mem, u₅'.mem, u₅.mem, g₄.mem, u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
      u₃.mem, u₂.mem, u₁.mem]
  obtain hfd : Frame [dR s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  obtain g : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .s5 → r ≠ .s7 → r ≠ .t2 → r ≠ .a2 → s₇.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₃' h₄ h₅ => by
      rw [u₇.other r h₅, u₆.other r h₄, u₅'.other r h₃', u₅.other r h₃, g₄.gpr, u₃.other r h₁,
        u₂.other r h₂, u₁.other r h₁]
  obtain hd : Dst s₀ (P s₀ j + (i + 8)) s₇.mem := fun k hk' => by
    rw [hm]
    by_cases hin : P s₀ j + i ≤ k ∧ k < P s₀ j + i + 8
    · have ek : dp s₀ + BitVec.ofNat 64 k = dA + BitVec.ofNat 64 (k - (P s₀ j + i)) := by
        rw [← hdA, add_ofNat]; congr 2; omega_using [hin]
      obtain ex : xA + BitVec.ofNat 64 (k - (P s₀ j + i)) = srp s₀ + BitVec.ofNat 64 k := by
        rw [← hxA, add_ofNat]; congr 2; omega_using [hin]
      obtain eb : bA + BitVec.ofNat 64 (k - (P s₀ j + i)) =
          bp s₀ + BitVec.ofNat 64 (i + (k - (P s₀ j + i))) := by rw [← hbA, add_ofNat]
      rw [ek, xor8_at _ _ _ _ (by omega_using [hin]), ex, eb, h.src k hk' (by omega_using [hin]), h.ks _ (by omega_using [hi, hC, hin]),
        ite_eq_left (show k < P s₀ j + (i + 8) by omega_using [hin]),
        ← ks_eq hj (by omega_using [hi, hin]), show P s₀ j + (i + (k - (P s₀ j + i))) = k by omega_using [hin]]
    · rw [Mem.writeW, Mem.write_apply (by
          rw [← hdA, Offset.add_sub_add_left]
          exact Offset.not_lt_sub_ofNat (by omega_using [hin]) (by omega_using [hL, hk']) (by omega_using []) (by omega_using [hi, hL, hC])), h.data k hk']
      by_cases h₁ : k < P s₀ j + i
      · simp [h₁, show k < P s₀ j + (i + 8) by omega_using [h₁]]
      · simp [h₁, show ¬ k < P s₀ j + (i + 8) by omega_using [hin, h₁]]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.a0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.a1], ?_, ?_, ?_,
    ?_,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide),
      g₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s6],
    by rw [u₇.rd, u₆.rd, u₅'.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅'.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [stateAt_frame hfd (by simpa using hp.st_d), h.cnt], hd,
    src_step hp (by omega_using []) h.src hfd hd,
    h.saved.frame hfd (by simpa using (hp.d_b.sub_right (savR_sub s₀)).symm), fun t ht => ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.other _ (by decide), u₅.gpr, g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s5, add_ofNat,
      Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅'.gpr, u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.s7, add_ofNat,
      Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅'.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.t2, add_ofNat]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.a2, sub_ofNat (by omega_using [hi]),
      Nat.sub_sub]
  · rw [hfd.bytes (R := bR s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega_using [])
      (show t < 320 by omega_using [ht])]
    exact h.ks t ht

theorem xorWide_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) (hc : C s₀ j % 8 = 0) (ax : (srp s₀ + BitVec.ofNat 64 (P s₀ j)).toNat % 8 = 0)
    (ad : (dp s₀ + BitVec.ofNat 64 (P s₀ j)).toNat % 8 = 0)
    (ab : (bp s₀).toNat % 8 = 0) : WP isa xorWide s (IInv s₀ j (C s₀ j)) := by
  obtain hpos : 0 < C s₀ j := by simp only [C]; omega_using [hj]
  obtain hC : C s₀ j ≤ 64 := by simp only [C]; omega_using []
  rw [xorWide_eq]
  let Inv : Nat → State → Prop := fun n s =>
    ∃ i, n = C s₀ j - i ∧ i < C s₀ j ∧ i % 8 = 0 ∧ IInv s₀ j i s
  obtain hstep : ∀ n s, Inv n s → WP isa (.block xorWBody) s (fun s' =>
      (isa.eval (.nonzero .a2) s' = some false ∧ IInv s₀ j (C s₀ j) s') ∨
      (isa.eval (.nonzero .a2) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, h8, hI⟩
    obtain axi : (srp s₀ + BitVec.ofNat 64 (P s₀ j + i)).toNat % 8 = 0 := by
      rw [← add_ofNat]; exact al8 ax h8
    obtain adi : (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)).toNat % 8 = 0 := by
      rw [← add_ofNat]; exact al8 ad h8
    refine WP.mono (xorW_step hp hj (by omega_using [hc, hi, h8]) axi adi (al8 ab h8) hI) fun s' h' => ?_
    obtain hz := eval_nonzero_ofNat s' .a2 (by omega_using [hC]) h'.a2
    by_cases hl : i + 8 = C s₀ j
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
    · exact .inr ⟨by rw [hz]; simp; omega_using [hc, hi, h8, hl], C s₀ j - (i + 8), by omega_using [hi], i + 8, rfl, by omega_using [hc, hi, h8, hl],
        by omega_using [h8], h'⟩
  exact WP.loop (M := isa) Inv hstep (C s₀ j) s ⟨0, by simp, hpos, rfl, h⟩

theorem xorAny_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) : WP isa xorAny s (IInv s₀ j (C s₀ j)) := by
  obtain hL := L_lt s₀
  unfold xorAny
  refine WP.seq (wp_or fun s₁ u₁ => wp_or fun s₂ u₂ => wp_or fun s₂' u₂' =>
    wp_andi (by decide) fun s₃ u₃ => WP.block_nil ?_)
  obtain h₁ := h.t3 u₁
  obtain h₂ := h₁.t3 u₂
  obtain h₂' := h₂.t3 u₂'
  obtain h₃ := h₂'.t3 u₃
  refine WP.ite (s₃.gpr .t3 == 0) rfl (fun hb => ?_) fun _ => xorLoop_ok hp hj h₃
  obtain e : (s.gpr .s5 ||| s.gpr .t2 ||| s.gpr .a2 ||| s.gpr .s7) &&& BitVec.ofInt 64 7 = 0 := by
    have := beq_iff_eq.mp hb
    rwa [u₃.gpr, u₂'.gpr, u₂.gpr, u₁.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      u₁.other _ (by decide)] at this
  obtain ⟨a5, a2', a2, a7⟩ := low3 e
  rw [h.s5, Nat.add_zero] at a5
  rw [h.s7, Nat.add_zero] at a7
  rw [h.t2, BitVec.add_zero] at a2'
  rw [h.a2, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := C s₀ j) (b := 2 ^ 64)
    (by simp only [C]; omega_using [])] at a2
  exact xorWide_ok hp hj h₃ a2 a5 a7 a2'

/-! ## The end of a block -/

theorem P_succ {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ (j + 1) = P s₀ j + C s₀ j := by
  simp only [P, C] at *; omega

/-- The counter stored by `addi t1, t1, 1` and `sw` after a `lwu t1`. -/
theorem inc_setWidth (v : BitVec 32) :
    ((v.setWidth 64 + BitVec.ofNat 64 1).setWidth 32) = v + 1 := by
  rw [lo32_add, lo32_ext]; rfl

theorem next_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j (C s₀ j) s) : WP isa (.block next) s (OInv s₀ (j + 1)) := by
  obtain hP := P_succ hj
  obtain c₁ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 48) 4 :=
    Offset.contains_base _ (by omega_using []) (by omega_using [])
  obtain al : (st s₀ + BitVec.ofNat 64 48).toNat % 4 = 0 :=
    VG.Proof.ChaCha20.RISCV64.al4 hp.st_al 12
  unfold next
  refine wp_lwu (a := st s₀ + BitVec.ofNat 64 48) (by decide) (by rw [h.a0]) al
    ⟨stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩ fun s₁ u₁ => ?_
  obtain hv : s.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) j)[12] := by
    rw [← h.cnt]; simp [stateAt]
  refine wp_addi (by decide) fun s₂ u₂ => ?_
  obtain a0₂ : s₂.gpr .a0 = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.a0]
  refine wp_sw (a := st s₀ + BitVec.ofNat 64 48) (by decide) (by rw [a0₂]) al
    (by rw [u₂.wr, u₁.wr]; exact ⟨stR s₀, by simp [h.wr, hp.wr], c₁⟩) fun s₃ g₃ => WP.block_nil ?_
  obtain hm : s₃.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 48) ((ctr (S0 s₀) j)[12] + 1) := by
    rw [g₃.mem, u₂.gpr, u₁.gpr, inc_setWidth, hv, u₂.mem, u₁.mem]
  obtain g : ∀ r, r ≠ .t1 → s₃.gpr r = s.gpr r := fun r h₁ => by
    rw [g₃.gpr, u₂.other r h₁, u₁.other r h₁]
  obtain rd₃ : s₃.rd = s.rd := by rw [g₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [g₃.wr, u₂.wr, u₁.wr]
  obtain hfs : Frame [stR s₀] s.mem s₃.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  refine ⟨by rw [g _ (by decide), h.a0], by rw [g _ (by decide), h.a1],
    by rw [g _ (by decide), h.s5, hP], by rw [g _ (by decide), h.s7, hP],
    by rw [g _ (by decide), h.s6, hP, Nat.sub_sub],
    by rw [rd₃, h.rd], by rw [wr₃, h.wr],
    by rw [hm, stateAt_writeW_counter, h.cnt, ctr_succ],
    by rw [hP]; exact h.data.frame hfs (by simpa using hp.st_d.symm),
    by rw [hP]; exact h.src.frame hfs (by simpa using hp.st_s.symm),
    h.saved.frame hfs (by simpa using (hp.st_b.sub_right (savR_sub s₀)).symm)⟩

/-- The body after the call. -/
def rest : Prog isa :=
  .seq (.block [.shift .srl .d .t1 .s6 6, mov .a2 .s6])
  (.seq (.ite (.zero .t1) (.block []) (.block [.li .a2 64]))
  (.seq (.block [.sub .s6 .s6 .a2, mov .t2 .a1])
  (.seq xorAny (.block next))))

theorem body_eq : body = .seq (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block) rest := rfl

theorem rest_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : AInv s₀ j s) : WP isa rest s (OInv s₀ (j + 1)) := by
  obtain hs := sel_ok hj h
  unfold selProg at hs
  rw [WP.seq_iff] at hs
  rw [rest, WP.seq_iff]
  refine WP.mono hs fun s₂ h₂ => ?_
  rw [WP.seq_iff] at h₂
  rw [WP.seq_iff]
  refine WP.mono h₂ fun s₃ h₃ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  exact WP.seq (WP.mono (xorAny_ok hp hj h₄) fun s₅ h₅ => next_ok hp hj h₅)

/-- Registers that code never writes keep their values. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

theorem body_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : OInv s₀ j s) (hnv : NV s₀ s) : WP isa body s fun s' => OInv s₀ (j + 1) s' ∧ NV s₀ s' := by
  rw [body_eq]
  refine WP.seq (WP.mono (call_ok hp h) fun s₁ ⟨h₁, nv₁⟩ => ?_)
  exact WP.mono (WP.gprs (rs := nvRegs) (rest_ok hp hj h₁) (by decide)) fun s₂ ⟨h₂, nv₂⟩ =>
    ⟨h₂, fun r hr => (nv₂ r hr).trans ((nv₁ r hr).trans (hnv r hr))⟩

/-! ## The epilogue -/

/-- What the code guarantees on return, beyond the registers it never writes. -/
def Post (s₀ s' : State) : Prop :=
  s'.gpr .s5 = s₀.gpr .s5 ∧ s'.gpr .s6 = s₀.gpr .s6 ∧ s'.gpr .ra = s₀.gpr .ra ∧
    s'.gpr .s7 = s₀.gpr .s7 ∧ Proof.ChaCha20.xorRISCV64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : OInv s₀ j s) : WP isa (.block restore) s (Post s₀) := by
  obtain i : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (sv s₀ + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], sav_in s₀ hd⟩
  obtain ⟨sv1, sv2, sv3, sv4⟩ := h.saved
  rw [restore, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a1) fun s₁ e => ?_
  subst e
  obtain t₀ : (s.write .t0 (s.gpr .a1 + BitVec.ofNat 64 256 +
      BitVec.ofNat 64 (pad (s.gpr .a1 + BitVec.ofNat 64 256)))).gpr .t0 = sv s₀ := by
    rw [RegUpd.gpr_write_self, h.a1]
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 16) (by decide) (by rw [t₀]) (sv_al _ (by decide))
    (i 16 (by omega_using [])) fun s₂ u₂ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 0) (by decide) (by rw [u₂.other _ (by decide), t₀])
    (sv_al _ (by decide)) (by rw [u₂.rd, u₂.wr]; exact i 0 (by omega_using [])) fun s₃ u₃ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 8) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), t₀])
    (sv_al _ (by decide)) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact i 8 (by omega_using [])) fun s₄ u₄ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 24) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), t₀])
    (sv_al _ (by decide)) (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact i 24 (by omega_using []))
    fun s₅ u₅ => WP.block_nil ?_
  obtain hm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]; rfl
  refine ⟨by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem]; exact sv1,
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem]; exact sv2,
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; exact sv3,
    by rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem]; exact sv4, ?_⟩
  refine bytesAt_xor_to (length_keystream _ _) fun k hk => ?_
  have hk' : k < L s₀ := hk
  rw [hm, h.data k hk']
  simp only [show k < P s₀ j by omega_using [hj, hk'], ite_true]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.RISCV64.Xor.xor =
    .seq (.block (save ++ [mov .s5 .a1, mov .s6 .a2, mov .s7 .a4, mov .a1 .a3]))
    (.seq (.ite (.zero .s6) (.block []) (.loop body (.nonzero .s6))) (.block restore)) := rfl

theorem main_ok {s₀ : State} (hp : XPre s₀) :
    WP isa Impl.ChaCha20.RISCV64.Xor.xor s₀ fun s' => Post s₀ s' ∧ NV s₀ s' := by
  obtain hL := L_lt s₀
  rw [xor_eq]
  refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (prologue_ok hp) (by decide)) fun s₁ ⟨h₁, nv₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s ∧ NV s₀ s) ?_
    fun s₂ ⟨j, hj, h₂, nv₂⟩ => WP.mono (WP.gprs (rs := nvRegs) (epilogue_ok hp hj h₂) (by decide))
      fun s₃ ⟨h₃, nv₃⟩ => ⟨h₃, fun r hr => (nv₃ r hr).trans (nv₂ r hr)⟩)
  obtain hz : isa.eval (.zero .s6) s₁ = some (decide (L s₀ = 0)) := by
    rw [eval_zero_ofNat _ _ (by omega_using [hL]) h₁.s6]
    simp [P]
  refine WP.ite (decide (L s₀ = 0)) hz (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨0, by simp [P, h], h₁, nv₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j < L s₀ ∧ OInv s₀ j s ∧ NV s₀ s
    obtain hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (isa.eval (.nonzero .s6) s' = some false ∧ ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s' ∧ NV s₀ s') ∨
        (isa.eval (.nonzero .s6) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, hI, hnv⟩
      refine WP.mono (body_ok hp hj hI hnv) fun s' ⟨h', nv'⟩ => ?_
      obtain hz' := eval_nonzero_ofNat s' .s6 (by omega_using [hL]) h'.s6
      obtain hP := P_succ hj
      obtain hC : 0 < C s₀ j := by simp only [C]; omega_using [hj]
      obtain hle : P s₀ (j + 1) ≤ L s₀ := by simp only [P]; omega_using []
      by_cases hl : L s₀ - P s₀ (j + 1) = 0
      · exact .inl ⟨by rw [hz']; simp [hl], j + 1, by omega_using [hle, hl], h', nv'⟩
      · exact .inr ⟨by rw [hz']; simp [hl], L s₀ - P s₀ (j + 1), by omega_using [hj, hP, hC], j + 1, rfl, by omega_using [hl],
          h', nv'⟩
    exact WP.loop (M := isa) Inv hstep (L s₀ - P s₀ 0) s₁ ⟨0, rfl, by simp [P]; omega_using [h], h₁, nv₁⟩

/-- The callee-saved registers that no instruction writes, including those of
the block function. -/
def untouched : List Reg := [.s8, .s9, .s10, .s11]

theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs Impl.ChaCha20.RISCV64.Xor.xor,
    dstOf i ≠ some r := by
  have : ((instrs Impl.ChaCha20.RISCV64.Xor.xor).all fun i =>
      untouched.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem correct {s₀ : State} (hp : XPre s₀) :
    ∃ t s', Exec isa Impl.ChaCha20.RISCV64.Xor.xor s₀ t s' ∧ abiPreserved s₀ s' ∧
      Proof.ChaCha20.xorRISCV64.post s₀ s' := by
  obtain ⟨t, s', he, ⟨h5, h6, hra, h7, hpost⟩, hnv⟩ := main_ok hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hra⟩, hpost⟩
  obtain hl : ∀ r ∈ untouched, r ∉ linkRegs := by decide
  obtain key : ∀ r ∈ preserved, r = .s5 ∨ r = .s6 ∨ r = .s7 ∨ r ∈ nvRegs ∨ r ∈ untouched := by decide
  rcases key r hr with rfl | rfl | rfl | h | h
  · exact h5
  · exact h6
  · exact h7
  · exact hnv r h
  · exact Exec.gpr (untouched_ok r h) he (.inr (hl r h))

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.ChaCha20.xorRISCV64.pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4, p5]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorRISCV64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.RISCV64.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorRISCV64.post s s' :=
  correct (XPre.of s hs)

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorRISCV64.pre Proof.ChaCha20.xorRISCV64.pub
    Impl.ChaCha20.RISCV64.Xor.xor :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

/-! ## Calling it

What a caller of `vg_chacha20_xor` needs, once for every caller: a call from
`src` to `dst` (`xor_call_to`), and in place (`xor_call`). -/

theorem xor_noFrames : Impl.ChaCha20.RISCV64.Xor.xor.noFrames = true := by decide +kernel

theorem xor_call_to {s : State} {S X D B : Addr} {n : Nat} (h0 : s.gpr .a0 = S) (h1 : s.gpr .a1 = X)
    (h2 : s.gpr .a2 = BitVec.ofNat 64 n) (h3 : s.gpr .a3 = B) (h4 : s.gpr .a4 = D) (hn : n < 2 ^ 64)
    (hSX : (⟨S, 64⟩ : Region).Disjoint ⟨X, n⟩) (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩)
    (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩) (hXB : (⟨X, n⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hXD : D = X ∨ (⟨X, n⟩ : Region).Disjoint ⟨D, n⟩)
    (hX : X.toNat + n ≤ 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64)
    (hSa : S.toNat % 4 = 0) (hBa : B.toNat % 4 = 0)
    (hc : Covers ([⟨X, n⟩] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.mem s'.mem → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ r, r ∉ linkRegs → (∀ i ∈ instrs Impl.ChaCha20.RISCV64.Xor.xor, dstOf i ≠ some r) →
        s'.gpr r = s.gpr r) →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem X n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.RISCV64.Xor.xor) s Q := by
  obtain hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  obtain c0 : s.callEntry.gpr .a0 = S := (State.callEntry_gpr _ (by decide)).trans h0
  obtain c1 : s.callEntry.gpr .a1 = X := (State.callEntry_gpr _ (by decide)).trans h1
  obtain c2 : s.callEntry.gpr .a2 = BitVec.ofNat 64 n := (State.callEntry_gpr _ (by decide)).trans h2
  obtain c3 : s.callEntry.gpr .a3 = B := (State.callEntry_gpr _ (by decide)).trans h3
  obtain c4 : s.callEntry.gpr .a4 = D := (State.callEntry_gpr _ (by decide)).trans h4
  refine WP.call (k := Proof.ChaCha20.xorRISCV64) xor_correct
    (rd := [⟨X, n⟩]) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_ xor_noFrames
  · simp only [Proof.ChaCha20.xorRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, c4, hn']
    exact ⟨trivial, trivial, hSX, hSD, hSB, hXB, hDB, hXD, hX, hD, hSa, hBa⟩
  · intro s' hrd hwr hsp hf hcs hk hpost
    simp only [Proof.ChaCha20.xorRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c4, hn'] at hpost
    exact hQ s' hrd hwr hsp hf hcs hk hpost

/-- In place: `xor_call_to` with `dst = src`, whose region the caller may
write. -/
theorem xor_call {s : State} {S D B : Addr} {n : Nat} (h0 : s.gpr .a0 = S) (h1 : s.gpr .a1 = D)
    (h2 : s.gpr .a2 = BitVec.ofNat 64 n) (h3 : s.gpr .a3 = B) (h4 : s.gpr .a4 = D) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hD : D.toNat + n ≤ 2 ^ 64)
    (hSa : S.toNat % 4 = 0) (hBa : B.toNat % 4 = 0)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.mem s'.mem → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ r, r ∉ linkRegs → (∀ i ∈ instrs Impl.ChaCha20.RISCV64.Xor.xor, dstOf i ≠ some r) →
        s'.gpr r = s.gpr r) →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.RISCV64.Xor.xor) s Q := by
  refine xor_call_to h0 h1 h2 h3 h4 hn hSD hSD hSB hDB hDB (.inl rfl) hD hD hSa hBa ?_ hw hQ
  intro a m ⟨r, hr, hcr⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr
  · exact hc a m ⟨⟨D, n⟩, by simp, hcr⟩
  · exact hc a m ⟨r, by simpa using hr, hcr⟩

end VG.Proof.ChaCha20.RISCV64.Xor
