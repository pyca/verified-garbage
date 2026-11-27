module

public import VerifiedGarbage.Proof.Scrypt.BlockMix
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa
public import VerifiedGarbage.Proof.Scrypt.Spec
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Range
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa
meta import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.Scrypt.RISCV64.BlockMix
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes
import all Init.Data.Nat.Power2.Basic
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.BlockMix
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes

/-! ### `Scrypt.RISCV64.Common`, which this module and modules that import it used -/

section

/-!
# scrypt on RISC-V: common lemmas

Untrusted: everything here is checked by Lean. The target-independent
lemmas about addresses and bytes are in `Proof/Scrypt/Memory.lean`; here are
the contracts of scryptBlockMix and scryptROMix, for both widths of their
accesses (`wide`: doublewords, which need the pointers to be multiples of 8;
otherwise bytes), and the exclusive-or of a byte.
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.RISCV64 in
/-- RISC-V contract for `vg_scrypt_blockmix(b = a0, r = a1, y = a2,
save = a3)` (`wide`) and `vg_scrypt_blockmix_bytes`: if `r > 0`, writes
scryptBlockMix of the `128 r` bytes at `b` to `y`. `save` (96 bytes, a
multiple of 8) is where it saves its caller's registers;
`b` and `y` must be multiples of 8 for `wide`. -/
def blockMixRISCV64 (wide : Bool) : Contract RISCV64.isa where
  pre s :=
    let r := (s.gpr .a1).toNat
    let b : Region := ⟨s.gpr .a0, r * 128⟩
    let y : Region := ⟨s.gpr .a2, r * 128⟩
    let save : Region := ⟨s.gpr .a3, 96⟩
    s.rd = [b] ∧ s.wr = [y, save] ∧
    y.Disjoint save ∧ b.Disjoint y ∧ b.Disjoint save ∧
    (s.gpr .a0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + r * 128 ≤ 2 ^ 64 ∧
    (s.gpr .a3).toNat + 96 ≤ 2 ^ 64 ∧ 0 < r ∧ (s.gpr .a3).toNat % 8 = 0 ∧
    (wide = true → (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0)
  post s s' := let r := (s.gpr .a1).toNat
    bytesAt s'.mem (s.gpr .a2) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .a0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- RISC-V contract for `vg_scrypt_romix(b = a0, r = a1, v = a2, vlen = a3,
t = a4, save = a5)` (`wide`) and `vg_scrypt_romix_bytes`: if `r > 0` and
`vlen = N r` for a power of two `N`, replaces the `128 r` bytes at `b` by
their scryptROMix, with `t` (`128 r` bytes) as working space. `save` (168
bytes, a multiple of 8) is where it and the functions it calls save their
callers' registers; `b`, `v` and `t` must be multiples of 8 for `wide`. The
indices `j` of step 3 are public. -/
def roMixRISCV64 (wide : Bool) : Contract RISCV64.isa where
  pre s :=
    let r := (s.gpr .a1).toNat
    let b : Region := ⟨s.gpr .a0, r * 128⟩
    let v : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat * 128⟩
    let t : Region := ⟨s.gpr .a4, r * 128⟩
    let save : Region := ⟨s.gpr .a5, 168⟩
    s.rd = [] ∧ s.wr = [b, v, t, save] ∧
    b.Disjoint v ∧ b.Disjoint t ∧ b.Disjoint save ∧ v.Disjoint t ∧ v.Disjoint save ∧
    t.Disjoint save ∧
    (s.gpr .a0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 168 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .a3).toNat % r = 0 ∧ ((s.gpr .a3).toNat / r).isPowerOfTwo ∧
    (s.gpr .a5).toNat % 8 = 0 ∧
    (wide = true → (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a4).toNat % 8 = 0)
  post s s' := let r := (s.gpr .a1).toNat
    bytesAt s'.mem (s.gpr .a0) (128 * r) =
      roMix r ((s.gpr .a3).toNat / r) (bytesAt s.mem (s.gpr .a0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.sp = s₂.sp ∧
    roMixIndices (s₁.gpr .a1).toNat ((s₁.gpr .a3).toNat / (s₁.gpr .a1).toNat)
        (bytesAt s₁.mem (s₁.gpr .a0) (128 * (s₁.gpr .a1).toNat)) =
      roMixIndices (s₂.gpr .a1).toNat ((s₂.gpr .a3).toNat / (s₂.gpr .a1).toNat)
        (bytesAt s₂.mem (s₂.gpr .a0) (128 * (s₂.gpr .a1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.WriteBytes
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt.Memory (sub_off writeW_xor xorBytes_length bytesAt_length bytesAt_add
  bytesAt_writeBytes_sep)

/-- A unit of `xor64`: an 8-byte write of the XOR of two 8-byte reads, as
bytes. -/
theorem writeW_xor_byte (m m' : Mem) (d a b : Addr) :
    m.writeW d (((m' a).setWidth 64 ^^^ (m' b).setWidth 64).setWidth 8) =
      writeBytes m d (xorBytes (bytesAt m' a 1) (bytesAt m' b 1)) := by
  rw [VG.RISCV64.Bytes.xor_setWidth]
  simp only [Mem.writeW, show (8 : Nat) / 8 = 1 from rfl, BitVec.setWidth_eq, write_eq_writeBytes]
  congr 1
  simp [xorBytes, bytesAt, BitVec.extractLsb'_eq_self]

/-- The units' size is positive. -/
theorem unitB_pos (wide : Bool) : 0 < unitB wide := by cases wide <;> decide

end VG.Proof.Scrypt.RISCV64

end

end

/-! ### `Scrypt.RISCV64.Salsa`, which only this module used -/

section

/-!
# The Salsa20/8 Core on RISC-V

Untrusted: everything here is checked by Lean. The rounds on the low words of the
registers (`RI`), each line an addition, a rotation by two word shifts and
two XORs (`line_regs`); then a whole step of scryptBlockMix (`half_core`),
for both widths of its accesses (`wide`: `lw` and `sw`; otherwise the
byte-wise `loadLE32` and `storeLE32`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Scrypt.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Scrypt (Word wordLE bytesAt)
open VG.Proof.Scrypt

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : Word := x.setWidth 32

/-! ## Registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne {k : Nat} (hk : k < 16) :
    wreg k ≠ .t0 ∧ wreg k ≠ .t1 := by
  have key : ∀ k < 16, wreg k ≠ .t0 ∧ wreg k ≠ .t1 := by
    decide
  exact key k hk

/-- The registers that hold words, and the temporaries. -/
def Words (r : Reg) : Prop := (∃ k < 16, r = wreg k) ∨ r = .t0 ∨ r = .t1

theorem words_ne {r : Reg} (h : ¬ Words r) {k : Nat} (hk : k < 16) : r ≠ wreg k :=
  fun e => h (.inl ⟨k, hk, e⟩)

theorem words_t0 {r : Reg} (h : ¬ Words r) : r ≠ .t0 := fun e => h (.inr (.inl e))

theorem words_t1 {r : Reg} (h : ¬ Words r) : r ≠ .t1 := fun e => h (.inr (.inr e))

theorem not_words {r : Reg} (h : ∀ k < 16, r ≠ wreg k) (h0 : r ≠ .t0) (h1 : r ≠ .t1) :
    ¬ Words r := by
  rintro (⟨k, hk, e⟩ | e | e)
  exacts [h k hk e, h0 e, h1 e]

/-! ## One line, on registers -/

/-- `a ^= R(b + c, n)`, through `t0` and `t1`, on the low words. -/
theorem line_regs {a b c : Reg} (ha0 : a ≠ .t0) (ha1 : a ≠ .t1) {n : Nat} (hn0 : 0 < n)
    (hn : n < 32) (s : State) :
    WP isa (.block [.addw .t0 b c, .shift .sll .w .t1 .t0 n, .shift .srl .w .t0 .t0 (32 - n),
        .logic .xor a a .t1, .logic .xor a a .t0]) s fun s' =>
      lo (s'.gpr a) = lo (s.gpr a) ^^^ (lo (s.gpr b) + lo (s.gpr c)).rotateLeft n ∧
      (∀ r, r ≠ a → r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn' : 32 - n < 32 := by omega_using [hn0]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addw, exec_logic, exec_shift_w hn,
    exec_shift_w hn', Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, ha0, ha1, Ne.symm ha0, ite_false, lo32_xor,
      lo32_sext, show Reg.t0 ≠ Reg.t1 by decide, show Reg.t1 ≠ Reg.t0 by decide]
    rw [BitVec.xor_assoc]
    refine congrArg _ ?_
    rw [rotateLeft_eq _ hn0 hn, ← rotr_shifts _ hn', Nat.sub_sub_self (Nat.le_of_lt hn)]
    exact BitVec.xor_comm _ _
  · simp only [RegUpd.gpr_write, h₁, h₂, h₃, ite_false]

/-! ## Where the words are -/

/-- The words `v` are in the low words of the registers. -/
def Holds (v : Vector Word 16) (s : State) : Prop := ∀ k (hk : k < 16), lo (s.gpr (wreg k)) = v[k]

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : Vector Word 16) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {v : Vector Word 16} {s₀ s : State}
    (h : RI v s₀ s) : WP isa (.block (line i j k n)) s (RI (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  refine WP.mono (line_regs (wreg_ne hi).1 (wreg_ne hi).2 (show 0 < n by omega_using [h1])
    (show n < 32 by omega_using [h2]) s) fun s' ⟨ha, hr, hm, hrd, hwr⟩ =>
    ⟨fun m hm' => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw => ?_⟩
  · rw [stepN_get v n hi hj hk m hm']
    by_cases e : i = m
    · subst e
      simp only [ite_true]
      rw [ha, h.holds i hi, h.holds j hj, h.holds k hk]
    · simp only [e, ite_false]
      rw [hr _ (fun e' => e (wreg_inj hi hm' e'.symm)) (wreg_ne hm').1 (wreg_ne hm').2]
      exact h.holds m hm'
  · rw [hr r (fun e => hw (.inl ⟨i, hi, e⟩)) (fun e => hw (.inr (.inl e)))
      (fun e => hw (.inr (.inr e)))]
    exact h.keep r hw

/-! ## Double rounds -/

theorem lines_ok {s₀ : State} :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h) fun s' h' => lines_ok l hl.2 _ s' h'

/-- The lines of a double round in the RFC's order: each quarter-round's four
lines in turn (`lines` takes a line of each in turn). -/
def rfcLines : List (Nat × Nat × Nat × Nat) :=
  [(4, 0, 12, 7), (8, 4, 0, 9), (12, 8, 4, 13), (0, 12, 8, 18), (9, 5, 1, 7), (13, 9, 5, 9), (1, 13, 9, 13), (5, 1, 13, 18), (14, 10, 6, 7), (2, 14, 10, 9), (6, 2, 14, 13), (10, 6, 2, 18), (3, 15, 11, 7), (7, 3, 15, 9), (11, 7, 3, 13), (15, 11, 7, 18)] ++
  [(1, 0, 3, 7), (2, 1, 0, 9), (3, 2, 1, 13), (0, 3, 2, 18), (6, 5, 4, 7), (7, 6, 5, 9), (4, 7, 6, 13), (5, 4, 7, 18), (11, 10, 9, 7), (8, 11, 10, 9), (9, 8, 11, 13), (10, 9, 8, 18), (12, 15, 14, 7), (13, 12, 15, 9), (14, 13, 12, 13), (15, 14, 13, 18)]

/-- The steps of a list of lines. -/
abbrev steps (l : List (Nat × Nat × Nat × Nat)) (v : Vector Word 16) : Vector Word 16 :=
  l.foldl (fun x (i, j, k, n) => stepN x i j k n) v

theorem doubleRound_rfc (v : Vector Word 16) : Spec.Scrypt.doubleRound v = steps rfcLines v := rfl

/-- Lines `a` and `b` touch disjoint words: neither writes a word the other
reads or writes. -/
def Indep : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Bool
  | (i, j, k, _), (i', j', k', _) =>
    decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ i' < 16 ∧ j' < 16 ∧ k' < 16 ∧
      i ≠ i' ∧ i ≠ j' ∧ i ≠ k' ∧ i' ≠ j ∧ i' ≠ k)

theorem stepN_comm {x : Vector Word 16} {i j k n i' j' k' n' : Nat}
    (h : Indep (i, j, k, n) (i', j', k', n') = true) :
    stepN (stepN x i j k n) i' j' k' n' = stepN (stepN x i' j' k' n') i j k n := by
  simp only [Indep, decide_eq_true_eq] at h
  obtain ⟨hi, hj, hk, hi', hj', hk', h1, h2, h3, h4, h5⟩ := h
  apply Vector.ext
  intro m hm
  simp only [stepN_get _ _ hi' hj' hk' _ hm, stepN_get _ _ hi hj hk _ hm, stepN_get _ _ hi hj hk _ hi',
    stepN_get _ _ hi hj hk _ hj', stepN_get _ _ hi hj hk _ hk', stepN_get _ _ hi' hj' hk' _ hi,
    stepN_get _ _ hi' hj' hk' _ hj, stepN_get _ _ hi' hj' hk' _ hk]
  have g1 : i' ≠ i := Ne.symm h1
  by_cases e : i = m
  · subst e; simp [g1, h4, h5]
  · by_cases e' : i' = m
    · subst e'; simp [e, h2, h3]
    · simp [e, e']

/-- `l` without its first `a`, if every line before it is independent of it. -/
def pull (a : Nat × Nat × Nat × Nat) : List (Nat × Nat × Nat × Nat) → Option (List (Nat × Nat × Nat × Nat))
  | [] => none
  | b :: l => if b = a then some l else if Indep b a then (pull a l).map (b :: ·) else none

/-- `l'` runs the lines of `l`, each moved only past lines independent of it. -/
def SameSteps : List (Nat × Nat × Nat × Nat) → List (Nat × Nat × Nat × Nat) → Bool
  | [], [] => true
  | a :: l', l => match pull a l with
    | some r => SameSteps l' r
    | none => false
  | [], _ :: _ => false

theorem steps_cons (a : Nat × Nat × Nat × Nat) (l : List (Nat × Nat × Nat × Nat)) (v : Vector Word 16) :
    steps (a :: l) v = steps l (stepN v a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  obtain ⟨i, j, k, n⟩ := a; rfl

theorem pull_ok {a : Nat × Nat × Nat × Nat} :
    ∀ {l r : List (Nat × Nat × Nat × Nat)}, pull a l = some r →
      ∀ v, steps l v = steps r (stepN v a.1 a.2.1 a.2.2.1 a.2.2.2)
  | [], _, h, _ => by simp [pull] at h
  | b :: l, r, h, v => by
    unfold pull at h
    by_cases e : b = a
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h; exact steps_cons _ _ _
    · simp only [e, ite_false] at h
      by_cases hb : Indep b a = true
      · simp only [hb, ite_true] at h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [steps_cons, pull_ok hr', steps_cons]
        obtain ⟨i, j, k, n⟩ := b; obtain ⟨i', j', k', n'⟩ := a
        exact congrArg _ (stepN_comm hb)
      · simp only [hb, Bool.false_eq_true, ite_false, reduceCtorEq] at h

theorem sameSteps_ok : ∀ {l' l : List (Nat × Nat × Nat × Nat)}, SameSteps l' l = true →
    ∀ v, steps l' v = steps l v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [SameSteps] at h
  | a :: l', l, h, v => by
    unfold SameSteps at h
    split at h
    · rename_i r hr
      rw [steps_cons, pull_ok hr, sameSteps_ok h]
    · simp at h

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v :=
  (doubleRound_rfc v).trans (sameSteps_ok (l' := lines) (l := rfcLines) (by decide) v).symm

theorem doubleRound_ok {v : Vector Word 16} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok lines (by decide) v s h

theorem rounds_ok {v : Vector Word 16} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

/-! ## Words of memory -/

/-- Word `k` of a 4-byte aligned pointer is 4-byte aligned. -/
theorem al4 {p : Addr} (h : p.toNat % 4 = 0) (k : Nat) :
    (p + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega_using [h]

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega_using [h]) (by omega_using [hj]) (by omega_using [hk])) (by decide)

/-- `loadWord`: the low word of `d` is the word read, and only `d` and `t1`
change. -/
theorem loadWord_ok {wide : Bool} {s : State} {d n : Reg} {off : Nat} (hdn : d ≠ n) (hd1 : d ≠ .t1)
    (hn1 : n ≠ .t1) (ho : off + 3 < 2048)
    (ha : wide = true → (s.gpr n + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block (loadWord wide d n off)) s fun s' =>
      lo (s'.gpr d) = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32 ∧
      (∀ r, r ≠ d → r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases wide with
  | true =>
    apply WP.of_runBlock
    simp only [loadWord, ↓reduceIte]
    rw [runBlock_cons, exec_load_w (by omega_using [ho]) (ha rfl) h, runStep_some,
      runBlock_nil]
    refine ⟨_, rfl, ?_, fun r h₁ _ => RegUpd.gpr_write_of_ne _ _ h₁, rfl, rfl, rfl⟩
    dsimp only [lo]
    rw [RegUpd.gpr_write_self, lo32_ext]
  | false =>
    simp only [loadWord, Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (loadLE32_ok hdn (Ne.symm hn1) hd1 ho h) fun s' e => ?_
    subst e
    refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl⟩
    · dsimp only [lo]
      rw [RegUpd.gpr_write_self, lo32_ext]
    · rw [RegUpd.gpr_write_of_ne _ _ h₁, RegUpd.gpr_write_of_ne _ _ h₂]

/-- `storeWord`: the low word of `v` is written, and only `t1` changes. -/
theorem storeWord_ok {wide : Bool} {s : State} {v n : Reg} {off : Nat} (hv1 : v ≠ .t1)
    (hn1 : n ≠ .t1) (ho : off + 3 < 2048)
    (ha : wide = true → (s.gpr n + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block (storeWord wide v n off)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (lo (s.gpr v)) ∧
      (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases wide with
  | true =>
    apply WP.of_runBlock
    simp only [storeWord, ↓reduceIte]
    rw [runBlock_cons, exec_store_w (by omega_using [ho]) (ha rfl) h, runStep_some,
      runBlock_nil]
    exact ⟨_, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
  | false =>
    simp only [storeWord, Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (storeLE32_ok (Ne.symm hv1) (Ne.symm hn1) ho h) fun s' e => ?_
    subst e
    exact ⟨rfl, fun r h₁ => RegUpd.gpr_write_of_ne _ _ h₁, rfl, rfl⟩

/-! ## Loading a block -/

/-- The words of the 64 bytes at `p` are in the registers. -/
def HoldsAt (p : Addr) (s : State) : Prop :=
  ∀ k < 16, lo (s.gpr (wreg k)) = s.mem.readW (p + BitVec.ofNat 64 (4 * k)) 32

/-- After loading `n` words. -/
structure LI (p : Addr) (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j < 16, j < n → lo (s.gpr (wreg j)) = s₀.mem.readW (p + BitVec.ofNat 64 (4 * j)) 32
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  t0 : s.gpr .t0 = p
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

/-- `load` from `t0`. -/
theorem load_ok {wide : Bool} {p : Addr} {s₀ : State} (gp : s₀.gpr .t0 = p)
    (ha : wide = true → p.toNat % 4 = 0)
    (hin : ∀ k < 16, InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (load wide .t0)) s₀ fun s =>
      HoldsAt p s ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      ∀ r, ¬ Words r → s.gpr r = s₀.gpr r := by
  refine WP.mono (wp_range_flatMap (M := isa) (LI p s₀) (fun n s hn h => ?_) 16 (Nat.le_refl _) s₀
    ⟨fun _ _ h => absurd h (by omega_using []), rfl, rfl, rfl, gp, fun _ _ => rfl⟩)
    fun s h => ⟨fun k hk => by rw [h.loaded k hk hk, h.mem], h.mem, h.rd, h.wr, h.keep⟩
  refine WP.mono (loadWord_ok (wreg_ne hn).1 (wreg_ne hn).2 (by decide) (by omega_using [hn])
    (fun hw => by rw [h.t0]; exact al4 (ha hw) n)
    (by rw [h.rd, h.wr, h.t0]; exact hin n hn)) fun s' ⟨hd, hr, hm, hrd, hwr⟩ => ?_
  refine ⟨fun j hj hjn => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr,
    by rw [hr _ (Ne.symm (wreg_ne hn).1) (by decide), h.t0], fun r hw => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [hr _ (fun e => absurd (wreg_inj hj hn e) (by omega_using [hjn])) (wreg_ne hj).2]
      exact h.loaded j hj hjn
    · rw [hd, h.t0, h.mem]
  · rw [hr r (words_ne hw hn) (words_t1 hw)]
    exact h.keep r hw

/-! ## A step: the block at `src` -/

/-- What a step needs of its pointers, `d` in `dR` and `y` in `sR`. -/
structure HP (wide : Bool) (dR sR : Reg) (d y : Addr) (s₀ : State) : Prop where
  gd : s₀.gpr dR = d
  gy : s₀.gpr sR = y
  nd : ¬ Words dR
  ns : ¬ Words sR
  disj : Region.Disjoint ⟨d, 64⟩ ⟨y, 64⟩
  iny : ∀ k < 16, InRegions (s₀.rd ++ s₀.wr) (y + BitVec.ofNat 64 (4 * k)) 4
  outd : ∀ k < 16, InRegions s₀.wr (d + BitVec.ofNat 64 (4 * k)) 4
  ald : wide = true → d.toNat % 4 = 0
  aly : wide = true → y.toNat % 4 = 0

/-- The words of `T`. -/
def tWords (X : Vector Word 16) (m : Mem) (y : Addr) : Vector Word 16 :=
  Vector.ofFn fun j => X[j] ^^^ m.readW (y + BitVec.ofNat 64 (4 * j.1)) 32

theorem tWords_get (X : Vector Word 16) (m : Mem) (y : Addr) {k : Nat} (hk : k < 16) :
    (tWords X m y)[k] = X[k] ^^^ m.readW (y + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [tWords, Vector.getElem_ofFn, Fin.getElem_fin]

/-- After `n` words of `mix`: those words of `T` are in their registers and
at `d`, and the other registers still hold `X`. -/
structure XI (d : Addr) (X T : Vector Word 16) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ j (hj : j < 16), lo (s.gpr (wreg j)) = if j < n then T[j] else X[j]
  out : ∀ j (hj : j < 16), j < n → s.mem.readW (d + BitVec.ofNat 64 (4 * j)) 32 = T[j]
  frame : Frame [⟨d, 64⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem mix_step {wide : Bool} {dR sR : Reg} {d y : Addr} {s₀ : State} (hp : HP wide dR sR d y s₀)
    {X : Vector Word 16} {n : Nat} (hn : n < 16) {s : State} (h : XI d X (tWords X s₀.mem y) s₀ n s) :
    WP isa (.block (mixWord wide dR sR n)) s (XI d X (tWords X s₀.mem y) s₀ (n + 1)) := by
  have gs : s.gpr sR = y := (h.keep _ hp.ns).trans hp.gy
  have hne := wreg_ne hn
  unfold mixWord
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadWord_ok (d := .t0) (Ne.symm (words_t0 hp.ns)) (by decide) (words_t1 hp.ns)
    (by omega_using [hn]) (fun hw => by rw [gs]; exact al4 (hp.aly hw) n)
    (by rw [h.rd, h.wr, gs]; exact hp.iny n hn)) fun s₁ ⟨t₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [List.singleton_append]
  refine Steps.WP.cons exec_logic ?_
  have hd₁ : s₁.gpr dR = d := by
    rw [g₁ _ (words_t0 hp.nd) (words_t1 hp.nd), h.keep _ hp.nd, hp.gd]
  have hr : s.mem.readW (y + BitVec.ofNat 64 (4 * n)) 32 =
      s₀.mem.readW (y + BitVec.ofNat 64 (4 * n)) 32 :=
    h.frame.readW (r := ⟨y, 64⟩) (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))
      (by simpa using hp.disj.symm) (by decide)
  have hw : lo (s₁.gpr (wreg n) ^^^ s₁.gpr .t0) = (tWords X s₀.mem y)[n] := by
    have hx := h.regs n hn
    rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl n)] at hx
    rw [tWords_get _ _ _ hn]
    dsimp only [lo] at t₁ hx ⊢
    rw [lo32_xor, t₁, gs, hr, g₁ _ hne.1 hne.2, hx]
  have hdn : dR ≠ wreg n := words_ne hp.nd hn
  refine WP.mono (storeWord_ok (s := s₁.write (wreg n) _) (v := wreg n) hne.2 (words_t1 hp.nd)
    (by omega_using [hn])
    (fun hwd => by rw [RegUpd.gpr_write_of_ne _ _ hdn, hd₁]; exact al4 (hp.ald hwd) n)
    (by rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ hdn, hd₁, wr₁, h.wr]
        exact hp.outd n hn)) fun s' ⟨m', g', rd', wr'⟩ => ?_
  have hm : s'.mem = s.mem.writeW (d + BitVec.ofNat 64 (4 * n)) (tWords X s₀.mem y)[n] := by
    rw [m', RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ hdn, hd₁, RegUpd.gpr_write_self]
    rw [← hw, m₁]
  have g₂ : ∀ r, r ≠ wreg n → r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₃, RegUpd.gpr_write_of_ne _ _ h₁, g₁ r h₂ h₃]
  refine ⟨fun j hj => ?_, fun j hj hjn => ?_, ?_, by rw [rd', RegUpd.rd_write, rd₁, h.rd],
    by rw [wr', RegUpd.wr_write, wr₁, h.wr], fun r hw' => ?_⟩
  · by_cases e : j = n
    · subst e
      rw [g' _ hne.2, RegUpd.gpr_write_self, ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self j) h]
      exact hw
    · rw [g₂ _ (fun e' => e (wreg_inj hj hn e')) (wreg_ne hj).1 (wreg_ne hj).2, h.regs j hj]
      by_cases hji : j < n
      · rw [ite_eq_left_iff.mpr fun h => absurd hji h,
          ite_eq_left_iff.mpr fun h => absurd (by omega_using [hji]) h]
      · rw [ite_eq_right_iff.mpr fun h => absurd h hji,
          ite_eq_right_iff.mpr fun h => absurd h (by omega_using [e, hji])]
  · rw [hm]
    by_cases e : j = n
    · subst e
      rw [Mem.readW_writeW_self32]
    · rw [readW_writeW_word _ _ _ hj hn e, h.out j hj (by omega_using [hjn, e])]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))
  · rw [g₂ r (words_ne hw' hn) (words_t0 hw') (words_t1 hw')]
    exact h.keep r hw'

/-! ## A step: adding `T` -/

/-- After finishing words `0 … i - 1`: those words are the sums, at `d` and
in their registers, the others at `d` still hold `T`, and in their registers
the rounds' result `R`. -/
structure FI (d : Addr) (R T : Vector Word 16) (s₀ : State) (i : Nat) (s : State) : Prop where
  regs : ∀ j (hj : j < 16), lo (s.gpr (wreg j)) = if j < i then R[j] + T[j] else R[j]
  out : ∀ j (hj : j < 16), s.mem.readW (d + BitVec.ofNat 64 (4 * j)) 32 =
    if j < i then R[j] + T[j] else T[j]
  frame : Frame [⟨d, 64⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem finish_step {wide : Bool} {dR sR : Reg} {d y : Addr} {s₀ : State} (hp : HP wide dR sR d y s₀)
    {R T : Vector Word 16} {i : Nat} (hi : i < 16) {s : State} (h : FI d R T s₀ i s) :
    WP isa (.block (finishWord wide dR i)) s (FI d R T s₀ (i + 1)) := by
  have hr0 : s.gpr dR = d := (h.keep _ hp.nd).trans hp.gd
  have hne := wreg_ne hi
  have hv : s.mem.readW (d + BitVec.ofNat 64 (4 * i)) 32 = T[i] := by
    rw [h.out i hi, ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl i)]
  unfold finishWord
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadWord_ok (d := .t0) (Ne.symm (words_t0 hp.nd)) (by decide) (words_t1 hp.nd)
    (by omega_using [hi]) (fun hw => by rw [hr0]; exact al4 (hp.ald hw) i)
    (by rw [h.rd, h.wr, hr0]; exact Memory.InRegions.right (hp.outd i hi))) fun s₁ ⟨t₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [List.singleton_append]
  refine Steps.WP.cons exec_addw ?_
  have hb₁ : s₁.gpr dR = d := by rw [g₁ _ (words_t0 hp.nd) (words_t1 hp.nd), hr0]
  have hw : lo (sext32 (lo (s₁.gpr (wreg i)) + lo (s₁.gpr .t0))) = R[i] + T[i] := by
    have hx := h.regs i hi
    rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl i)] at hx
    dsimp only [lo] at t₁ hx ⊢
    rw [lo32_sext, t₁, hr0, hv, g₁ _ hne.1 hne.2, hx]
  have hdn : dR ≠ wreg i := words_ne hp.nd hi
  refine WP.mono (storeWord_ok (s := s₁.write (wreg i) _) (v := wreg i) hne.2 (words_t1 hp.nd)
    (by omega_using [hi])
    (fun hwd => by rw [RegUpd.gpr_write_of_ne _ _ hdn, hb₁]; exact al4 (hp.ald hwd) i)
    (by rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ hdn, hb₁, wr₁, h.wr]
        exact hp.outd i hi)) fun s' ⟨m', g', rd', wr'⟩ => ?_
  have hm : s'.mem = s.mem.writeW (d + BitVec.ofNat 64 (4 * i)) (R[i] + T[i]) := by
    rw [m', RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ hdn, hb₁, RegUpd.gpr_write_self, hw, m₁]
  have g₂ : ∀ r, r ≠ wreg i → r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₃, RegUpd.gpr_write_of_ne _ _ h₁, g₁ r h₂ h₃]
  refine ⟨fun j hj => ?_, fun j hj => ?_, ?_, by rw [rd', RegUpd.rd_write, rd₁, h.rd],
    by rw [wr', RegUpd.wr_write, wr₁, h.wr], fun r hw' => ?_⟩
  · by_cases e : j = i
    · subst e
      rw [g' _ hne.2, RegUpd.gpr_write_self, ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self j) h]
      exact hw
    · rw [g₂ _ (fun e' => e (wreg_inj hj hi e')) (wreg_ne hj).1 (wreg_ne hj).2, h.regs j hj]
      by_cases hji : j < i
      · rw [ite_eq_left_iff.mpr fun h => absurd hji h,
          ite_eq_left_iff.mpr fun h => absurd (by omega_using [hji]) h]
      · rw [ite_eq_right_iff.mpr fun h => absurd h hji,
          ite_eq_right_iff.mpr fun h => absurd h (by omega_using [e, hji])]
  · rw [hm]
    by_cases e : j = i
    · subst e
      rw [Mem.readW_writeW_self32, ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self j) h]
    · rw [readW_writeW_word _ _ _ hj hi e, h.out j hj]
      by_cases hji : j < i
      · rw [ite_eq_left_iff.mpr fun h => absurd hji h,
          ite_eq_left_iff.mpr fun h => absurd (by omega_using [hji]) h]
      · rw [ite_eq_right_iff.mpr fun h => absurd h hji,
          ite_eq_right_iff.mpr fun h => absurd h (by omega_using [e, hji])]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  · rw [g₂ r (words_ne hw' hi) (words_t0 hw') (words_t1 hw')]
    exact h.keep r hw'

/-! ## A whole step -/

theorem bytes_xor (p q r t p' q' r' t' : Byte) :
    (p ++ q ++ r ++ t : BitVec (8 + 8 + 8 + 8)) ^^^ (p' ++ q' ++ r' ++ t') =
      (p ^^^ p') ++ (q ^^^ q') ++ (r ^^^ r') ++ (t ^^^ t') := by
  simp only [BitVec.xor_append]

/-- The words of the exclusive-or of two byte strings. -/
theorem wordLE_xor (a b : List Byte) (ha : a.length = 64) (hb : b.length = 64) {j : Nat} (hj : j < 16) :
    wordLE (Spec.Pbkdf2.xorBytes a b) j = wordLE a j ^^^ wordLE b j := by
  have e : ∀ i < 64, (Spec.Pbkdf2.xorBytes a b).getD i 0 = a.getD i 0 ^^^ b.getD i 0 := fun i hi => by
    simp only [Spec.Pbkdf2.xorBytes, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
      List.getElem?_eq_getElem (show i < a.length by omega_using [hi, ha]),
      List.getElem?_eq_getElem (show i < b.length by omega_using [hi, hb]), Option.getD_some]
  simp only [wordLE, e _ (show 4 * j + 3 < 64 by omega_using [hj]),
    e _ (show 4 * j + 2 < 64 by omega_using [hj]), e _ (show 4 * j + 1 < 64 by omega_using [hj]),
    e _ (show 4 * j < 64 by omega_using [hj])]
  exact (bytes_xor _ _ _ _ _ _ _ _).symm

/-- A step: `X`, the words of the bytes `x`, becomes the Salsa20/8 Core of
`x xor` the bytes at `y`, in the registers and at `d`. -/
theorem half_core {wide : Bool} {dR sR : Reg} {d y : Addr} {s₀ : State} (hp : HP wide dR sR d y s₀)
    {x : List Byte} (hl : x.length = 64) (hx : ∀ k < 16, lo (s₀.gpr (wreg k)) = wordLE x k) :
    WP isa (half wide dR sR) s₀ fun s' =>
      bytesAt s'.mem d 64 =
        Spec.Scrypt.salsa (Spec.Pbkdf2.xorBytes x (bytesAt s₀.mem y 64)) ∧
      HoldsAt d s' ∧ Frame [⟨d, 64⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      ∀ r, ¬ Words r → s'.gpr r = s₀.gpr r := by
  let X : Vector Word 16 := Vector.ofFn fun j => wordLE x j.1
  let T := tWords X s₀.mem y
  have hX : ∀ k (hk : k < 16), lo (s₀.gpr (wreg k)) = X[k] := fun k hk => by
    rw [hx k hk]; simp only [X, Vector.getElem_ofFn]
  refine WP.seq (WP.mono (wp_range_flatMap (M := isa) (XI d X T s₀) (fun n s hn h => mix_step hp hn h)
    16 (Nat.le_refl _) s₀ ⟨fun j hj => ?_, fun _ _ h => absurd h (by omega_using []), Frame.refl _ _,
      rfl, rfl, fun _ _ => rfl⟩) fun s₁ h₁ => ?_)
  · rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero j)]; exact hX j hj
  have hT : Holds T s₁ := fun k hk => by
    rw [h₁.regs k hk, ite_eq_left_iff.mpr fun h => absurd hk h]
  refine WP.seq (WP.mono (rounds_ok hT 4) fun s₂ h₂ => ?_)
  refine WP.mono (wp_range_flatMap (M := isa) (FI d (Nat.repeat Spec.Scrypt.doubleRound 4 T) T s₀)
    (fun i s hi h => finish_step hp hi h) 16 (Nat.le_refl _) s₂ ⟨fun j hj => ?_, fun j hj => ?_, ?_,
      h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hw => (h₂.keep r hw).trans (h₁.keep r hw)⟩)
    fun s' h => ⟨?_, fun k hk => by
      rw [h.regs k hk, h.out k hk, ite_eq_left_iff.mpr fun e => absurd hk e,
        ite_eq_left_iff.mpr fun e => absurd hk e], h.frame, h.rd, h.wr, h.keep⟩
  · rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero j)]; exact h₂.holds j hj
  · rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero j), h₂.mem]; exact h₁.out j hj hj
  · rw [h₂.mem]; exact h₁.frame
  · have hi : (Vector.ofFn fun j : Fin 16 =>
        wordLE (Spec.Pbkdf2.xorBytes x (bytesAt s₀.mem y 64)) j.1) = T := by
      apply Vector.ext
      intro j hj
      rw [Vector.getElem_ofFn, wordLE_xor _ _ hl (by simp [bytesAt]) hj, wordLE_bytesAt _ _ (by omega_using [hj]),
        tWords_get _ _ _ hj]
      simp only [X, Vector.getElem_ofFn]
    rw [Spec.Scrypt.salsa, hi]
    refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
    rw [Spec.Scrypt.core, Vector.getElem_zipWith, h.out j hj, ite_eq_left_iff.mpr fun e => absurd hj e]

end VG.Proof.Scrypt.RISCV64

end

end

/-!
# scryptBlockMix on RISC-V

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Scrypt/PPC64LE/BlockMix.lean`), for both widths of the
accesses: the steps (`half_core`), the loop over the pairs (`Inv`), and the
registers saved in `save` (`Spill`). There is no stack frame and no call.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.BlockMix

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64 VG.WriteBytes
open VG.Spec.Scrypt (bytesAt blk salsa blockMix)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ blockMix_eq flatMap_congr)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt
  bytesAt_add bytesAt_blocks bytesAt_congr)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .a0
abbrev rr : Nat := (s₀.gpr .a1).toNat
abbrev yP : Addr := s₀.gpr .a2
abbrev sv : Addr := s₀.gpr .a3
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev svR : Region := ⟨sv s₀, 96⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k

/-- Our caller's `s0`–`s8` and `s10` are saved in `save`. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved (sv s₀) s₀.gpr bmSaved m

end

/-- The return address, and the callee-saved registers the code never writes. -/
def others : List Reg := [.ra, .s9, .s11]

structure Pre (wide : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, svR s₀]
  y_s : (yR s₀).Disjoint (svR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (svR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sv s₀).toNat + 96 ≤ 2 ^ 64
  pos : 0 < rr s₀
  s_al : (sv s₀).toNat % 8 = 0
  al : wide = true → (bP s₀).toNat % 8 = 0 ∧ (yP s₀).toNat % 8 = 0

theorem pre_of {wide : Bool} {s₀ : State} (h : (Proof.Scrypt.blockMixRISCV64 wide).pre s₀) :
    Pre wide s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- An offset that is a multiple of 8 of an address that is one. -/
theorem al8 {p : Addr} (hp : p.toNat % 8 = 0) {o : Nat} (ho : o % 8 = 0) :
    (p + BitVec.ofNat 64 o).toNat % 8 = 0 := Spill.al8 hp ho

section
variable {wide : Bool} {s₀ : State} (hp : Pre wide s₀)
include hp

/-- `y` is not the whole address space, since `save` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (sv s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
  simp only [Region.Contains]
  have := (sv s₀ - yP s₀).isLt
  omega_using [hc]

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_using [h]) (by have := r_lt hp; omega_using [h, this])

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_using [h]) (by have := r_lt hp; omega_using [h, this])

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega) (by omega) (by omega) (by omega)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega_using [h]) (by have := r_lt hp; omega_using [h, this])

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega_using [h]) (by have := r_lt hp; omega_using [h, this])

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (y_sub hp h₁)).sub_right (b_sub hp h₂)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 96) :
    (svR s₀).Contains (sv s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega_using [h])

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 96) :
    Region.Sub ⟨sv s₀ + BitVec.ofNat 64 o, n⟩ (svR s₀) :=
  sub_off h (by omega_using [h])

/-- The registers that are not `X`'s. -/
def ptrs : List Reg := [.s5, .s6, .s7, .s8, .s10, .ra, .s9, .s11]

theorem others_words : ∀ r ∈ ptrs, ¬ Words r := by
  obtain key : ∀ r ∈ ptrs, (∀ k < 16, r ≠ wreg k) ∧ r ≠ .t0 ∧ r ≠ .t1 := by decide
  exact fun r hr => not_words (key r hr).1 (key r hr).2.1 (key r hr).2.2

theorem others_ptr : ∀ r ∈ others, r ∈ ptrs := by decide

theorem others_ne : ∀ r ∈ others, r ≠ .s5 := by decide

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  s5 : s.gpr .s5 = bB s₀ k
  s6 : s.gpr .s6 = yE s₀ k
  s7 : s.gpr .s7 = yO s₀ k
  s10 : s.gpr .s10 = sv s₀
  s8 : s.gpr .s8 = BitVec.ofNat 64 (rr s₀ - k)
  xs : HoldsAt (xP s₀ k) s
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, svR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `save`. -/
theorem b_frame {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {m : Mem}
    (hf : Frame [yR s₀, svR s₀] s₀.mem m) {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega_using [ho, this])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega_using [hi])

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

/-! ## One pair -/

/-- Where `X` is. -/
theorem xP_in {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, svR s₀]) :
    ∀ i < 16, InRegions (s.rd ++ s.wr) (xP s₀ 0 + BitVec.ofNat 64 (4 * i)) 4 := by
  intro i hi
  rw [hrd, hwr]
  simp only [xP]
  rw [add_ofNat]
  exact InRegions.of_mem (by simp) (in_b hp (by have := hp.pos; omega_using [this, hi]))

/-- What a step keeps: our caller's saved registers. -/
theorem saved_keep {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {m m' : Mem} (hf : Frame [slot s₀ o] m m') (h : Saved s₀ m) : Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
  obtain hp8 : p.2 + 8 ≤ 96 := by revert p; decide
  obtain hsub : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (svR s₀) := s_sub s₀ hp8
  simp only [List.mem_singleton] at hr
  subst hr
  exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm

/-- What a step keeps: the other blocks of `y`. -/
theorem slot_keep {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega_using [])
  simp only [List.mem_singleton] at hr
  subst hr
  exact y_disj hp hd ho' ho (by omega_using []) (by omega_using [])

theorem frame_big {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {m m' : Mem} (hf : Frame [slot s₀ o] m m') : Frame [yR s₀, svR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩

/-- Half a pair: `X`, the block at `x`, becomes Salsa20/8 of `X xor B[i]`,
in the registers and at block `o` of `y`. -/
theorem half_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {dR : Reg}
    (hd : ¬ Words dR) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (ho8 : o % 8 = 0)
    {x : Addr} {ob : Nat} (hob : ob + 64 ≤ 128 * rr s₀) (hob8 : ob % 8 = 0) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, svR s₀])
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o)
    (gs : s.gpr .s5 = bP s₀ + BitVec.ofNat 64 ob) (hx : HoldsAt x s) :
    WP isa (half wide dR .s5) s fun s' =>
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)) ∧
      HoldsAt (yP s₀ + BitVec.ofNat 64 o) s' ∧
      Frame [slot s₀ o] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, ¬ Words r → s'.gpr r = s.gpr r := by
  obtain lt := r_lt hp
  refine half_core ⟨gd, gs, hd, others_words _ (by decide), yb_disj hp ho hob, fun k hk => ?_, fun k hk => ?_,
    fun hw => ?_, fun hw => ?_⟩ (bytesAt_length _ _ _) fun k hk => ?_
  · rw [hrd, hwr, add_ofNat]
    exact InRegions.of_mem (by simp) (in_b hp (by omega_using [hob, hk]))
  · rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega_using [ho, hk]))
  · have := al8 (hp.al hw).2 ho8; omega_using [this]
  · have := al8 (hp.al hw).1 hob8; omega_using [this]
  · rw [hx k hk, wordLE_bytesAt _ _ (by omega_using [hk])]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  s5 : s.gpr .s5 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  s6 : s.gpr .s6 = yE s₀ k
  s7 : s.gpr .s7 = yO s₀ k
  s10 : s.gpr .s10 = sv s₀
  s8 : s.gpr .s8 = BitVec.ofNat 64 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, svR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  xs : HoldsAt (yO s₀ k) s
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀)
    {s s₂ s₅ : State} (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k)] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k))] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, svR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  obtain lt := r_lt hp
  obtain oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_using [hk]
  obtain oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_using [hk]
  obtain F₂ := h.frame.trans (frame_big hp oE f₂)
  obtain yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega_using [hk] : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega_using [], ← blk_B s₀ (by omega_using [hk]), yAt_eq]
  obtain hb : bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega_using [hk])]
    exact b_frame hp F₂ (by omega_using [hk])
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega_using [hk]) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega_using [hi, hik]
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega_using [hk, hi]) (by omega_using [hk, hi]) f₅, slot_keep hp oE (by omega_using [hk, hi]) (by omega_using [hik]) f₂, d₁]
    · rw [slot_keep hp oO (by omega_using [hk, hi]) (by omega_using [hik]) f₅, slot_keep hp oE (by omega_using [hk, hi]) (by omega_using [hk]) f₂, d₂]

/-- Both halves of pair `k`. -/
theorem halves_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (half wide .s6 .s5) <| .seq (.block [.addi .s5 .s5 64]) <|
      .seq (half wide .s7 .s5) P) s Q := by
  obtain lt := r_lt hp
  obtain hrd : s.rd = [bR s₀] := by rw [h.rd, hp.rd]
  obtain hwr : s.wr = [yR s₀, svR s₀] := by rw [h.wr, hp.wr]
  obtain oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_using [hk]
  obtain oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_using [hk]
  refine WP.seq (WP.mono (half_ok hp (others_words _ (by decide)) oE (by omega_using []) (ob := 128 * k)
    (by omega_using [hk]) (by omega_using []) hrd hwr h.s6 h.s5 h.xs)
    fun s₂ ⟨b₂, x₂, f₂, rd₂, wr₂, k₂⟩ => ?_)
  refine WP.seq (wp_addi (by decide) fun s₃ u₃ => WP.block_nil ?_)
  obtain k3 : ∀ r, r ≠ .s5 → ¬ Words r → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h1, k₂ r h2]
  obtain e3 : s₃.gpr .s5 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, k₂ _ (others_words _ (by decide)), h.s5, add_ofNat, show 128 * k + 64 = 64 * (2 * k + 1) by omega_using []]
  obtain hrd₃ : s₃.rd = [bR s₀] := by rw [u₃.rd, rd₂, hrd]
  obtain hwr₃ : s₃.wr = [yR s₀, svR s₀] := by rw [u₃.wr, wr₂, hwr]
  obtain x₃ : HoldsAt (yE s₀ k) s₃ := fun j hj => by
    rw [u₃.other _ (Ne.symm (words_ne (others_words .s5 (by decide)) hj)), u₃.mem]; exact x₂ j hj
  refine WP.seq (WP.mono (half_ok hp (others_words _ (by decide)) oO (by omega_using []) (ob := 64 * (2 * k + 1))
    (by omega_using [hk]) (by omega_using []) hrd₃ hwr₃
    (by rw [k3 _ (by decide) (others_words _ (by decide)), h.s7]) e3 x₃)
    fun s₅ ⟨b₅, x₅, f₅, rd₅, wr₅, k₅⟩ => ?_)
  rw [u₃.mem] at f₅ b₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  obtain k5 : ∀ r, r ≠ .s5 → ¬ Words r → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [k₅ r h2, k3 r h1 h2]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [k₅ _ (others_words _ (by decide)), e3],
    by rw [k5 _ (by decide) (others_words _ (by decide)), h.s6],
    by rw [k5 _ (by decide) (others_words _ (by decide)), h.s7],
    by rw [k5 _ (by decide) (others_words _ (by decide)), h.s10],
    by rw [k5 _ (by decide) (others_words _ (by decide)), h.s8],
    fun r hr => by
      rw [k5 r (others_ne r hr) (others_words r (others_ptr r hr)), h.keep r hr],
    F, S, x₅, D⟩

theorem sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64 := by omega) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} {wide : Bool} (hp : Pre wide s₀) {k : Nat} (hk : k < rr s₀)
    {s : State} (h : Mid s₀ k s) :
    WP isa (.block [.addi .s5 .s5 64, .addi .s6 .s6 64, .addi .s7 .s7 64, .addi .s8 .s8 (-1)]) s
      (Inv s₀ (k + 1)) := by
  obtain lt := r_lt hp
  refine wp_addi (by decide) fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ =>
    wp_addi (by decide) fun s₉ u₉ => wp_subi (imm := 1) (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  obtain m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  obtain g : ∀ r, r ≠ .s5 → r ≠ .s6 → r ≠ .s7 → r ≠ .s8 → s₁₀.gpr r = s.gpr r :=
    fun r h4 h5 h6 h7 => by rw [u₁₀.other _ h7, u₉.other _ h6, u₈.other _ h5, u₇.other _ h4]
  refine ⟨(by omega_using [hk]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, h.wr]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      h.s5, add_ofNat, show 64 * (2 * k + 1) + 64 = 128 * (k + 1) by omega_using []]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      h.s6, add_ofNat, show 64 * k + 64 = 64 * (k + 1) by omega_using []]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      h.s7, add_ofNat, show 64 * (rr s₀ + k) + 64 = 64 * (rr s₀ + (k + 1)) by omega_using []]
  · rw [g _ (by decide) (by decide) (by decide) (by decide), h.s10]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      h.s8, sub_ofNat' (by omega_using [hk])]
    congr 1
  · intro j hj
    rw [g _ (Ne.symm (words_ne (others_words .s5 (by decide)) hj))
      (Ne.symm (words_ne (others_words .s6 (by decide)) hj))
      (Ne.symm (words_ne (others_words .s7 (by decide)) hj))
      (Ne.symm (words_ne (others_words .s8 (by decide)) hj)), m₁₀]
    exact h.xs j hj
  · intro r hr
    have : r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .s7 ∧ r ≠ .s8 := by
      revert r; decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega_using [])).2]
    rfl

theorem body_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) : WP isa (bmBody wide) s (Inv s₀ (k + 1)) :=
  halves_ok hp hk h fun _ hm => regs_ok hp hk hm

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sv s₀) s₀.gpr bmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved (by decide) _ _ _

theorem saveMem_frame (s₀ : State) : Frame [svR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem prologue_eq : bmPrologue = Spill.saveCode .a3 bmSaved ++
    ([mov .s8 .a1, mov .s5 .a0, mov .s6 .a2, mov .s10 .a3,
      .shift .sll .d .t1 .a1 6, .add .s7 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .t0 .a0 .t1, .addi .t0 .t0 (-64)] : List Instr) := rfl

theorem save_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (Spill.saveCode .a3 bmSaved ++ rest)) s₀ Q :=
  Spill.save_ok hp.s_al (by decide) (fun p hp' => by
    rw [hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    (k _ rfl rfl rfl rfl)

theorem shl_eq {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    x <<< n = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega_using [h], BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-- The registers the loop starts with. -/
theorem setup_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block ([mov .s8 .a1, mov .s5 .a0, mov .s6 .a2, mov .s10 .a3,
      .shift .sll .d .t1 .a1 6, .add .s7 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .t0 .a0 .t1, .addi .t0 .t0 (-64)] : List Instr)) s₁ fun s =>
      WP isa (.block (load wide .t0)) s (Inv s₀ 0) := by
  obtain lt : 128 * (s₀.gpr .a1).toNat < 2 ^ 64 := r_lt hp
  have pos := hp.pos
  refine wp_mv fun a ua => wp_mv fun b ub => wp_mv fun c uc => wp_mv fun d ud =>
    wp_sll (by decide) fun e ue => wp_add fun f uf => wp_sll (by decide) fun g' ug =>
    wp_add fun h uh => wp_subi (imm := 64) (by decide) fun i ui => WP.block_nil ?_
  obtain r1 : d.gpr .a1 = s₀.gpr .a1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  obtain e1 : e.gpr .t1 = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [ue.gpr, r1, shl_eq (by simp; omega_using [lt]), Nat.mul_comm]
  obtain g1 : g'.gpr .t1 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), r1, shl_eq (by simp; omega_using [lt]),
      Nat.mul_comm]
  obtain hm' : i.mem = saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  obtain k : ∀ r, r ≠ .t1 → r ≠ .s5 → r ≠ .s6 → r ≠ .s7 → r ≠ .s10 → r ≠ .s8 → r ≠ .t0 →
      i.gpr r = s₀.gpr r := fun r h1 h4 h5 h6 h9 h7 h8 => by
    rw [ui.other _ h8, uh.other _ h8, ug.other _ h1, uf.other _ h6, ue.other _ h1,
      ud.other _ h9, uc.other _ h5, ub.other _ h4, ua.other _ h7, g]
  obtain hrd' : i.rd = s₀.rd := by rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  obtain hwr' : i.wr = s₀.wr := by rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  obtain t0 : i.gpr .t0 = xP s₀ 0 := by
    rw [ui.gpr, uh.gpr, g1, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, add_sub64 _ (by omega_using [pos])]
    rfl
  refine WP.mono (load_ok t0 (fun hw => ?_) (xP_in hp (hrd'.trans hp.rd) (hwr'.trans hp.wr)))
    fun s ⟨xs, sm, srd, swr, sk⟩ => ?_
  · have := al8 (hp.al hw).1 (o := 128 * rr s₀ - 64) (by omega_using [])
    simp only [xP]
    omega_using [this]
  refine ⟨Nat.zero_le _, srd.trans hrd', swr.trans hwr', ?_, ?_, ?_, ?_, ?_, xs, ?_, ?_, ?_,
    fun i hi => absurd hi (by omega_using []), ?_⟩
  · rw [sk _ (others_words _ (by decide)), ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
    simp
  · rw [sk _ (others_words _ (by decide)), ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr,
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [sk _ (others_words _ (by decide)), ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e1,
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [sk _ (others_words _ (by decide)), ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [sk _ (others_words _ (by decide)), ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
    simp
  · intro r hr
    have : r ≠ .t1 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .s7 ∧ r ≠ .s10 ∧ r ≠ .s8 ∧ r ≠ .t0 := by
      revert r; decide
    obtain ⟨h1, h4, h5, h6, h9, h7, h8⟩ := this
    rw [sk r (others_words r (others_ptr r hr))]
    exact k r h1 h4 h5 h6 h9 h7 h8
  · rw [sm, hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [sm, hm']; exact saveMem_saved s₀
  · rw [sm, hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega_using [pos]), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega_using []]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega_using [])
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega_using [pos]))

/-! ## The loop -/

theorem loop_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody wide) (.nonzero .s8)) s (Inv s₀ (rr s₀)) := by
  obtain lt := r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hp hk hi) fun s' hi' => ?_
  obtain hz : isa.eval (.nonzero .s8) s' = some (decide (rr s₀ - (k + 1) ≠ 0)) :=
    eval_nonzero_ofNat s' .s8 (by omega_using [lt]) hi'.s8
  by_cases hl : rr s₀ - (k + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show k + 1 = rr s₀ by omega_using [hk, hl]] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], rr s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hl], hi'⟩

/-! ## The epilogue -/

theorem preserved_cases : ∀ r ∈ preserved, r ∈ bmSaved.map Prod.fst ∨ r ∈ others := by
  decide

theorem restore_ok {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra :=
  WP.mono (Spill.restore_wp (b := .s10) hp.s_al h.s10 (by decide) (by decide) (fun p hp' => by
      rw [h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    h.saved) fun s' h' => ⟨h'.mem, fun r hr =>
      h'.gpr_of ((preserved_cases r hr).imp id (h.keep r)), h'.gpr_of (.inr (h.keep _ (by decide)))⟩

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega_using [], bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem correct {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    WP isa (Impl.Scrypt.RISCV64.blockMix wide) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧
      bytesAt s'.mem (yP s₀) (128 * rr s₀) = Spec.Scrypt.blockMix (rr s₀) (B s₀) := by
  unfold Impl.Scrypt.RISCV64.blockMix
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hm => ?_
  refine WP.mono (setup_ok hp g hrd hwr hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono h₂ fun s₂' h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hg', hra⟩ => ⟨hg', hra, ?_⟩
  rw [hm']
  exact post_of fun i hi => h₃.done i hi

theorem blockMix_correct {wide : Bool} (s : State) (hs : (Proof.Scrypt.blockMixRISCV64 wide).pre s) :
    ∃ t s', Exec isa (Impl.Scrypt.RISCV64.blockMix wide) s t s' ∧ abiPreserved s s' ∧
      (Proof.Scrypt.blockMixRISCV64 wide).post s s' := by
  obtain ⟨t, s', he, hk, hra, hpost⟩ := correct (pre_of hs)
  exact ⟨t, s', he, ⟨hk, Exec.sp he, hra⟩, hpost⟩

theorem agree₀ {wide : Bool} {s₁ s₂ : State} (hpub : (Proof.Scrypt.blockMixRISCV64 wide).pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem blockMix_ct (wide : Bool) : ConstantTime isa (Proof.Scrypt.blockMixRISCV64 wide).pre
    (Proof.Scrypt.blockMixRISCV64 wide).pub (Impl.Scrypt.RISCV64.blockMix wide) := by
  cases wide
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data). -/
def bmSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 96⟩]

theorem blockMix_verified (wide : Bool) :
    Verified RISCV64.target (Impl.Scrypt.RISCV64.blockMix wide)
      (Proof.Scrypt.blockMixRISCV64 wide) :=
  ⟨blockMix_correct, blockMix_ct wide, ⟨bmSat, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide,
    by decide, by decide, by decide, fun _ => by decide⟩⟩

end VG.Proof.Scrypt.RISCV64.BlockMix
