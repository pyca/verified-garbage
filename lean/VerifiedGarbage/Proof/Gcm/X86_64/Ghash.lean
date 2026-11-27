module

import VerifiedGarbage.Proof.Gcm.X86_64.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.Contract
public import VerifiedGarbage.Impl.Gcm.X86_64
public import VerifiedGarbage.Proof.Gcm.Slots
public import VerifiedGarbage.Proof.Gcm.Spread
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Gcm.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# GHASH with integer multiplications on x86-64

Untrusted: everything here is checked by Lean. The blocks of the code but for
its loads of `H`, `Y` and the data are run on an abstract machine, the
registers and the 32 words of `scratch` (`A`, `evalA`), which the machine
follows (`sound`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64
open VG.Impl.Gcm.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-! ## The abstract machine -/

structure A where
  g : Reg → BitVec 64
  m : Nat → BitVec 64

namespace A

def set (a : A) (d : Reg) (v : BitVec 64) : A := ⟨fun r => if r = d then v else a.g r, a.m⟩
def put (a : A) (k : Nat) (v : BitVec 64) : A := ⟨a.g, fun j => if j = k then v else a.m j⟩

theorem g_set (a : A) (d : Reg) (v : BitVec 64) (r : Reg) : (a.set d v).g r = if r = d then v else a.g r := rfl
theorem m_set (a : A) (d : Reg) (v : BitVec 64) : (a.set d v).m = a.m := rfl
theorem g_put (a : A) (k : Nat) (v : BitVec 64) : (a.put k v).g = a.g := rfl
theorem m_put (a : A) (k : Nat) (v : BitVec 64) (j : Nat) : (a.put k v).m j = if j = k then v else a.m j := rfl

end A

/-- The word of `scratch` an operand is. -/
def slotOf (m : MemOp) : Option Nat :=
  if m.base = .r8 ∧ m.index = none ∧ m.disp.toNat % 8 = 0 ∧ m.disp.toNat < 256 ∧ 0 ≤ m.disp then
    some (m.disp.toNat / 8) else none

theorem slotOf_slot {k : Nat} (hk : k < 32) : slotOf (slot k) = some k := by
  simp only [slotOf, slot]
  rw [ite_eq_left ⟨trivial, trivial, by rw [Int.toNat_natCast]; omega, by rw [Int.toNat_natCast]; omega, Int.natCast_nonneg _⟩,
    Int.toNat_natCast, Nat.mul_div_cancel_left k (by decide)]

theorem ea_slotOf {m : MemOp} {k : Nat} (h : slotOf m = some k) (s : State) :
    k < 32 ∧ s.ea m = s.gpr .r8 + BitVec.ofNat 64 (8 * k) := by
  simp only [slotOf] at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    cases h
    refine ⟨by omega, ?_⟩
    have hd : m.disp = ((8 * (m.disp.toNat / 8) : Nat) : Int) := by omega
    simp only [State.ea, h1, h2]
    conv_lhs => rw [hd, BitVec.ofInt_natCast]
  · cases h

def srcA (a : A) : Src → Option (BitVec 64)
  | .reg r => some (a.g r)
  | .imm _ => none
  | .mem m => (slotOf m).map a.m

def stepA : Instr → A → Option A
  | .mov d s, a => if d = .r8 then none else (srcA a s).map (a.set d)
  | .alu .xor d s, a => if d = .r8 then none else (srcA a s).map fun v => a.set d (a.g d ^^^ v)
  | .alu .and d s, a => if d = .r8 then none else (srcA a s).map fun v => a.set d (a.g d &&& v)
  | .movImm64 d v, a => if d = .r8 then none else some (a.set d v)
  | .bswap d, a => if d = .r8 then none else some (a.set d (bswap64 (a.g d)))
  | .shift .shl d n, a => if d = .r8 ∨ ¬ (1 ≤ n ∧ n ≤ 63) then none else some (a.set d (a.g d <<< n))
  | .shift .shr d n, a => if d = .r8 ∨ ¬ (1 ≤ n ∧ n ≤ 63) then none else some (a.set d (a.g d >>> n))
  | .mul r, a =>
    let p := (a.g .rax).toNat * (a.g r).toNat
    some ((a.set .rax (BitVec.ofNat 64 p)).set .rdx (BitVec.ofNat 64 (p / 2 ^ 64)))
  | .store m r, a => (slotOf m).map fun k => a.put k (a.g r)
  | _, _ => none

def evalA : List Instr → A → Option A
  | [], a => some a
  | i :: is, a => (stepA i a).bind (evalA is)

theorem evalA_append (l₁ l₂ : List Instr) (a : A) : evalA (l₁ ++ l₂) a = (evalA l₁ a).bind (evalA l₂) := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, evalA, Option.bind_assoc]
    exact congrArg _ (funext fun a' => ih a')

/-- What the machine's state is to the abstract one's: `s₀` is the state at
entry, whose memory outside `scratch` is unchanged. -/
structure Rel (s₀ : State) (s : State) (a : A) : Prop where
  g : s.gpr = a.g
  m : Slots s₀.mem s.mem (s₀.gpr .r8) 32 a.m
  r8 : a.g .r8 = s₀.gpr .r8
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

namespace Rel

variable {s₀ s : State} {a : A}

theorem set (h : Rel s₀ s a) {d : Reg} (hd : d ≠ .r8) (v : BitVec 64) : Rel s₀ (s.setReg d v) (a.set d v) :=
  ⟨by funext r; show (if r = d then v else s.gpr r) = _; rw [h.g]; rfl, h.m, by rw [A.g_set, ite_eq_right (Ne.symm hd)]; exact h.r8, h.rd, h.wr⟩

theorem flags (h : Rel s₀ s a) (c o z f : Option Bool) : Rel s₀ (s.setFlags c o z f) a := ⟨h.g, h.m, h.r8, h.rd, h.wr⟩

theorem in_slot (h : Rel s₀ s a) (hw : (⟨s₀.gpr .r8, 256⟩ : Region) ∈ s₀.wr) {k : Nat} (hk : k < 32) :
    InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨_, by rw [h.wr]; exact hw, by rw [h.g, h.r8]; exact Slots.contains (n := 32) _ hk (by decide)⟩

theorem src (h : Rel s₀ s a) (hw : (⟨s₀.gpr .r8, 256⟩ : Region) ∈ s₀.wr) {o : Src} {v : BitVec 64}
    (hv : srcA a o = some v) : readSrc s o = some v := by
  cases o with
  | reg r => rw [← hv]; simp only [readSrc, srcA, h.g]
  | imm _ => cases hv
  | mem m =>
    simp only [srcA, Option.map_eq_some_iff] at hv
    obtain ⟨k, hk, hv⟩ := hv
    obtain ⟨hk, he⟩ := ea_slotOf hk s
    obtain ⟨r, hr, hc⟩ := h.in_slot hw hk
    rw [readSrc, State.load64, he, ite_eq_left ⟨r, List.mem_append_right _ hr, hc⟩, ← hv, h.g, h.r8, h.m.get k hk]

end Rel

theorem step_sound {s₀ s : State} {a a' : A} (h : Rel s₀ s a) (hw : (⟨s₀.gpr .r8, 256⟩ : Region) ∈ s₀.wr)
    (i : Instr) (hi : stepA i a = some a') : ∃ s', exec i s = some s' ∧ Rel s₀ s' a' := by
  unfold stepA at hi
  split at hi
  · split at hi
    · cases hi
    · rename_i hd
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨v, hv, rfl⟩ := hi
      exact ⟨_, by rw [show exec _ s = (readSrc s _).map _ from rfl, h.src hw hv]; rfl, h.set hd v⟩
  · split at hi
    · cases hi
    · rename_i hd
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨v, hv, rfl⟩ := hi
      refine ⟨_, by rw [show exec _ s = (readSrc s _).bind _ from rfl, h.src hw hv]; rfl, ?_⟩
      rw [h.g]
      exact (h.flags ..).set hd _
  · split at hi
    · cases hi
    · rename_i hd
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨v, hv, rfl⟩ := hi
      refine ⟨_, by rw [show exec _ s = (readSrc s _).bind _ from rfl, h.src hw hv]; rfl, ?_⟩
      rw [h.g]
      exact (h.flags ..).set hd _
  · split at hi
    · cases hi
    · rename_i hd; cases hi; exact ⟨_, rfl, h.set hd _⟩
  · split at hi
    · cases hi
    · rename_i hd; cases hi; refine ⟨_, rfl, ?_⟩; rw [h.g]; exact h.set hd _
  · split at hi
    · cases hi
    · rename_i hd; cases hi
      obtain ⟨hd, hn⟩ := not_or.mp hd
      refine ⟨_, (ite_eq_left (Classical.not_not.mp hn)), ?_⟩
      show Rel s₀ (State.setReg _ _ _) _
      rw [h.g]; exact (h.flags ..).set hd _
  · split at hi
    · cases hi
    · rename_i hd; cases hi
      obtain ⟨hd, hn⟩ := not_or.mp hd
      refine ⟨_, (ite_eq_left (Classical.not_not.mp hn)), ?_⟩
      show Rel s₀ (State.setReg _ _ _) _
      rw [h.g]; exact (h.flags ..).set hd _
  · cases hi
    refine ⟨_, rfl, ?_⟩
    simp only [execMul, h.g]
    exact ((h.flags ..).set (by decide) _).set (by decide) _
  · simp only [Option.map_eq_some_iff] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    obtain ⟨hk, he⟩ := ea_slotOf hk s
    refine ⟨_, by rw [show exec _ s = State.store64 _ _ _ from rfl, State.store64, he, ite_eq_left (h.in_slot hw hk)], ?_⟩
    refine ⟨h.g, ?_, h.r8, h.rd, h.wr⟩
    simp only [h.g, h.r8]
    exact h.m.store hk (by decide) _
  · cases hi

/-- The machine runs what the abstract machine runs. -/
theorem sound {s₀ : State} (hw : (⟨s₀.gpr .r8, 256⟩ : Region) ∈ s₀.wr) {is : List Instr} {s : State} {a a' : A}
    (h : Rel s₀ s a) (he : evalA is a = some a') : WP isa (.block is) s fun s' => Rel s₀ s' a' := by
  induction is generalizing s a with
  | nil => cases he; exact WP.block_nil h
  | cons i is ih =>
    simp only [evalA, Option.bind_eq_some_iff] at he
    obtain ⟨a₁, h₁, h₂⟩ := he
    obtain ⟨s₁, e, r⟩ := step_sound h hw i h₁
    exact WP.block_cons_iff.mpr ⟨s₁, e, ih r h₂⟩

/-! ## Running blocks -/

def WA (is : List Instr) (a : A) (Q : A → Prop) : Prop := ∃ a', evalA is a = some a' ∧ Q a'

theorem WA.append {l₁ l₂ : List Instr} {a : A} {Q : A → Prop} (h : WA l₁ a fun a' => WA l₂ a' Q) :
    WA (l₁ ++ l₂) a Q := by
  obtain ⟨a₁, e₁, a₂, e₂, q⟩ := h
  exact ⟨a₂, by rw [evalA_append, e₁]; exact e₂, q⟩

theorem WA.mono {l : List Instr} {a : A} {Q R : A → Prop} (h : WA l a Q) (hq : ∀ a', Q a' → R a') : WA l a R := by
  obtain ⟨a', e, q⟩ := h; exact ⟨a', e, hq a' q⟩

/-- Registers other than `rs` are unchanged. -/
def Keeps (rs : List Reg) (a a' : A) : Prop := ∀ r, r ∉ rs → a'.g r = a.g r

theorem Keeps.trans {rs : List Reg} {a b c : A} (h₁ : Keeps rs a b) (h₂ : Keeps rs b c) : Keeps rs a c :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem Keeps.mono {rs rs' : List Reg} {a b : A} (h : Keeps rs a b) (hs : ∀ r ∈ rs, r ∈ rs') : Keeps rs' a b :=
  fun r hr => h r fun h' => hr (hs r h')

open Spread (m5 M5 cp meet mul5 mul5_eq up dn keyW0 keyW1 redW mulW)
open VG.Proof.Gcm.Clmul (vdword vdword_xor)

theorem mask_eq (r : Nat) : mask r = m5 r := by
  unfold mask m5; rfl

/-- `mul`'s result. -/
theorem mul_append (x y : BitVec 64) :
    BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) ++ BitVec.ofNat 64 (x.toNat * y.toNat) =
      x.setWidth 128 * y.setWidth 128 := by
  have hp : x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' x.isLt y.isLt
  apply BitVec.eq_of_toNat_eq
  rw [toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show x.toNat < 2 ^ 128 by have := x.isLt; omega),
    Nat.mod_eq_of_lt (show y.toNat < 2 ^ 128 by have := y.isLt; omega)]
  generalize x.toNat * y.toNat = p at hp ⊢
  omega

theorem part_ok (t i j : Nat) (hk : 5 * t + j < 32) (hi : i < 5) (a : A) :
    WA (part t i j) a fun a' =>
      a'.g .r10 ++ a'.g .r9 = (a.g .r10 ++ a.g .r9) ^^^ ((a.g (cls i)).setWidth 128 * (a.m (5 * t + j)).setWidth 128) ∧
      Keeps [.rax, .rdx, .r9, .r10] a a' ∧ a'.m = a.m := by
  have hc : ∀ i < 5, cls i ≠ .rax ∧ cls i ≠ .rdx := by decide
  obtain ⟨h1, h2⟩ := hc i hi
  simp only [WA, part, xorR, evalA, stepA, srcA, slotOf_slot hk, Option.map_some, Option.bind_some, A.g_set,
    reduceCtorEq, h1, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl⟩
  · rw [BitVec.mul_comm, ← mul_append, BitVec.xor_append]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem cls0 : cls 0 = .rcx := rfl
theorem cls1 : cls 1 = .rbx := rfl
theorem cls2 : cls 2 = .rbp := rfl
theorem cls3 : cls 3 = .r12 := rfl
theorem cls4 : cls 4 = .r13 := rfl

theorem split_ok (k : Nat) (hk : k < 32) (a : A) :
    WA (split k) a fun a' => (∀ i < 5, a'.g (cls i) = a.m k &&& m5 i) ∧
      Keeps [.rcx, .rbx, .rbp, .r12, .r13] a a' ∧ a'.m = a.m := by
  simp only [WA, split, split1, cls0, cls1, cls2, cls3, cls4, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, evalA, stepA, srcA, slotOf_slot hk, Option.map_some, Option.bind_some, A.g_set,
    A.m_set, reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, trivial⟩
  · have h : ∀ i, i < 5 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    intro i hi
    rcases h i hi with rfl | rfl | rfl | rfl | rfl <;>
      simp only [cls, reduceCtorEq, ite_false, ite_true, mask_eq, BitVec.and_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

/-- What `classSum` adds. -/
theorem classSum_ok (t r : Nat) (ht : t < 3) (w kw : BitVec 64) {a : A}
    (hC : ∀ i < 5, a.g (cls i) = w &&& m5 i) (hK : ∀ j < 5, a.m (5 * t + j) = kw &&& m5 j) :
    WA (classSum t r) a fun a' =>
      a'.g .r14 ++ a'.g .r11 = (a.g .r14 ++ a.g .r11) ^^^ (meet w kw r &&& M5 r) ∧
      Keeps [.rax, .rdx, .r9, .r10, .r11, .r14] a a' ∧ a'.m = a.m := by
  have hcls : ∀ i < 5, cls i ∉ [Reg.rax, .rdx, .r9, .r10] := by decide
  have hb : ∀ j < 5, 5 * t + j < 32 := by omega
  rw [classSum, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  have hz : WA [xorR .r9 .r9, xorR .r10 .r10] a fun a' => a'.g .r10 ++ a'.g .r9 = 0#128 ∧
      Keeps [.rax, .rdx, .r9, .r10] a a' ∧ a'.m = a.m := by
    refine ⟨_, rfl, ?_, fun r hr => ?_, rfl⟩
    · simp only [A.g_set, reduceCtorEq, ite_false, ite_true, BitVec.xor_self]; decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [A.g_set, hr, ite_false]
  have hP : ∀ (i j : Nat), i < 5 → j < 5 → ∀ b : A, Keeps [.rax, .rdx, .r9, .r10] a b → b.m = a.m →
      WA (part t i j) b fun b' => b'.g .r10 ++ b'.g .r9 = (b.g .r10 ++ b.g .r9) ^^^ cp w kw i j ∧
        Keeps [.rax, .rdx, .r9, .r10] a b' ∧ b'.m = a.m := by
    intro i j hi hj b hkb hmb
    refine (part_ok t i j (hb j hj) hi b).mono fun b' ⟨e, k', m'⟩ => ⟨?_, hkb.trans k', m'.trans hmb⟩
    rw [e, hkb _ (hcls i hi), hC i hi, hmb, hK j hj, cp]
  refine WA.append (hz.mono fun a₀ ⟨e₀, k₀, m₀⟩ => ?_)
  refine WA.append ((hP 0 _ (by decide) (Nat.mod_lt _ (by decide)) a₀ k₀ m₀).mono fun a₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WA.append ((hP 1 _ (by decide) (Nat.mod_lt _ (by decide)) a₁ k₁ m₁).mono fun a₂ ⟨e₂, k₂, m₂⟩ => ?_)
  refine WA.append ((hP 2 _ (by decide) (Nat.mod_lt _ (by decide)) a₂ k₂ m₂).mono fun a₃ ⟨e₃, k₃, m₃⟩ => ?_)
  refine WA.append ((hP 3 _ (by decide) (Nat.mod_lt _ (by decide)) a₃ k₃ m₃).mono fun a₄ ⟨e₄, k₄, m₄⟩ => ?_)
  refine WA.append ((hP 4 _ (by decide) (Nat.mod_lt _ (by decide)) a₄ k₄ m₄).mono fun a₅ ⟨e₅, k₅, m₅⟩ => ?_)
  have he : a₅.g .r10 ++ a₅.g .r9 = meet w kw r := by
    rw [e₅, e₄, e₃, e₂, e₁, e₀, BitVec.zero_xor, meet]
  refine ⟨_, rfl, ?_, fun q hq => ?_, m₅⟩
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true, mask_eq]
    rw [← he, M5, BitVec.and_append, ← k₅ .r14 (by decide), ← k₅ .r11 (by decide), BitVec.xor_append]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]
    exact k₅ q (by simp [hq])

theorem mul_ok (k t : Nat) (hk : k < 32) (ht : t < 3) (kw : BitVec 64) {a : A}
    (hK : ∀ j < 5, a.m (5 * t + j) = kw &&& m5 j) :
    WA (mul k t) a fun a' => a'.g .r14 ++ a'.g .r11 = VectorCrypto.polyMul (a.m k) kw ∧
      Keeps [.rax, .rdx, .r9, .r10, .r11, .r14, .rcx, .rbx, .rbp, .r12, .r13] a a' ∧ a'.m = a.m := by
  have hcls : ∀ i < 5, cls i ∉ [Reg.rax, .rdx, .r9, .r10, .r11, .r14] := by decide
  rw [mul, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append ((split_ok k hk a).mono fun a₀ ⟨c₀, k₀, m₀⟩ => ?_)
  have hz : WA [xorR .r11 .r11, xorR .r14 .r14] a₀ fun a' => a'.g .r14 ++ a'.g .r11 = 0#128 ∧
      Keeps [.rax, .rdx, .r9, .r10, .r11, .r14] a₀ a' ∧ a'.m = a₀.m := by
    refine ⟨_, rfl, ?_, fun r hr => ?_, rfl⟩
    · simp only [A.g_set, reduceCtorEq, ite_false, ite_true, BitVec.xor_self]; decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [A.g_set, hr, ite_false]
  have hS : ∀ r < 5, ∀ b : A, Keeps [.rax, .rdx, .r9, .r10, .r11, .r14] a₀ b → b.m = a₀.m →
      WA (classSum t r) b fun b' =>
        b'.g .r14 ++ b'.g .r11 = (b.g .r14 ++ b.g .r11) ^^^ (meet (a.m k) kw r &&& M5 r) ∧
        Keeps [.rax, .rdx, .r9, .r10, .r11, .r14] a₀ b' ∧ b'.m = a₀.m := by
    intro r hr b hkb hmb
    refine (classSum_ok t r ht (a.m k) kw (fun i hi => by rw [hkb _ (hcls i hi), c₀ i hi])
      (fun j hj => by rw [hmb, m₀, hK j hj])).mono fun b' ⟨e, k', m'⟩ => ⟨e, hkb.trans k', m'.trans hmb⟩
  refine WA.append (hz.mono fun a₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WA.append ((hS 0 (by decide) a₁ k₁ m₁).mono fun a₂ ⟨e₂, k₂, m₂⟩ => ?_)
  refine WA.append ((hS 1 (by decide) a₂ k₂ m₂).mono fun a₃ ⟨e₃, k₃, m₃⟩ => ?_)
  refine WA.append ((hS 2 (by decide) a₃ k₃ m₃).mono fun a₄ ⟨e₄, k₄, m₄⟩ => ?_)
  refine WA.append ((hS 3 (by decide) a₄ k₄ m₄).mono fun a₅ ⟨e₅, k₅, m₅⟩ => ?_)
  refine (hS 4 (by decide) a₅ k₅ m₅).mono fun a₆ ⟨e₆, k₆, m₆⟩ => ⟨?_, ?_, m₆.trans m₀⟩
  · rw [e₆, e₅, e₄, e₃, e₂, e₁, BitVec.zero_xor, ← mul5_eq, mul5]
  · exact (k₀.mono (by decide)).trans (k₆.mono (by decide))

/-! ## The key and the reduction -/

theorem xor_rev (d a b c : BitVec 64) : d ^^^ a ^^^ b ^^^ c = d ^^^ (c ^^^ b ^^^ a) := by ac_rfl

/-- The fold of `s` down, through `r9`. -/
theorem foldDn_ok (d q : Reg) (hd : d ≠ .r8) (hd9 : d ≠ .r9) (hdq : q ≠ d) (a : A) :
    WA (foldDn d q) a fun a' => a'.g d = a.g d ^^^ dn (a.g q) ∧ Keeps [d, .r9] a a' ∧ a'.m = a.m := by
  have hdq' : ¬ d = q := fun e => hdq e.symm
  have e1 : ∀ v : BitVec 64, v <<< 57 <<< 5 = v <<< 62 := fun v => (BitVec.shiftLeft_add v 57 5).symm
  have e2 : ∀ v : BitVec 64, v <<< 62 <<< 1 = v <<< 63 := fun v => (BitVec.shiftLeft_add v 62 1).symm
  simp (config := {decide := true}) only [WA, foldDn, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some,
    A.g_set, hd, hd9, hd9.symm, ite_false, ite_true, Option.some.injEq, exists_eq_left', e1, e2]
  refine ⟨?_, fun r hr => ?_, rfl⟩
  · rw [dn, xor_rev]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem foldUp_ok (d q : Reg) (hd : d ≠ .r8) (hd9 : d ≠ .r9) (a : A) :
    WA (foldUp d q) a fun a' => a'.g d = a.g d ^^^ up (a.g q) ∧ Keeps [d, .r9] a a' ∧ a'.m = a.m := by
  have e1 : ∀ v : BitVec 64, v >>> 1 >>> 1 = v >>> 2 := fun v => (BitVec.shiftRight_add v 1 1).symm
  have e2 : ∀ v : BitVec 64, v >>> 2 >>> 5 = v >>> 7 := fun v => (BitVec.shiftRight_add v 2 5).symm
  simp (config := {decide := true}) only [WA, foldUp, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some,
    A.g_set, hd, hd9, hd9.symm, ite_false, ite_true, Option.some.injEq, exists_eq_left', e1, e2]
  refine ⟨?_, fun r hr => ?_, rfl⟩
  · rw [up, BitVec.xor_assoc, BitVec.xor_assoc, BitVec.xor_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem adjust_ok (a : A) :
    WA adjust a fun a' =>
      a'.g .r9 = keyW1 (bswap64 (a.g .r9)) (bswap64 (a.g .r10)) ∧
      a'.g .r10 = keyW0 (bswap64 (a.g .r9)) (bswap64 (a.g .r10)) ∧
      a'.g .r11 = a'.g .r9 ^^^ a'.g .r10 ∧ Keeps [.r9, .r10, .r11, .r14] a a' ∧ a'.m = a.m := by
  have e1 : ∀ v : BitVec 64, v <<< 57 <<< 5 = v <<< 62 := fun v => (BitVec.shiftLeft_add v 57 5).symm
  have e2 : ∀ v : BitVec 64, v <<< 62 <<< 1 = v <<< 63 := fun v => (BitVec.shiftLeft_add v 62 1).symm
  simp (config := {decide := true}) only [WA, adjust, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some,
    A.g_set, ite_false, ite_true, Option.some.injEq, exists_eq_left', e1, e2]
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl⟩
  · rw [keyW1, dn, xor_rev]
  · rw [keyW0]
  · trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem keyClass_ok (t : Nat) (r : Reg) (j : Nat) (hr : r ≠ .rax) (hk : 5 * t + j < 32) (a : A) :
    WA (keyClass t r j) a fun a' => a'.m (5 * t + j) = a.g r &&& m5 j ∧
      (∀ k, k ≠ 5 * t + j → a'.m k = a.m k) ∧ Keeps [.rax] a a' := by
  simp only [WA, keyClass, evalA, stepA, srcA, slotOf_slot hk, Option.map_some, Option.bind_some, A.g_set, A.m_put,
    A.m_set, hr, reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left', mask_eq]
  refine ⟨BitVec.and_comm _ _, fun k hk' => by simp only [hk', ite_false], fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [A.g_put, A.g_set, hq, ite_false]

theorem keyWord_ok (t : Nat) (r : Reg) (hr : r ≠ .rax) (ht : t < 3) (a : A) :
    WA (keyWord t r) a fun a' => (∀ j < 5, a'.m (5 * t + j) = a.g r &&& m5 j) ∧
      (∀ k, k < 5 * t ∨ 5 * t + 5 ≤ k → a'.m k = a.m k) ∧ Keeps [.rax] a a' := by
  have hr' : r ∉ [Reg.rax] := by simp [hr]
  have h : ∀ n ≤ 5, WA ((List.range n).flatMap (keyClass t r)) a fun a' =>
      (∀ j < n, a'.m (5 * t + j) = a.g r &&& m5 j) ∧
      (∀ k, k < 5 * t ∨ 5 * t + 5 ≤ k → a'.m k = a.m k) ∧ Keeps [.rax] a a' := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨a, rfl, fun _ h => absurd h (by omega), fun _ _ => rfl, fun _ _ => rfl⟩
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine WA.append ((ih (by omega)).mono fun b ⟨h1, h2, h3⟩ => ?_)
      refine (keyClass_ok t r n hr (by omega) b).mono fun c ⟨g1, g2, g3⟩ => ⟨fun j hj => ?_, fun k hk => ?_, h3.trans g3⟩
      · by_cases e : j = n
        · subst e; rw [g1, h3 r hr']
        · rw [g2 _ (by omega), h1 j (by omega)]
      · rw [g2 k (by omega), h2 k hk]
  exact h 5 (Nat.le_refl 5)

theorem xor_mid (c l1 h1 h0 l0 u v : BitVec 64) :
    c ^^^ l1 ^^^ h1 ^^^ h0 ^^^ l0 ^^^ u ^^^ v = h0 ^^^ (c ^^^ l1 ^^^ h1) ^^^ l0 ^^^ u ^^^ v := by ac_rfl

theorem reduce_ok {a : A} {l h c : BitVec 128} (hl0 : a.m lS = vdword l 0) (hl1 : a.m (lS + 1) = vdword l 1)
    (hh0 : a.m hS = vdword h 0) (hh1 : a.m (hS + 1) = vdword h 1) (hc0 : a.g .r11 = vdword c 0)
    (hc1 : a.g .r14 = vdword c 1) :
    WA reduce a fun a' => a'.m y1S = (redW l h c).1 ∧ a'.m y0S = (redW l h c).2 ∧
      (∀ k, k ≠ y1S → k ≠ y0S → a'.m k = a.m k) ∧ Keeps [.rax, .rdx, .rcx, .rbx, .r9, .r11, .r14] a a' := by
  rw [reduce, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append (WA.mono (Q := fun b => b.g .rax = vdword l 0 ∧ b.g .rcx = vdword h 0 ∧ b.g .rbx = vdword h 1 ∧
      b.g .r11 = vdword c 0 ^^^ vdword l 0 ^^^ vdword h 0 ^^^ vdword l 1 ∧
      b.g .r14 = vdword c 1 ^^^ vdword l 1 ^^^ vdword h 1 ^^^ vdword h 0 ^^^ vdword l 0 ∧
      Keeps [.rax, .rdx, .rcx, .rbx, .r9, .r11, .r14] a b ∧ b.m = a.m) ?_ fun b ⟨hax, hcx, hbx, h11, h14, kb, mb⟩ => ?_)
  · simp (config := {decide := true}) only [WA, xorR, evalA, stepA, srcA, slotOf_slot, Option.map_some, Option.bind_some,
      A.g_set, A.m_set, ite_false, ite_true, Option.some.injEq, exists_eq_left', hl0, hl1, hh0, hh1, hc0, hc1]
    refine ⟨trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [A.g_set, hr, ite_false]
  · refine WA.append ((foldDn_ok .r11 .rax (by decide) (by decide) (by decide) b).mono fun b₁ ⟨e₁, k₁, m₁⟩ => ?_)
    refine WA.append ((foldUp_ok .r14 .rax (by decide) (by decide) b₁).mono fun b₂ ⟨e₂, k₂, m₂⟩ => ?_)
    refine WA.append (WA.mono (Q := fun b' => b'.g .rbx = b₂.g .rbx ^^^ b₂.g .r11 ∧ Keeps [.rbx] b₂ b' ∧ b'.m = b₂.m)
      ⟨_, rfl, rfl, fun r hr => by
        rw [A.g_set, ite_eq_right (fun e => hr (by simp [e]))], rfl⟩ fun b₃ ⟨e₃, k₃, m₃⟩ => ?_)
    refine WA.append ((foldUp_ok .rbx .r11 (by decide) (by decide) b₃).mono fun b₄ ⟨e₄, k₄, m₄⟩ => ?_)
    refine WA.append ((foldDn_ok .r14 .r11 (by decide) (by decide) (by decide) b₄).mono fun b₅ ⟨e₅, k₅, m₅⟩ => ?_)
    have hu : b₁.g .r11 = vdword (c ^^^ l ^^^ h) 0 ^^^ vdword l 1 ^^^ dn (vdword l 0) := by
      rw [e₁, h11, hax, vdword_xor, vdword_xor]
    have h1 : b₅.g .rbx = (redW l h c).1 := by
      rw [k₅ _ (by decide), e₄, e₃, k₃ .r11 (by decide), k₂ .r11 (by decide), k₂ .rbx (by decide),
        k₁ .rbx (by decide), hbx, hu, redW]
    have h2 : b₅.g .r14 = (redW l h c).2 := by
      rw [e₅, k₄ .r14 (by decide), k₄ .r11 (by decide), k₃ .r14 (by decide), k₃ .r11 (by decide), e₂,
        k₂ .r11 (by decide), k₁ .r14 (by decide), k₁ .rax (by decide), hax, hu, h14, redW, vdword_xor _ _ 1,
        vdword_xor _ _ 1, xor_mid]
    have hm : b₅.m = a.m := by rw [m₅, m₄, m₃, m₂, m₁, mb]
    refine ⟨_, rfl, ?_, ?_, fun k hk1 hk0 => ?_, fun r hr => ?_⟩
    · show (A.put (A.put b₅ 25 _) 26 _).m 25 = _
      rw [A.m_put, A.m_put]; exact h1
    · show (A.put (A.put b₅ 25 _) 26 _).m 26 = _
      rw [A.m_put]; exact h2
    · show (A.put (A.put b₅ 25 _) 26 _).m k = _
      exact (ite_eq_right hk0).trans ((ite_eq_right hk1).trans (congrFun hm k))
    · show b₅.g r = _
      rw [(k₅.mono (by decide) : Keeps [.rax, .rdx, .rcx, .rbx, .r9, .r11, .r14] b₄ b₅) r hr,
        (k₄.mono (by decide) : Keeps [.rax, .rdx, .rcx, .rbx, .r9, .r11, .r14] b₃ b₄) r hr,
        (k₃.mono (by decide) : Keeps [.rax, .rdx, .rcx, .rbx, .r9, .r11, .r14] b₂ b₃) r hr,
        (k₂.mono (by decide) : Keeps [.rax, .rdx, .rcx, .rbx, .r9, .r11, .r14] b₁ b₂) r hr,
        (k₁.mono (by decide) : Keeps [.rax, .rdx, .rcx, .rbx, .r9, .r11, .r14] b b₁) r hr, kb r hr]

/-! ## The whole function -/

section
variable (s₀ : State)

abbrev hA : Addr := s₀.gpr .rdi
abbrev yp : Addr := s₀.gpr .rsi
abbrev dp : Addr := s₀.gpr .rdx
abbrev nb : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 256⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)

/-- The words of `H`. -/
abbrev h1 : BitVec 64 := bswap64 (s₀.mem.readW (hA s₀ + BitVec.ofNat 64 0) 64)
abbrev h0 : BitVec 64 := bswap64 (s₀.mem.readW (hA s₀ + BitVec.ofNat 64 8) 64)

/-- The words of the key. -/
def kw (t : Nat) : BitVec 64 :=
  match t with
  | 0 => keyW0 (h1 s₀) (h0 s₀)
  | 1 => keyW1 (h1 s₀) (h0 s₀)
  | _ => keyW0 (h1 s₀) (h0 s₀) ^^^ keyW1 (h1 s₀) (h0 s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_s : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_s : (yR s₀).Disjoint (scrR s₀)
  d_s : (dR s₀).Disjoint (scrR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_s : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : ghashX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h4, h5, h6, h7, h8, h9⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, zero_add, Nat.one_le_ofNat]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega

theorem mem_s : (⟨s₀.gpr .r8, 256⟩ : Region) ∈ s₀.wr := by rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem mem_h : hR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.rd]; exact List.mem_cons_self ..
theorem mem_d : dR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.rd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem mem_y : yR s₀ ∈ s₀.rd ++ s₀.wr := by
  rw [h.wr]; exact List.mem_append_right _ (List.mem_cons_self ..)

end Pre

/-- A load from a region disjoint from `scratch`. -/
theorem ext_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {d b : Reg} (hd : d ≠ .r8) (o : Nat) {R : Region} {p : Addr}
    (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (scrR s₀)) (hp : a.g b + BitVec.ofNat 64 o = p) (hc : R.Contains p 8) :
    WP isa (.block [.mov d (.mem (at_ b o))]) s fun s' => Rel s₀ s' (a.set d (s₀.mem.readW p 64)) := by
  have he : s.ea (at_ b o) = p := by
    rw [← hp, ← h.g]
    simp only [State.ea, at_, BitVec.ofInt_natCast]
  refine WP.block_cons_iff.mpr ⟨_, ?_, WP.block_nil (h.set hd _)⟩
  show (readSrc s (.mem (at_ b o))).map _ = _
  rw [readSrc, State.load64, he, ite_eq_left ⟨R, by rw [h.rd, h.wr]; exact hR, hc⟩,
    h.m.frame.readW hc (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hdis) (by decide)]
  rfl

/-- Two words of a block. -/
theorem ext2_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {b : Reg} (hb : b ≠ .r9) {R : Region} {p : Addr}
    (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (scrR s₀)) (hp : a.g b = p)
    (hc : R.Contains p 8) (hc' : R.Contains (p + BitVec.ofNat 64 8) 8) :
    WP isa (.block [.mov .r9 (.mem (at_ b 0)), .mov .r10 (.mem (at_ b 8))]) s fun s' =>
      Rel s₀ s' ((a.set .r9 (s₀.mem.readW (p + BitVec.ofNat 64 0) 64)).set .r10
        (s₀.mem.readW (p + BitVec.ofNat 64 8) 64)) := by
  have h0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  refine (WP.block_append_iff (l₁ := [_])).mpr ?_
  refine WP.mono (ext_ok h (by decide) 0 hR hdis (p := p + BitVec.ofNat 64 0) (by rw [hp]) (by rw [h0]; exact hc))
    fun s₁ r₁ => ?_
  refine ext_ok r₁ (by decide) 8 hR hdis (p := p + BitVec.ofNat 64 8) ?_ hc'
  rw [A.g_set, ite_eq_right hb, hp]

theorem ofNat_sub_ofNat {n k : Nat} (h : k ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp only [h, decide_false]

/-! ### The invariant -/

structure InvA (s₀ : State) (i : Nat) (a : A) : Prop where
  key : ∀ t < 3, ∀ j < 5, a.m (5 * t + j) = kw s₀ t &&& m5 j
  sav : ∀ q ∈ saved, a.m q.2 = s₀.gpr q.1
  y : a.m y1S ++ a.m y0S = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)
  r15 : a.g .r15 = blkAddr s₀ i
  rdi : a.g .rdi = BitVec.ofNat 64 (nb s₀ - i)
  rsi : a.g .rsi = yp s₀
  rsp : a.g .rsp = s₀.gpr .rsp

def Inv (s₀ : State) (i : Nat) (s : State) : Prop := i ≤ nb s₀ ∧ ∃ a, Rel s₀ s a ∧ InvA s₀ i a

theorem addX_ok (a : A) :
    WA addX a fun a' => a'.m y1S = bswap64 (a.g .r9) ^^^ a.m y1S ∧ a'.m y0S = bswap64 (a.g .r10) ^^^ a.m y0S ∧
      a'.m yS = a'.m y1S ^^^ a'.m y0S ∧ (∀ k < 25, a'.m k = a.m k) ∧ Keeps [.r9, .r10] a a' := by
  simp (config := {decide := true}) only [WA, addX, y1S, y0S, yS, xorR, evalA, stepA, srcA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun k hk => ?_, fun r hr => ?_⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_put, A.g_set, hr, ite_false]

theorem keep_ok (k : Nat) (hk : k + 1 < 32) (a : A) :
    WA (keep k) a fun a' => a'.m k = a.g .r11 ∧ a'.m (k + 1) = a.g .r14 ∧
      (∀ j, j ≠ k → j ≠ k + 1 → a'.m j = a.m j) ∧ a'.g = a.g := by
  simp only [WA, keep, evalA, stepA, slotOf_slot hk, slotOf_slot (Nat.lt_of_succ_lt hk), Option.map_some,
    Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨ite_eq_right (Nat.ne_of_lt (Nat.lt_succ_self k)), trivial, fun j h1 h2 => by rw [ite_eq_right h2, ite_eq_right h1], trivial⟩

/-- A block's arithmetic, its words in `r9` and `r10`. -/
def core : List Instr :=
  addX ++ mul y0S 0 ++ keep lS ++ mul y1S 1 ++ keep hS ++ mul yS 2 ++ reduce

theorem append_split {v : BitVec 128} {b c : BitVec 64} (h : b ++ c = v) : c = vdword v 0 ∧ b = vdword v 1 := by
  rw [← h, Clmul.vdword_append_0, Clmul.vdword_append_1]; exact ⟨rfl, rfl⟩

theorem core_ok {s₀ : State} {a : A} (hK : ∀ t < 3, ∀ j < 5, a.m (5 * t + j) = kw s₀ t &&& m5 j) :
    WA core a fun a' =>
      a'.m y1S ++ a'.m y0S = Spec.Gcm.mul ((bswap64 (a.g .r9) ^^^ a.m y1S) ++ (bswap64 (a.g .r10) ^^^ a.m y0S))
        (h1 s₀ ++ h0 s₀) ∧
      (∀ k < 25, k ≠ 15 → k ≠ 16 → k ≠ 17 → k ≠ 18 → a'.m k = a.m k) ∧
      Keeps [.rax, .rdx, .r9, .r10, .r11, .r14, .rcx, .rbx, .rbp, .r12, .r13] a a' := by
  have hkk : ∀ {t j : Nat}, t < 3 → j < 5 → 5 * t + j < 15 := by omega
  rw [core, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append ((addX_ok a).mono fun a₁ ⟨x1, x0, xs, m₁, g₁⟩ => ?_)
  refine WA.append ((mul_ok y0S 0 (by decide) (by decide) (kw s₀ 0) (a := a₁) (fun j hj => by
    rw [m₁ _ (by have := hkk (t := 0) (by decide) hj; omega), hK 0 (by decide) j hj])).mono fun a₂ ⟨e₂, g₂, m₂⟩ => ?_)
  refine WA.append ((keep_ok lS (by decide) a₂).mono fun a₃ ⟨l₃, l₃', m₃, g₃⟩ => ?_)
  have k₃ : ∀ k, k ≠ 15 → k ≠ 16 → a₃.m k = a₁.m k := fun k h1 h2 => by rw [m₃ k h1 h2, m₂]
  refine WA.append ((mul_ok y1S 1 (by decide) (by decide) (kw s₀ 1) (a := a₃) (fun j hj => by
    rw [k₃ _ (by omega) (by omega), m₁ _ (by omega), hK 1 (by decide) j hj])).mono fun a₄ ⟨e₄, g₄, m₄⟩ => ?_)
  refine WA.append ((keep_ok hS (by decide) a₄).mono fun a₅ ⟨l₅, l₅', m₅, g₅⟩ => ?_)
  have k₅ : ∀ k, k ≠ 17 → k ≠ 18 → a₅.m k = a₃.m k := fun k h1 h2 => by rw [m₅ k h1 h2, m₄]
  refine WA.append ((mul_ok yS 2 (by decide) (by decide) (kw s₀ 2) (a := a₅) (fun j hj => by
    rw [k₅ _ (by omega) (by omega), k₃ _ (by omega) (by omega), m₁ _ (by omega), hK 2 (by decide) j hj])).mono
      fun a₆ ⟨e₆, g₆, m₆⟩ => ?_)
  obtain ⟨p₂, p₂'⟩ := append_split e₂
  obtain ⟨p₄, p₄'⟩ := append_split e₄
  obtain ⟨p₆, p₆'⟩ := append_split e₆
  refine (reduce_ok (l := VectorCrypto.polyMul (a₁.m y0S) (kw s₀ 0)) (h := VectorCrypto.polyMul (a₃.m y1S) (kw s₀ 1))
    (c := VectorCrypto.polyMul (a₅.m yS) (kw s₀ 2)) (by rw [m₆, k₅ _ (by decide) (by decide), l₃, p₂])
    (by rw [m₆, k₅ _ (by decide) (by decide), l₃', p₂']) (by rw [m₆, l₅, p₄]) (by rw [m₆, l₅', p₄']) p₆ p₆').mono
    fun a₇ ⟨r1, r0, m₇, g₇⟩ => ⟨?_, ?_, ?_⟩
  · rw [r1, r0, ← Spread.mul_words, mulW, k₃ y1S (by decide) (by decide), k₅ yS (by decide) (by decide),
      k₃ yS (by decide) (by decide), xs, x1, x0, BitVec.xor_comm (_ ^^^ a.m y1S)]
    rfl
  · intro k hk h1 h2 h3 h4
    rw [m₇ k (by unfold y1S; omega) (by unfold y0S; omega), m₆, k₅ k h3 h4, k₃ k h1 h2, m₁ k hk]
  · refine (g₁.mono (by decide)).trans (g₂.trans ?_)
    refine Keeps.trans (b := a₃) (fun r _ => by rw [g₃]) (g₄.trans ?_)
    exact Keeps.trans (b := a₅) (fun r _ => by rw [g₅]) (g₆.trans (g₇.mono (by decide)))

/-- The machine runs what `WA` says. -/
theorem WA.sound {s₀ s : State} {a : A} {is : List Instr} {Q : A → Prop} (hp : Pre s₀) (h : Rel s₀ s a) (hw : WA is a Q) :
    WP isa (.block is) s fun s' => ∃ a', Rel s₀ s' a' ∧ Q a' := by
  obtain ⟨a', e, q⟩ := hw
  exact WP.mono (X86_64.sound hp.mem_s h e) fun s' r => ⟨a', r, q⟩

theorem next_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) :
    WP isa (.block next) s fun s' =>
      Rel s₀ s' ((a.set .r15 (a.g .r15 + 16)).set .rdi (a.g .rdi - 1)) ∧ s'.zf = some (a.g .rdi - 1 == 0) := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  obtain ⟨s₁, x₁, r₁⟩ : ∃ s₁, exec (.alu .add .r15 (.imm 16)) s = some s₁ ∧ Rel s₀ s₁ (a.set .r15 (a.g .r15 + 16)) :=
    ⟨_, rfl, by rw [← h.g, ← e16]; exact (h.flags ..).set (by decide) _⟩
  obtain ⟨s₂, x₂, r₂, hz⟩ : ∃ s₂, exec (.alu .sub .rdi (.imm 1)) s₁ = some s₂ ∧
      Rel s₀ s₂ ((a.set .r15 (a.g .r15 + 16)).set .rdi (a.g .rdi - 1)) ∧ s₂.zf = some (a.g .rdi - 1 == 0) := by
    have hg : s₁.gpr .rdi = a.g .rdi := congrFun r₁.g .rdi
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [← hg, ← e1]; exact (r₁.flags ..).set (by decide) _
    · rw [← hg, ← e1]; rfl
  exact WP.block_cons_iff.mpr ⟨s₁, x₁, WP.block_cons_iff.mpr ⟨s₂, x₂, WP.block_nil ⟨r₂, hz⟩⟩⟩

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nb s₀ - (i + 1) = 0)) := by
  have hn := hp.nb_lt
  obtain ⟨-, a, hr, ha⟩ := hI
  have hbody : body = loadX ++ (core ++ next) := by simp only [body, core, List.append_assoc]
  rw [hbody, WP.block_append_iff]
  have hc8 : ∀ o ≤ 8, (dR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 o) 8 := fun o ho => by
    rw [blkAddr, Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (ext2_ok hr (b := .r15) (by decide) hp.mem_d hp.d_s ha.r15
    (by have := hc8 0 (by decide); rwa [show blkAddr s₀ i + BitVec.ofNat 64 0 = blkAddr s₀ i from BitVec.add_zero _] at this)
    (hc8 8 (by decide))) fun s₁ r₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp r₁ (core_ok (s₀ := s₀) ha.key)) fun s₂ ⟨a₂, r₂, hy, hm, hg⟩ => ?_
  refine WP.mono (next_ok r₂) fun s₃ ⟨r₃, hz⟩ => ?_
  have hrdi : a₂.g .rdi - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hg _ (by decide)]
    show a.g .rdi - 1 = _
    rw [ha.rdi]
    exact ofNat_sub_ofNat (k := 1) (by omega) (by omega)
  refine ⟨⟨hi, _, r₃, ?_⟩, ?_⟩
  · refine ⟨fun t ht j hj => ?_, fun q hq => ?_, ?_, ?_, hrdi, ?_, ?_⟩
    · show a₂.m _ = _
      rw [hm _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact ha.key t ht j hj
    · show a₂.m _ = _
      have hq' : ∀ q ∈ saved, q.2 < 25 ∧ 18 < q.2 := by decide
      obtain ⟨h1, h2⟩ := hq' q hq
      rw [hm _ h1 (by omega) (by omega) (by omega) (by omega)]
      exact ha.sav q hq
    · refine Eq.trans hy ?_
      have hH : h1 s₀ ++ h0 s₀ = H₀ s₀ := blockAt_bswap s₀.mem (hA s₀)
      have hX := blockAt_bswap s₀.mem (blkAddr s₀ i)
      rw [ghashFrom_blocksAt_succ, ← ha.y, hH, ← hX, BitVec.xor_append, BitVec.xor_comm (a.m y1S),
        BitVec.xor_comm (a.m y0S)]
      rfl
    · show a₂.g .r15 + 16 = _
      rw [hg _ (by decide)]
      show a.g .r15 + 16 = _
      rw [ha.r15]
      exact Offset.add_add_eq (b := 16) _ (by omega)
    · show a₂.g .rsi = _
      rw [hg _ (by decide)]; exact ha.rsi
    · show a₂.g .rsp = _
      rw [hg _ (by decide)]; exact ha.rsp
  · rw [hz, hrdi, beq_ofNat_zero (by omega)]

/-! ### The prologue and the epilogue -/

theorem save_ok (a : A) :
    WA save a fun a' => (∀ q ∈ saved, a'.m q.2 = a.g q.1) ∧ a'.g = a.g := by
  simp (config := {decide := true}) only [WA, save, saved, List.map_cons, List.map_nil, evalA, stepA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left', List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ite_true, ite_false, and_self]

/-- The key's words, from `H`'s in `r9` and `r10`. -/
theorem keys_ok {s₀ : State} (a : A) (h9 : bswap64 (a.g .r9) = h1 s₀) (h10 : bswap64 (a.g .r10) = h0 s₀) :
    WA (adjust ++ (keyWord 0 .r10 ++ (keyWord 1 .r9 ++ keyWord 2 .r11))) a fun a' =>
      (∀ t < 3, ∀ j < 5, a'.m (5 * t + j) = kw s₀ t &&& m5 j) ∧ (∀ k, 15 ≤ k → a'.m k = a.m k) ∧
      Keeps [.rax, .r9, .r10, .r11, .r14] a a' := by
  refine WA.append ((adjust_ok a).mono fun a₁ ⟨e9, e10, e11, g₁, m₁⟩ => ?_)
  rw [h9, h10] at e9 e10
  refine WA.append ((keyWord_ok 0 .r10 (by decide) (by decide) a₁).mono fun a₂ ⟨k₂, m₂, g₂⟩ => ?_)
  refine WA.append ((keyWord_ok 1 .r9 (by decide) (by decide) a₂).mono fun a₃ ⟨k₃, m₃, g₃⟩ => ?_)
  refine (keyWord_ok 2 .r11 (by decide) (by decide) a₃).mono fun a₄ ⟨k₄, m₄, g₄⟩ => ⟨?_, fun k hk => ?_, ?_⟩
  · intro t ht j hj
    have h3 : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases h3 with rfl | rfl | rfl
    · rw [m₄ _ (by omega), m₃ _ (by omega), k₂ j hj, e10]; rfl
    · rw [m₄ _ (by omega), k₃ j hj, g₂ _ (by decide), e9]; rfl
    · rw [k₄ j hj, g₃ _ (by decide), g₂ _ (by decide), e11, e9, e10, BitVec.xor_comm]; rfl
  · rw [m₄ k (by omega), m₃ k (by omega), m₂ k (by omega), m₁]
  · exact (g₁.mono (by decide)).trans ((g₂.mono (by decide)).trans ((g₃.mono (by decide)).trans (g₄.mono (by decide))))

theorem storeYs_ok (a : A) :
    WA storeYs a fun a' => a'.m y1S = bswap64 (a.g .r9) ∧ a'.m y0S = bswap64 (a.g .r10) ∧
      (∀ k < 25, a'.m k = a.m k) ∧ Keeps [.r9, .r10] a a' := by
  simp (config := {decide := true}) only [WA, storeYs, y1S, y0S, evalA, stepA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, fun k hk => ?_, fun r hr => ?_⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_put, A.g_set, hr, ite_false]

theorem contains_first (p : Addr) : (⟨p, 16⟩ : Region).Contains p 8 := by
  have h := Offset.contains_base (d := 0) (n := 8) (k := 16) p (by decide) (by decide)
  rwa [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at h

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s' => Inv s₀ 0 s' ∧ s'.zf = some (decide (nb s₀ = 0)) := by
  have hpr : prologue = save ++ (([.mov .r15 (.reg .rdx)] : List Instr) ++ (([.mov .r9 (.mem (at_ .rdi 0)),
      .mov .r10 (.mem (at_ .rdi 8))] : List Instr) ++ (([.mov .rdi (.reg .rcx)] : List Instr) ++
      ((adjust ++ (keyWord 0 .r10 ++ (keyWord 1 .r9 ++ keyWord 2 .r11))) ++ (loadY ++ (storeYs ++
      ([.alu .test .rdi (.reg .rdi)] : List Instr))))))) := by
    simp only [prologue, loadH, List.append_assoc, List.cons_append, List.nil_append]
  have r₀ : Rel s₀ s₀ ⟨s₀.gpr, fun k => s₀.mem.readW (s₀.gpr .r8 + BitVec.ofNat 64 (8 * k)) 64⟩ :=
    ⟨rfl, Slots.init _ _ _, rfl, rfl, rfl⟩
  rw [hpr, WP.block_append_iff]
  refine WP.mono (WA.sound hp r₀ (save_ok _)) fun s₁ ⟨a₁, r₁, hs₁, hg₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sound hp.mem_s r₁ (a' := a₁.set .r15 (a₁.g .rdx)) rfl) fun s₂ r₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ext2_ok r₂ (b := .rdi) (p := hA s₀) (by decide) hp.mem_h hp.h_s
    (by rw [A.g_set, hg₁]; rfl) (contains_first _)
    (Offset.contains_base _ (by decide) (by decide))) fun s₃ r₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sound hp.mem_s r₃ (a' := A.set _ .rdi _) rfl) fun s₄ r₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp r₄ (keys_ok (s₀ := s₀) _ rfl rfl)) fun s₅ ⟨a₅, r₅, hk₅, hm₅, hg₅⟩ => ?_
  have gr : ∀ r, r ∉ [Reg.rax, .r9, .r10, .r11, .r14, .r15, .rdi] → a₅.g r = s₀.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg₅ r (by simp [hr])]
    simp only [A.g_set, hr, ite_false, hg₁]
  rw [WP.block_append_iff]
  refine WP.mono (ext2_ok r₅ (b := .rsi) (p := yp s₀) (by decide) hp.mem_y hp.y_s (gr .rsi (by decide))
    (contains_first _)
    (Offset.contains_base _ (by decide) (by decide))) fun s₆ r₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp r₆ (storeYs_ok _)) fun s₇ ⟨a₇, r₇, y1, y0, hm₇, hg₇⟩ => ?_
  have hdi : a₇.g .rdi = s₀.gpr .rcx := by
    rw [hg₇ _ (by decide)]
    show a₅.g .rdi = _
    rw [hg₅ _ (by decide)]
    simp only [A.g_set, reduceCtorEq, ite_false, ite_true, hg₁]
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨⟨Nat.zero_le _, a₇, r₇.flags .., ?_⟩, ?_⟩⟩
  · refine ⟨fun t ht j hj => ?_, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm₇ _ (by omega)]; exact hk₅ t ht j hj
    · have hq' : ∀ q ∈ saved, q.2 < 25 ∧ 15 ≤ q.2 := by decide
      rw [hm₇ _ (hq' q hq).1]
      exact (hm₅ _ (hq' q hq).2).trans (hs₁ q hq)
    · rw [y1, y0, ghashFrom_blocksAt_zero]
      exact blockAt_bswap s₀.mem (yp s₀)
    · rw [hg₇ _ (by decide)]
      show a₅.g .r15 = _
      rw [hg₅ _ (by decide)]
      simp only [A.g_set, reduceCtorEq, ite_false, ite_true, hg₁, blkAddr, Nat.mul_zero, BitVec.add_zero]
    · rw [hdi, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [hg₇ _ (by decide)]; exact gr .rsi (by decide)
    · rw [hg₇ _ (by decide)]; exact gr .rsp (by decide)
  · show some (s₇.gpr .rdi &&& s₇.gpr .rdi == 0) = _
    have hb := beq_ofNat_zero (k := nb s₀) (s₀.gpr .rcx).isLt
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    rw [r₇.g, hdi, BitVec.and_self, hb]

theorem restore_ok (a : A) :
    WA (([.mov .r9 (.mem (slot y1S)), .mov .r10 (.mem (slot y0S)), .bswap .r9, .bswap .r10] : List Instr) ++ restore) a
      fun a' => a'.g .r9 = bswap64 (a.m y1S) ∧ a'.g .r10 = bswap64 (a.m y0S) ∧ (∀ q ∈ saved, a'.g q.1 = a.m q.2) ∧
        Keeps [.r9, .r10, .rbx, .rbp, .r12, .r13, .r14, .r15] a a' ∧ a'.m = a.m := by
  simp (config := {decide := true}) only [WA, restore, saved, y1S, y0S, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, evalA, stepA, srcA, slotOf_slot, Option.map_some, Option.bind_some, A.g_set, A.m_set, ite_false,
    ite_true, Option.some.injEq, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    and_self, true_and]
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [A.g_set, hr, ite_false]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' => gprPreserved s₀ s' ∧ ghashX86_64.post s₀ s' := by
  obtain ⟨-, a, r, ha⟩ := hI
  rw [epilogue, WP.block_append_iff]
  refine WP.mono (WA.sound hp r (restore_ok a)) fun s₁ ⟨a₁, r₁, e9, e10, hs, hg, hm⟩ => ?_
  have hsi : s₁.gpr .rsi = yp s₀ := by rw [r₁.g, hg _ (by decide), ha.rsi]
  have hin : ∀ o ≤ 8, InRegions s₁.wr (yp s₀ + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨yR s₀, by rw [r₁.wr, hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  have hst : ∀ (s : State) (o : Nat) (q : Reg), o ≤ 8 → s.gpr = s₁.gpr → s.wr = s₁.wr →
      exec (.store (at_ .rsi o) q) s = some { s with mem := s.mem.writeW (yp s₀ + BitVec.ofNat 64 o) (s₁.gpr q) } := by
    intro s o q ho hgs hws
    show State.store64 _ _ _ = _
    rw [State.store64, show s.ea (at_ .rsi o) = yp s₀ + BitVec.ofNat 64 o by
      simp only [State.ea, at_, BitVec.ofInt_natCast, hgs, hsi], ite_eq_left (by rw [hws]; exact hin o ho), hgs]
  refine WP.block_cons_iff.mpr ⟨_, hst s₁ 0 .r9 (by decide) rfl rfl, WP.block_cons_iff.mpr ⟨_,
    hst _ 8 .r10 (by decide) rfl rfl, WP.block_nil ⟨⟨fun q hq => ?_, ?_⟩, ?_⟩⟩⟩
  · show s₁.gpr q = _
    rw [r₁.g]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hq
    have hsv : ∀ q ∈ saved, a₁.g q.1 = s₀.gpr q.1 := fun q hq => (hs q hq).trans (ha.sav q hq)
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hsv (.rbx, 19) (by decide) | exact hsv (.rbp, 20) (by decide) | exact hsv (.r12, 21) (by decide)
      | exact hsv (.r13, 22) (by decide) | exact hsv (.r14, 23) (by decide) | exact hsv (.r15, 24) (by decide)
      | exact (hg _ (by decide)).trans ha.rsp
  · have hd : ∀ o ≤ 8, Mem.Sep (s₀.gpr .rsp) 8 (yp s₀ + BitVec.ofNat 64 o) 8 := fun o ho =>
      hp.ret_y.sep (Region.contains_self _ _) (Offset.contains_base _ (by omega) (by omega))
    show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [Mem.readW_writeW_sep (hd 8 (by decide)) (by decide), Mem.readW_writeW_sep (hd 0 (by decide)) (by decide),
      r₁.m.frame.readW (r := retR s₀) (Region.contains_self _ _)
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.ret_s) (by decide)]
  · show blockAt ((s₁.mem.writeW (yp s₀ + BitVec.ofNat 64 0) _).writeW (yp s₀ + BitVec.ofNat 64 8) _) (yp s₀) = _
    have h08 := Offset.sep (yp s₀) (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
    rw [← blockAt_bswap, Mem.readW_writeW_self64, Mem.readW_writeW_sep h08 (by decide), Mem.readW_writeW_self64,
      r₁.g, e9, e10, bswap64_bswap64, bswap64_bswap64, ha.y]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => gprPreserved s₀ s' ∧ ghashX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (nb s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (nb s₀ = 0)) (by simp only [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := of_decide_eq_true h
    exact WP.block_nil (h0.symm ▸ hI)
  · have h0 : 0 < nb s₀ := Nat.pos_of_ne_zero (of_decide_eq_false h)
    let I : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Inv s₀ i s
    have hstep : ∀ m s, I m s → WP isa (.block body) s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (nb s₀) s') ∨ (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body_ok hp hi hI) fun s' ⟨hI', hz'⟩ => ?_
      by_cases hl : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega
        exact .inl ⟨by simp only [eval, hz', hl, decide_true, Option.map_some, Bool.not_true], this ▸ hI'⟩
      · exact .inr ⟨by simp only [eval, hz', hl, decide_false, Option.map_some, Bool.not_false], nb s₀ - (i + 1),
          by omega, i + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀) s₁ ⟨0, rfl, h0, hI⟩

theorem ghash_correct (s : State) (hs : ghashX86_64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86_64.ghash s t s' ∧ abiPreserved s s' ∧ ghashX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem ghash_ct : ConstantTime isa ghashX86_64.pre ghashX86_64.pub Impl.Gcm.X86_64.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Gcm.X86_64
