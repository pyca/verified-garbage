module

public import VerifiedGarbage.Impl.Gcm.X86
public import VerifiedGarbage.Proof.Gcm.X86.Ghash
public import VerifiedGarbage.Proof.Gcm.Slots
public import VerifiedGarbage.Proof.Gcm.Spread32
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Gcm.X86.Lit
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Gcm.X86.Lit
meta import VerifiedGarbage.Proof.Gcm.X86.Ghash
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# GHASH with integer multiplications on x86 (32-bit)

Untrusted: everything here is checked by Lean. The blocks of the code but for
its loads of the arguments, `H`, `Y` and the data are run on an abstract
machine, the registers and the 64 words of `scratch` (`A`, `evalA`), which
the machine follows (`sound`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86

open VG VG.X86
open VG.Impl.Gcm.X86
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-! ## The abstract machine -/

structure A where
  g : Reg → BitVec 32
  m : Nat → BitVec 32

namespace A

def set (a : A) (d : Reg) (v : BitVec 32) : A := ⟨fun r => if r = d then v else a.g r, a.m⟩
def put (a : A) (k : Nat) (v : BitVec 32) : A := ⟨a.g, fun j => if j = k then v else a.m j⟩

theorem g_set (a : A) (d : Reg) (v : BitVec 32) (r : Reg) : (a.set d v).g r = if r = d then v else a.g r := rfl
theorem m_set (a : A) (d : Reg) (v : BitVec 32) : (a.set d v).m = a.m := rfl
theorem g_put (a : A) (k : Nat) (v : BitVec 32) : (a.put k v).g = a.g := rfl
theorem m_put (a : A) (k : Nat) (v : BitVec 32) (j : Nat) : (a.put k v).m j = if j = k then v else a.m j := rfl

end A

/-- The word of `scratch` an operand is. -/
def slotOf (m : MemOp) : Option Nat :=
  if m.base = .ecx ∧ m.disp % 4 = 0 ∧ m.disp < 256 then some (m.disp / 4) else none

theorem slotOf_slot {k : Nat} (hk : k < 64) : slotOf (slot k) = some k := by
  rw [slotOf, slot, at_, ite_eq_left ⟨rfl, by show 4 * k % 4 = 0; omega, by show 4 * k < 256; omega⟩]
  exact congrArg some (Nat.mul_div_cancel_left k (by decide))

def srcA (a : A) : Src → Option (BitVec 32)
  | .reg r => some (a.g r)
  | .imm v => some v
  | .mem m => (slotOf m).map a.m

def stepA : Instr → A → Option A
  | .mov d s, a => if d = .ecx ∨ d = .esp then none else (srcA a s).map (a.set d)
  | .alu .xor d s, a => if d = .ecx ∨ d = .esp then none else (srcA a s).map fun v => a.set d (a.g d ^^^ v)
  | .alu .and d s, a => if d = .ecx ∨ d = .esp then none else (srcA a s).map fun v => a.set d (a.g d &&& v)
  | .alu .add d s, a => if d = .ecx ∨ d = .esp then none else (srcA a s).map fun v => a.set d (a.g d + v)
  | .bswap d, a => if d = .ecx ∨ d = .esp then none else some (a.set d (bswap (a.g d)))
  | .shift .shr d n, a =>
    if (d = .ecx ∨ d = .esp) ∨ ¬ (1 ≤ n ∧ n ≤ 31) then none else some (a.set d (a.g d >>> n))
  | .shift .ror d n, a =>
    if (d = .ecx ∨ d = .esp) ∨ ¬ (1 ≤ n ∧ n ≤ 31) then none else some (a.set d ((a.g d).rotateRight n))
  | .mul r, a =>
    let p := (a.g .eax).toNat * (a.g r).toNat
    some ((a.set .eax (BitVec.ofNat 32 p)).set .edx (BitVec.ofNat 32 (p / 2 ^ 32)))
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
  m : Slots32 s₀.mem s.mem ((sP s₀).setWidth 64) 64 a.m
  ecx : a.g .ecx = sP s₀
  esp : a.g .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What of the state at entry the abstract machine's steps need. -/
structure Scr (s₀ : State) : Prop where
  mem : sR s₀ ∈ s₀.wr
  fit : (sP s₀).toNat + 256 ≤ 2 ^ 32

namespace Rel

variable {s₀ s : State} {a : A}

theorem set (h : Rel s₀ s a) {d : Reg} (hd : ¬ (d = .ecx ∨ d = .esp)) (v : BitVec 32) : Rel s₀ (s.setReg d v) (a.set d v) :=
  ⟨by funext r; show (if r = d then v else s.gpr r) = _; rw [h.g]; rfl, h.m,
    by rw [A.g_set, ite_eq_right (fun e => hd (.inl e.symm))]; exact h.ecx,
    by rw [A.g_set, ite_eq_right (fun e => hd (.inr e.symm))]; exact h.esp, h.rd, h.wr⟩

theorem flags (h : Rel s₀ s a) (c o z f : Option Bool) : Rel s₀ (s.setFlags c o z f) a :=
  ⟨h.g, h.m, h.ecx, h.esp, h.rd, h.wr⟩

theorem slot (h : Rel s₀ s a) (hw : Scr s₀) {m : MemOp} {k : Nat} (hk : slotOf m = some k) :
    k < 64 ∧ s.ea m = (sP s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) ∧
      InRegions s.wr ((sP s₀).setWidth 64 + BitVec.ofNat 64 (4 * k)) 4 := by
  have hf := hw.fit
  rw [slotOf] at hk
  split at hk
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases hk
    refine ⟨by omega, ?_, _, by rw [h.wr]; exact hw.mem, Slots32.contains (n := 64) _ (by omega) (by decide)⟩
    rw [State.ea, h1, h.g, h.ecx]
    exact (addr_eq (by omega)).trans (by rw [show 4 * (m.disp / 4) = m.disp by omega])
  · cases hk

theorem src (h : Rel s₀ s a) (hw : Scr s₀) {o : Src} {v : BitVec 32} (hv : srcA a o = some v) : readSrc s o = some v := by
  cases o with
  | reg r => rw [← hv]; simp only [readSrc, srcA, h.g]
  | imm _ => exact hv
  | mem m =>
    simp only [srcA, Option.map_eq_some_iff] at hv
    obtain ⟨k, hk, hv⟩ := hv
    obtain ⟨hk, he, r, hr, hc⟩ := h.slot hw hk
    rw [readSrc, State.load32, he, ite_eq_left ⟨r, List.mem_append_right _ hr, hc⟩, ← hv, h.m.get k hk]

end Rel

theorem step_sound {s₀ s : State} {a a' : A} (h : Rel s₀ s a) (hw : Scr s₀) (i : Instr) (hi : stepA i a = some a') :
    ∃ s', exec i s = some s' ∧ Rel s₀ s' a' := by
  unfold stepA at hi
  split at hi
  · split at hi
    · cases hi
    · rename_i hd
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨v, hv, rfl⟩ := hi
      exact ⟨_, by rw [show exec _ s = (readSrc s _).map _ from rfl, h.src hw hv]; rfl, h.set hd v⟩
  iterate 3
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
    · rename_i hd; cases hi; refine ⟨_, rfl, ?_⟩; rw [h.g]; exact h.set hd _
  iterate 2
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
    obtain ⟨hk, he, hin⟩ := h.slot hw hk
    refine ⟨_, by rw [show exec _ s = State.store32 _ _ _ from rfl, State.store32, he, ite_eq_left hin], ?_⟩
    rw [h.g]
    exact ⟨rfl, h.m.store hk (by decide) _, h.ecx, h.esp, h.rd, h.wr⟩
  · cases hi

/-- The machine runs what the abstract machine runs. -/
theorem sound {s₀ : State} (hw : Scr s₀) {is : List Instr} {s : State} {a a' : A}
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

/-- The machine runs what `WA` says. -/
theorem WA.sound {s₀ s : State} {a : A} {is : List Instr} {Q : A → Prop} (hp : Scr s₀) (h : Rel s₀ s a) (hw : WA is a Q) :
    WP isa (.block is) s fun s' => ∃ a', Rel s₀ s' a' ∧ Q a' := by
  obtain ⟨a', e, q⟩ := hw
  exact WP.mono (X86.sound hp h e) fun s' r => ⟨a', r, q⟩

/-- Registers other than `rs` are unchanged. -/
def Keeps (rs : List Reg) (a a' : A) : Prop := ∀ r, r ∉ rs → a'.g r = a.g r

theorem Keeps.trans {rs : List Reg} {a b c : A} (h₁ : Keeps rs a b) (h₂ : Keeps rs b c) : Keeps rs a c :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem Keeps.mono {rs rs' : List Reg} {a b : A} (h : Keeps rs a b) (hs : ∀ r ∈ rs, r ∈ rs') : Keeps rs' a b :=
  fun r hr => h r fun h' => hr (hs r h')

open Spread (c4 m4 meet4 mul4 mul32x mulW4 W4 up32 dn32 redW4 mul_words32 setWidth_c4 m4_append append_halves)

theorem mask_eq (r : Nat) : mask r = c4 r := rfl

/-! ## The product of two words -/

/-- `mul`'s result. -/
theorem mul_append (x y : BitVec 32) :
    BitVec.ofNat 32 (x.toNat * y.toNat / 2 ^ 32) ++ BitVec.ofNat 32 (x.toNat * y.toNat) =
      x.setWidth 64 * y.setWidth 64 := by
  have hp : x.toNat * y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' x.isLt y.isLt
  apply BitVec.eq_of_toNat_eq
  rw [toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by have := x.isLt; omega),
    Nat.mod_eq_of_lt (show y.toNat < 2 ^ 64 by have := y.isLt; omega)]
  generalize x.toNat * y.toNat = p at hp ⊢
  omega

/-- Class `i` by class `j`. -/
def cp4 (a b : BitVec 32) (i j : Nat) : BitVec 64 := (a.setWidth 64 &&& m4 i) * (b.setWidth 64 &&& m4 j)

/-- The classes of `w` are at `b`. -/
def Cls (a : A) (b : Nat) (w : BitVec 32) : Prop := ∀ j < 4, a.m (b + j) = w &&& c4 j

theorem part_ok (t i j : Nat) (ht : t < 9) (hi : i < 4) (hj : j < 4) (w k : BitVec 32) (a : A) (hw : Cls a 36 w)
    (hk : Cls a (4 * t) k) :
    WA (part t i j) a fun a' => a'.g .edx ++ a'.g .eax = cp4 w k i j ∧ Keeps [.eax, .edx] a a' ∧ a'.m = a.m := by
  simp only [WA, part, ld, wS, evalA, stepA, srcA, slotOf_slot (show 36 + i < 64 by omega),
    slotOf_slot (show 4 * t + j < 64 by omega), Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left', hw i hi, hk j hj]
  refine ⟨?_, fun r hr => ?_, trivial⟩
  · rw [mul_append, setWidth_c4 _ hi, setWidth_c4 _ hj, cp4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem addPart_ok (a : A) :
    WA addPart a fun a' => a'.g .esi ++ a'.g .ebx = (a.g .esi ++ a.g .ebx) ^^^ (a.g .edx ++ a.g .eax) ∧
      Keeps [.ebx, .esi] a a' ∧ a'.m = a.m := by
  simp only [WA, addPart, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, trivial⟩
  · exact Spread.xor_append' .. |>.symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

abbrev cw : List Reg := [.eax, .edx, .ebx, .esi]

theorem and_append' (a b c d : BitVec 32) : ((a ++ b : BitVec 64) &&& (c ++ d : BitVec 64)) = (a &&& c) ++ (b &&& d) :=
  BitVec.and_append

theorem classSum_ok (t r : Nat) (ht : t < 9) (hr4 : r < 4) (w k : BitVec 32) (a : A) (hw : Cls a 36 w)
    (hk : Cls a (4 * t) k) :
    WA (classSum t r) a fun a' => a'.g .esi ++ a'.g .ebx = meet4 (w.setWidth 64) (k.setWidth 64) r &&& m4 r ∧
      Keeps cw a a' ∧ a'.m = a.m := by
  have hP : ∀ i j, i < 4 → j < 4 → ∀ b : A, b.m = a.m → WA (part t i j) b fun b' =>
      b'.g .edx ++ b'.g .eax = cp4 w k i j ∧ Keeps [.eax, .edx] b b' ∧ b'.m = a.m := by
    intro i j hi hj b hb
    exact (part_ok t i j ht hi hj w k b (by rw [Cls, hb]; exact hw) (by rw [Cls, hb]; exact hk)).mono
      fun b' ⟨e, g, m⟩ => ⟨e, g, m.trans hb⟩
  have hS : ∀ (i j : Nat), i < 4 → j < 4 → ∀ b : A, b.m = a.m → Keeps cw a b → WA (part t i j ++ addPart) b fun b' =>
      b'.g .esi ++ b'.g .ebx = (b.g .esi ++ b.g .ebx) ^^^ cp4 w k i j ∧ Keeps cw a b' ∧ b'.m = a.m := by
    intro i j hi hj b hb kb
    refine WA.append ((hP i j hi hj b hb).mono fun c ⟨e, g, m⟩ => (addPart_ok c).mono fun d ⟨e', g', m'⟩ => ⟨?_, ?_, m'.trans m⟩)
    · rw [e', e, g _ (by decide), g _ (by decide)]
    · exact kb.trans ((g.mono (by decide)).trans (g'.mono (by decide)))
  rw [show classSum t r = part t 0 (r % 4) ++ (([mv .ebx .eax, mv .esi .edx] : List Instr) ++ ((part t 1 ((r + 3) % 4) ++
    addPart) ++ ((part t 2 ((r + 2) % 4) ++ addPart) ++ ((part t 3 ((r + 1) % 4) ++ addPart) ++
    ([.alu .and .ebx (.imm (mask r)), .alu .and .esi (.imm (mask r))] : List Instr))))) by
      simp only [classSum, List.append_assoc]]
  refine WA.append ((hP 0 _ (by decide) (Nat.mod_lt _ (by decide)) a rfl).mono fun b ⟨e₁, g₁, m₁⟩ => ?_)
  refine WA.append (WA.mono (Q := fun c => c.g .esi ++ c.g .ebx = cp4 w k 0 (r % 4) ∧ Keeps cw a c ∧ c.m = a.m)
    ?_ fun c ⟨e₂, g₂, m₂⟩ => ?_)
  · simp only [WA, mv, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
      reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨e₁, fun r hr => ?_, m₁⟩
    have hg := (g₁.mono (by decide) : Keeps cw a b) r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false, hg]
  refine WA.append ((hS 1 _ (by decide) (Nat.mod_lt _ (by decide)) c m₂ g₂).mono fun d ⟨e₃, g₃, m₃⟩ => ?_)
  refine WA.append ((hS 2 _ (by decide) (Nat.mod_lt _ (by decide)) d m₃ g₃).mono fun e ⟨e₄, g₄, m₄⟩ => ?_)
  refine WA.append ((hS 3 _ (by decide) (Nat.mod_lt _ (by decide)) e m₄ g₄).mono fun f ⟨e₅, g₅, m₅⟩ => ?_)
  rw [e₄, e₃, e₂] at e₅
  simp only [WA, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set, mask_eq,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, m₅⟩
  · rw [m4_append hr4, ← and_append', e₅]; rfl
  · have hg := g₅ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false, hg]

/-! ### Splitting a word -/

theorem classStore_ok (b : Nat) (r : Reg) (j : Nat) (hb : b + j < 64) (a : A) :
    WA (classStore b r j) a fun a' => a'.m (b + j) = a.g r &&& c4 j ∧ (∀ k, k ≠ b + j → a'.m k = a.m k) ∧
      Keeps [.edx] a a' := by
  simp only [WA, classStore, mv, st, evalA, stepA, srcA, slotOf_slot hb, Option.map_some, Option.bind_some, A.g_set,
    A.m_set, A.m_put, mask_eq, reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun k hk => ite_eq_right hk, fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [A.g_put, A.g_set, hq, ite_false]

theorem split_ok (b : Nat) (r : Reg) (hb : b + 3 < 64) (hr : r ≠ .edx) (a : A) :
    WA (split b r) a fun a' => Cls a' b (a.g r) ∧ (∀ k, k < b ∨ b + 4 ≤ k → a'.m k = a.m k) ∧ Keeps [.edx] a a' := by
  have hr' : r ∉ [Reg.edx] := by simp [hr]
  rw [split, List.append_assoc, List.append_assoc]
  refine WA.append ((classStore_ok b r 0 (by omega) a).mono fun a₀ ⟨e₀, m₀, g₀⟩ => ?_)
  refine WA.append ((classStore_ok b r 1 (by omega) a₀).mono fun a₁ ⟨e₁, m₁, g₁⟩ => ?_)
  refine WA.append ((classStore_ok b r 2 (by omega) a₁).mono fun a₂ ⟨e₂, m₂, g₂⟩ => ?_)
  refine (classStore_ok b r 3 (by omega) a₂).mono fun a₃ ⟨e₃, m₃, g₃⟩ => ⟨fun j hj => ?_, fun k hk => ?_, ?_⟩
  · have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · rw [m₃ _ (by omega), m₂ _ (by omega), m₁ _ (by omega), e₀]
    · rw [m₃ _ (by omega), m₂ _ (by omega), e₁, g₀ _ hr']
    · rw [m₃ _ (by omega), e₂, g₁ _ hr', g₀ _ hr']
    · rw [e₃, g₂ _ hr', g₁ _ hr', g₀ _ hr']
  · rw [m₃ k (by omega), m₂ k (by omega), m₁ k (by omega), m₀ k (by omega)]
  · exact g₀.trans (g₁.trans (g₂.trans g₃))

/-- The sum of the words `ks`. -/
def sumOf (m : Nat → BitVec 32) : List Nat → BitVec 32
  | [] => 0
  | k :: ks => ks.foldl (fun v k => v ^^^ m k) (m k)

theorem xors_ok (ks : List Nat) (hk : ∀ k ∈ ks, k < 64) (a : A) :
    WA (ks.map (xorM .eax)) a fun a' => a'.g .eax = ks.foldl (fun v k => v ^^^ a.m k) (a.g .eax) ∧ Keeps [.eax] a a' ∧
      a'.m = a.m := by
  induction ks generalizing a with
  | nil => exact ⟨a, rfl, rfl, fun _ _ => rfl, rfl⟩
  | cons k ks ih =>
    rw [List.map_cons]
    refine WA.append (l₁ := [_]) ?_
    simp only [WA, xorM, evalA, stepA, srcA, slotOf_slot (hk k (List.mem_cons_self ..)), reduceCtorEq, or_self, ite_false,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    obtain ⟨b, e, h1, h2, h3⟩ := ih (fun k h => hk k (List.mem_cons_of_mem _ h)) (a.set .eax (a.g .eax ^^^ a.m k))
    exact ⟨b, e, h1, fun r hr => (h2 r hr).trans (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp only [A.g_set, hr, ite_false]), h3⟩

theorem sumWords_ok (k : Nat) (ks : List Nat) (h : ∀ j ∈ k :: ks, j < 64) (a : A) :
    WA (sumWords (k :: ks)) a fun a' => a'.g .eax = sumOf a.m (k :: ks) ∧ Keeps [.eax] a a' ∧ a'.m = a.m := by
  rw [sumWords]
  refine WA.append (l₁ := [_]) ?_
  simp only [WA, ld, evalA, stepA, srcA, slotOf_slot (h k (List.mem_cons_self ..)), reduceCtorEq, or_self, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  obtain ⟨b, e, h1, h2, h3⟩ := xors_ok ks (fun j hj => h j (List.mem_cons_of_mem _ hj)) (a.set .eax (a.m k))
  exact ⟨b, e, h1, fun r hr => (h2 r hr).trans (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp only [A.g_set, hr, ite_false]), h3⟩

/-! ### The product -/

abbrev work : List Reg := [.eax, .edx, .ebx, .esi, .edi, .ebp]

theorem take_ok (a : A) :
    WA [xorR .edi .ebx, xorR .ebp .esi] a fun a' =>
      a'.g .ebp ++ a'.g .edi = (a.g .ebp ++ a.g .edi) ^^^ (a.g .esi ++ a.g .ebx) ∧ Keeps [.edi, .ebp] a a' ∧ a'.m = a.m := by
  simp only [WA, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, trivial⟩
  · exact Spread.xor_append' .. |>.symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem append_split {v : BitVec 64} {b c : BitVec 32} (h : b ++ c = v) : c = v.extractLsb' 0 32 ∧ b = v.extractLsb' 32 32 := by
  subst h
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> rw [BitVec.extractLsb'_toNat, toNat_append] <;>
    have := b.isLt <;> have := c.isLt <;> omega

theorem mul32_ok (k : Nat) (ks : List Nat) (t : Nat) (hks : ∀ j ∈ k :: ks, j < 64) (ht : t < 9) (kw : BitVec 32) (a : A)
    (hK : Cls a (4 * t) kw) :
    WA (mul32 (k :: ks) t) a fun a' =>
      a'.g .edi = (mul32x (sumOf a.m (k :: ks)) kw).1 ∧ a'.g .ebp = (mul32x (sumOf a.m (k :: ks)) kw).2 ∧
      Keeps work a a' ∧ ∀ j, j < 36 ∨ 40 ≤ j → a'.m j = a.m j := by
  generalize hw : sumOf a.m (k :: ks) = w
  rw [mul32]
  simp only [List.append_assoc]
  refine WA.append ((sumWords_ok k ks hks a).mono fun b ⟨e₁, g₁, m₁⟩ => ?_)
  refine WA.append ((split_ok 36 .eax (by decide) (by decide) b).mono fun c ⟨C, m₂, g₂⟩ => ?_)
  rw [e₁, hw] at C
  have hKc : Cls c (4 * t) kw := fun j hj => by rw [m₂ _ (by omega), m₁, hK j hj]
  have Mc : ∀ j, j < 36 ∨ 40 ≤ j → c.m j = a.m j := fun j hj => by rw [m₂ j hj, m₁]
  have kc : Keeps work a c := (g₁.mono (by decide)).trans (g₂.mono (by decide))
  have hC : ∀ r < 4, ∀ d : A, d.m = c.m → WA (classSum t r) d fun d' =>
      d'.g .esi ++ d'.g .ebx = meet4 (w.setWidth 64) (kw.setWidth 64) r &&& m4 r ∧ Keeps cw d d' ∧ d'.m = c.m :=
    fun r hr d hd => (classSum_ok t r ht hr w kw d (by rw [Cls, hd]; exact C) (by rw [Cls, hd]; exact hKc)).mono
      fun d' ⟨e, g, m⟩ => ⟨e, g, m.trans hd⟩
  refine WA.append ((hC 0 (by decide) c rfl).mono fun d ⟨e₃, g₃, m₃⟩ => ?_)
  refine WA.append (WA.mono (Q := fun e => e.g .ebp ++ e.g .edi = d.g .esi ++ d.g .ebx ∧ Keeps [.edi, .ebp] d e ∧ e.m = d.m)
    ?_ fun e ⟨e₄, g₄, m₄⟩ => ?_)
  · simp only [WA, mv, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
      reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  refine WA.append ((hC 1 (by decide) e (m₄.trans m₃)).mono fun f ⟨e₅, g₅, m₅⟩ => ?_)
  refine WA.append ((take_ok f).mono fun g ⟨e₆, g₆, m₆⟩ => ?_)
  refine WA.append ((hC 2 (by decide) g (m₆.trans m₅)).mono fun h ⟨e₇, g₇, m₇⟩ => ?_)
  refine WA.append ((take_ok h).mono fun i ⟨e₈, g₈, m₈⟩ => ?_)
  refine WA.append ((hC 3 (by decide) i (m₈.trans m₇)).mono fun l ⟨e₉, g₉, m₉⟩ => ?_)
  refine (take_ok l).mono fun n ⟨e₁₀, g₁₀, m₁₀⟩ => ?_
  have hv : n.g .ebp ++ n.g .edi = mul4 (w.setWidth 64) (kw.setWidth 64) := by
    rw [e₁₀, g₉ _ (by decide), g₉ .edi (by decide), e₈, g₇ _ (by decide), g₇ .edi (by decide), e₆, g₅ _ (by decide),
      g₅ .edi (by decide), e₄, e₃, e₅, e₇, e₉, mul4]
  obtain ⟨v1, v2⟩ := append_split hv
  refine ⟨v1, v2, ?_, fun j hj => ?_⟩
  · exact kc.trans <| (g₃.mono (by decide)).trans <| (g₄.mono (by decide)).trans <| (g₅.mono (by decide)).trans <|
      (g₆.mono (by decide)).trans <| (g₇.mono (by decide)).trans <| (g₈.mono (by decide)).trans <|
      (g₉.mono (by decide)).trans <| g₁₀.mono (by decide)
  · rw [m₁₀, m₉, Mc j hj]

theorem keep_ok (b : Nat) (hb : b + 1 < 64) (a : A) :
    WA (keep b) a fun a' => a'.m b = a.g .edi ∧ a'.m (b + 1) = a.g .ebp ∧ (∀ j, j ≠ b → j ≠ b + 1 → a'.m j = a.m j) ∧
      a'.g = a.g := by
  simp only [WA, keep, st, evalA, stepA, slotOf_slot hb, slotOf_slot (Nat.lt_of_succ_lt hb), Option.map_some,
    Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨ite_eq_right (Nat.ne_of_lt (Nat.lt_succ_self b)), trivial,
    fun j h1 h2 => by rw [ite_eq_right h2, ite_eq_right h1], trivial⟩

/-- The four words at `b`. -/
def At (a : A) (b : Nat) (w : W4) : Prop := a.m b = w.w0 ∧ a.m (b + 1) = w.w1 ∧ a.m (b + 2) = w.w2 ∧ a.m (b + 3) = w.w3

theorem sumOf_congr {m m' : Nat → BitVec 32} {ks : List Nat} (h : ∀ k ∈ ks, m k = m' k) : sumOf m ks = sumOf m' ks := by
  cases ks with
  | nil => rfl
  | cons k ks =>
    have hl : ∀ (l : List Nat) (v : BitVec 32), (∀ k ∈ l, m k = m' k) →
        l.foldl (fun v k => v ^^^ m k) v = l.foldl (fun v k => v ^^^ m' k) v := by
      intro l
      induction l with
      | nil => exact fun _ _ => rfl
      | cons k l ih =>
        intro v h
        rw [List.foldl_cons, List.foldl_cons, h k (List.mem_cons_self ..), ih _ fun j hj => h j (List.mem_cons_of_mem _ hj)]
    rw [sumOf, sumOf, h k (List.mem_cons_self ..), hl _ _ fun j hj => h j (List.mem_cons_of_mem _ hj)]

/-- Words multiplied: of `Y`'s. -/
def Ys (ks : List Nat) : Prop := ∀ k ∈ ks, 40 ≤ k ∧ k < 44

theorem mul64_ok (x₀ : Nat) (xs₀ : List Nat) (x₁ : Nat) (xs₁ : List Nat) (t b : Nat) (ht : t + 2 < 9)
    (hb : b = 44 ∨ b = 48 ∨ b = 52) (k0 k1 : BitVec 32) (a : A) (h₀ : Ys (x₀ :: xs₀)) (h₁ : Ys (x₁ :: xs₁))
    (hK : Cls a (4 * t) k0 ∧ Cls a (4 * (t + 1)) k1 ∧ Cls a (4 * (t + 2)) (k0 ^^^ k1))
    (hS : sumOf a.m (x₀ :: xs₀ ++ x₁ :: xs₁) = sumOf a.m (x₀ :: xs₀) ^^^ sumOf a.m (x₁ :: xs₁)) :
    WA (mul64 (x₀ :: xs₀) (x₁ :: xs₁) t b) a fun a' =>
      At a' b (mulW4 mul32x (sumOf a.m (x₁ :: xs₁)) (sumOf a.m (x₀ :: xs₀)) k1 k0) ∧ Keeps work a a' ∧
      ∀ j, j < 36 ∨ 40 ≤ j → (j < b ∨ b + 4 ≤ j) → a'.m j = a.m j := by
  have lt : ∀ {ks : List Nat}, Ys ks → ∀ j ∈ ks, j < 64 := fun h j hj => by have := h j hj; omega
  have h₂ : Ys (x₀ :: (xs₀ ++ x₁ :: xs₁)) := fun k hk => by
    rw [← List.cons_append, List.mem_append] at hk
    rcases hk with hk | hk
    · exact h₀ k hk
    · exact h₁ k hk
  rw [mul64, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append ((mul32_ok x₀ xs₀ t (lt h₀) (by omega) k0 a hK.1).mono fun c ⟨p0, p1, kc, mc⟩ => ?_)
  refine WA.append ((keep_ok b (by omega) c).mono fun d ⟨q0, q1, md, gd⟩ => ?_)
  have kd : Keeps work a d := fun r hr => by rw [gd, kc r hr]
  have Md : ∀ j, j < 36 ∨ 40 ≤ j → j ≠ b → j ≠ b + 1 → d.m j = a.m j := fun j hj h1 h2 => by rw [md j h1 h2, mc j hj]
  have hKd : Cls d (4 * (t + 1)) k1 := fun j hj => by rw [Md _ (by omega) (by omega) (by omega), hK.2.1 j hj]
  refine WA.append ((mul32_ok x₁ xs₁ (t + 1) (lt h₁) (by omega) k1 d hKd).mono fun e ⟨p2, p3, ke, me⟩ => ?_)
  refine WA.append ((keep_ok (b + 2) (by omega) e).mono fun f ⟨q2, q3, mf, gf⟩ => ?_)
  have kf : Keeps work a f := fun r hr => by rw [gf, ke r hr, kd r hr]
  have Mf : ∀ j, j < 36 ∨ 40 ≤ j → (j < b ∨ b + 4 ≤ j) → f.m j = a.m j := fun j hj h => by
    rw [mf j (by omega) (by omega), me j hj, Md j hj (by omega) (by omega)]
  have hKf : Cls f (4 * (t + 2)) (k0 ^^^ k1) := fun j hj => by rw [Mf _ (by omega) (by omega), hK.2.2 j hj]
  refine WA.append ((mul32_ok x₀ (xs₀ ++ x₁ :: xs₁) (t + 2) (lt h₂) (by omega) (k0 ^^^ k1) f hKf).mono
    fun g ⟨p4, p5, kg, mg⟩ => ?_)
  have s₁ : sumOf d.m (x₁ :: xs₁) = sumOf a.m (x₁ :: xs₁) := sumOf_congr fun k hk => by
    have := h₁ k hk; exact Md k (by omega) (by omega) (by omega)
  have s₂ : sumOf f.m (x₀ :: (xs₀ ++ x₁ :: xs₁)) = sumOf a.m (x₀ :: xs₀) ^^^ sumOf a.m (x₁ :: xs₁) :=
    (sumOf_congr fun k hk => by have := h₂ k hk; exact Mf k (by omega) (by omega)).trans hS
  rw [s₂] at p4 p5
  rw [s₁] at p2 p3
  have w0 : g.m b = (mul32x (sumOf a.m (x₀ :: xs₀)) k0).1 := by
    rw [mg _ (by omega), mf _ (by omega) (by omega), me _ (by omega), q0, p0]
  have w1 : g.m (b + 1) = (mul32x (sumOf a.m (x₀ :: xs₀)) k0).2 := by
    rw [mg _ (by omega), mf _ (by omega) (by omega), me _ (by omega), q1, p1]
  have w2 : g.m (b + 2) = (mul32x (sumOf a.m (x₁ :: xs₁)) k1).1 := by rw [mg _ (by omega), q2, p2]
  have w3 : g.m (b + 3) = (mul32x (sumOf a.m (x₁ :: xs₁)) k1).2 := by
    rw [mg _ (by omega), show f.m (b + 3) = e.g .ebp from q3, p3]
  simp only [WA, ld, st, xorR, evalA, stepA, srcA, slotOf_slot (show b < 64 by omega),
    slotOf_slot (show b + 1 < 64 by omega), slotOf_slot (show b + 2 < 64 by omega), slotOf_slot (show b + 3 < 64 by omega),
    Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, reduceCtorEq, or_self,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, w0, w1, w2, w3, p4, p5, At, mulW4,
    show ¬ b = b + 1 by omega, show ¬ b = b + 2 by omega, show ¬ b + 1 = b + 2 by omega,
    show ¬ b + 3 = b + 1 by omega, show ¬ b + 3 = b + 2 by omega]
  refine ⟨⟨trivial, trivial, trivial, trivial⟩, fun r hr => ?_, fun j hj h => ?_⟩
  · have hk := (kf.trans kg) r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_put, A.g_set, hr, ite_false, hk]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), mg j hj, Mf j hj h]

/-! ## The reduction and the key -/

theorem ror_eq (z : BitVec 32) {k : Nat} (h0 : 0 < k) (hk : k < 32) : z.rotateRight k = z >>> k ^^^ z <<< (32 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h : i < 32 - k
  · simp [h]
  · simp [h, hi, BitVec.getLsbD_of_ge z (k + i) (by omega)]

theorem ror_ror (z : BitVec 32) {k l : Nat} (hk : k < 32) (hl : l < 32) (h : k + l < 32) :
    (z.rotateRight k).rotateRight l = z.rotateRight (k + l) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt h]
  by_cases h1 : i < 32 - l
  · simp only [h1, ite_true]
    by_cases h2 : l + i < 32 - k
    · simp only [h2, ite_true, show i < 32 - (k + l) by omega, Nat.add_assoc]
    · simp only [h2, ite_false, show ¬ i < 32 - (k + l) by omega, hi, show l + i < 32 by omega,
        show l + i - (32 - k) = i - (32 - (k + l)) by omega]
  · simp only [h1, ite_false, show ¬ i < 32 - (k + l) by omega, hi, show i - (32 - l) < 32 - k by omega, ite_true,
      decide_true, Bool.true_and, show k + (i - (32 - l)) = i - (32 - (k + l)) by omega]

theorem fold_xor (p q r a b c : BitVec 32) : (p ^^^ a) ^^^ (q ^^^ b) ^^^ (r ^^^ c) ^^^ (p ^^^ q ^^^ r) = a ^^^ b ^^^ c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases p.getLsbD i <;> cases q.getLsbD i <;> cases r.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;>
    cases c.getLsbD i <;> rfl

theorem fold_ok (a : A) :
    WA fold a fun a' => (a'.g .esi = up32 (a.g .eax) ∧ a'.g .ebx = dn32 (a.g .eax)) ∧ Keeps [.eax, .ebx, .esi] a a' ∧
      a'.m = a.m := by
  have e1 : ∀ v : BitVec 32, v >>> 1 >>> 1 = v >>> 2 := fun v => (BitVec.shiftRight_add v 1 1).symm
  have e2 : ∀ v : BitVec 32, v >>> 2 >>> 5 = v >>> 7 := fun v => (BitVec.shiftRight_add v 2 5).symm
  have r1 : ∀ v : BitVec 32, (v.rotateRight 1).rotateRight 1 = v.rotateRight 2 := fun v =>
    ror_ror v (by decide) (by decide) (by decide)
  have r2 : ∀ v : BitVec 32, (v.rotateRight 2).rotateRight 5 = v.rotateRight 7 := fun v =>
    ror_ror v (by decide) (by decide) (by decide)
  simp only [WA, fold, mv, shr, ror, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, Nat.reduceLeDiff, and_self, not_true_eq_false, ite_false, ite_true, Option.some.injEq,
    exists_eq_left', e1, e2, r1, r2]
  refine ⟨⟨rfl, ?_⟩, fun r hr => ?_, trivial⟩
  · rw [ror_eq _ (k := 1) (by decide) (by decide), ror_eq _ (k := 2) (by decide) (by decide),
      ror_eq _ (k := 7) (by decide) (by decide), fold_xor, dn32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem reduce_ok {a : A} {l h c : W4} (hl : At a 44 l) (hh : At a 48 h) (hc : At a 52 c) :
    WA reduce a fun a' => (a'.m 40 = (redW4 l h c).w0 ∧ a'.m 41 = (redW4 l h c).w1 ∧ a'.m 42 = (redW4 l h c).w2 ∧
      a'.m 43 = (redW4 l h c).w3) ∧ (∀ k, k < 40 ∨ 44 ≤ k → a'.m k = a.m k) ∧ Keeps work a a' := by
  obtain ⟨l0, l1, l2, l3⟩ := hl
  obtain ⟨h0, h1, h2, h3⟩ := hh
  obtain ⟨c0, c1, c2, c3⟩ := hc
  simp only [Nat.reduceAdd] at l1 l2 l3 h1 h2 h3 c1 c2 c3
  rw [reduce]
  simp only [List.append_assoc]
  refine WA.append (WA.mono (Q := fun b => b.g .eax = l.w0 ∧ Keeps work a b ∧ b.m = a.m) ?_ fun b₁ ⟨e₁, k₁, m₁⟩ => ?_)
  · simp (config := {decide := true}) only [WA, ld, lS, evalA, stepA, srcA, slotOf_slot, Option.map_some,
      Option.bind_some, A.g_set, A.m_set, ite_false, ite_true, Option.some.injEq, exists_eq_left', l0]
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  refine WA.append ((fold_ok b₁).mono fun b₂ ⟨⟨u₂, d₂⟩, k₂, m₂⟩ => ?_)
  rw [e₁] at u₂ d₂
  have M₂ : b₂.m = a.m := m₂.trans m₁
  refine WA.append (WA.mono (Q := fun b => (b.g .edx = c.w1 ^^^ l.w1 ^^^ h.w1 ^^^ l.w3 ^^^ dn32 l.w0 ∧
      b.g .edi = h.w0 ^^^ c.w2 ^^^ l.w2 ^^^ h.w2 ^^^ l.w0 ^^^ up32 l.w0 ∧ b.g .eax = l.w1) ∧
      Keeps work b₂ b ∧ b.m = a.m) ?_ fun b₃ ⟨⟨z₃, w₃, e₃⟩, k₃, m₃⟩ => ?_)
  · simp (config := {decide := true}) only [WA, ld, xorM, xorR, lS, hS, cS, evalA, stepA, srcA, slotOf_slot, Option.map_some,
      Option.bind_some, A.g_set, A.m_set, ite_false, ite_true, Option.some.injEq, exists_eq_left', M₂, l0, l1, l2, l3, h0, h1,
      h2, c1, c2, u₂, d₂]
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  refine WA.append ((fold_ok b₃).mono fun b₄ ⟨⟨u₄, d₄⟩, k₄, m₄⟩ => ?_)
  rw [e₃] at u₄ d₄
  have M₄ : b₄.m = a.m := m₄.trans m₃
  have w₄ : b₄.g .edi = _ := (k₄ _ (by decide)).trans w₃
  refine WA.append (WA.mono (Q := fun b => (b.m 40 = (redW4 l h c).w0 ∧
      b.g .edi = h.w1 ^^^ c.w3 ^^^ l.w3 ^^^ h.w3 ^^^ l.w1 ^^^ up32 l.w1 ∧ b.g .eax = c.w0 ^^^ l.w0 ^^^ h.w0 ^^^ l.w2 ∧
      b.g .ebp = c.w0 ^^^ l.w0 ^^^ h.w0 ^^^ l.w2) ∧
      Keeps [.eax, .ebx, .esi, .edi, .ebp] b₄ b ∧ ∀ k, k ≠ 40 → b.m k = a.m k) ?_ fun b₅ ⟨⟨o₅, w₅, e₅, p₅⟩, k₅, m₅⟩ => ?_)
  · simp (config := {decide := true}) only [WA, ld, st, mv, xorM, xorR, yS, lS, hS, cS, evalA, stepA, srcA, slotOf_slot,
      Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq,
      exists_eq_left', M₄, l0, l1, l2, l3, h0, h1, h3, c0, c3, u₄, d₄, w₄]
    refine ⟨⟨?_, trivial⟩, fun r hr => ?_, fun k hk => ite_eq_right hk⟩
    · simp only [redW4, BitVec.xor_assoc]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [A.g_put, A.g_set, hr, ite_false]
  refine WA.append ((fold_ok b₅).mono fun b₆ ⟨⟨u₆, d₆⟩, k₆, m₆⟩ => ?_)
  rw [e₅] at u₆ d₆
  have w₆ : b₆.g .edi = _ := (k₆ _ (by decide)).trans w₅
  have p₆ : b₆.g .ebp = _ := (k₆ _ (by decide)).trans p₅
  have z₆ : b₆.g .edx = _ := (k₆ _ (by decide)).trans ((k₅ _ (by decide)).trans ((k₄ _ (by decide)).trans z₃))
  have H₆ : b₆.m 50 = h.w2 := by rw [m₆, m₅ _ (by decide), h2]
  refine WA.append (WA.mono (Q := fun b => (b.m 41 = (redW4 l h c).w1 ∧
      b.g .edi = h.w2 ^^^ (c.w0 ^^^ l.w0 ^^^ h.w0 ^^^ l.w2) ^^^ up32 (c.w0 ^^^ l.w0 ^^^ h.w0 ^^^ l.w2) ∧
      b.g .eax = c.w1 ^^^ l.w1 ^^^ h.w1 ^^^ l.w3 ^^^ dn32 l.w0 ∧
      b.g .edx = c.w1 ^^^ l.w1 ^^^ h.w1 ^^^ l.w3 ^^^ dn32 l.w0) ∧
      Keeps work b₆ b ∧ ∀ k, k ≠ 41 → b.m k = b₆.m k) ?_ fun b₇ ⟨⟨o₇, w₇, e₇, z₇⟩, k₇, m₇⟩ => ?_)
  · simp (config := {decide := true}) only [WA, ld, st, mv, xorR, yS, hS, evalA, stepA, srcA, slotOf_slot,
      Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq,
      exists_eq_left', H₆, u₆, d₆, w₆, p₆, z₆]
    refine ⟨⟨?_, trivial⟩, fun r hr => ?_, fun k hk => ite_eq_right hk⟩
    · simp only [redW4, BitVec.xor_assoc]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [A.g_put, A.g_set, hr, ite_false]
  refine WA.append ((fold_ok b₇).mono fun b₈ ⟨⟨u₈, d₈⟩, k₈, m₈⟩ => ?_)
  rw [e₇] at u₈ d₈
  have w₈ : b₈.g .edi = _ := (k₈ _ (by decide)).trans w₇
  have z₈ : b₈.g .edx = _ := (k₈ _ (by decide)).trans z₇
  have H₈ : b₈.m 51 = h.w3 := by rw [m₈, m₇ _ (by decide), m₆, m₅ _ (by decide), h3]
  have O₀ : b₈.m 40 = (redW4 l h c).w0 := by rw [m₈, m₇ _ (by decide), m₆, o₅]
  have O₁ : b₈.m 41 = (redW4 l h c).w1 := by rw [m₈, o₇]
  simp (config := {decide := true}) only [WA, ld, st, xorR, yS, hS, evalA, stepA, srcA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq,
    exists_eq_left', H₈, u₈, d₈, w₈, z₈, O₀, O₁]
  refine ⟨⟨trivial, trivial, ?_, ?_⟩, fun k hk => ?_, fun r hr => ?_⟩
  · simp only [redW4, BitVec.xor_assoc]
  · simp only [redW4, BitVec.xor_assoc]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), m₈, m₇ _ (by omega), m₆, m₅ _ (by omega)]
  · have hk : Keeps work a b₈ := k₁.trans <| (k₂.mono (by decide)).trans <| k₃.trans <| (k₄.mono (by decide)).trans <|
      (k₅.mono (by decide)).trans <| (k₆.mono (by decide)).trans <| k₇.trans (k₈.mono (by decide))
    have hk := hk r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_put, A.g_set, hr, ite_false, hk]

theorem addX_ok (a : A) :
    WA addX a fun a' =>
      (a'.m 43 = bswap (a.g .eax) ^^^ a.m 43 ∧ a'.m 42 = bswap (a.g .ebx) ^^^ a.m 42 ∧
        a'.m 41 = bswap (a.g .esi) ^^^ a.m 41 ∧ a'.m 40 = bswap (a.g .edi) ^^^ a.m 40) ∧
      (∀ k, k < 40 ∨ 44 ≤ k → a'.m k = a.m k) ∧ Keeps work a a' := by
  simp (config := {decide := true}) only [WA, addX, revBlk, List.cons_append, List.nil_append, xorM, st, yS,
    evalA, stepA, srcA, slotOf_slot, Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put,
    ite_false, ite_true, Option.some.injEq, exists_eq_left', and_self]
  refine ⟨trivial, fun k hk => ?_, fun r hr => ?_⟩
  · simp only [show ¬ k = 40 by omega, show ¬ k = 41 by omega, show ¬ k = 42 by omega, show ¬ k = 43 by omega, ite_false]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_put, A.g_set, hr, ite_false]

/-- The key's words, of which `h₃` is `H`'s first. -/
def kws (h3 h2 h1 h0 : BitVec 32) : W4 :=
  ⟨h0 <<< 1 ^^^ h3 >>> 31, h1 <<< 1 ^^^ h0 >>> 31, h2 <<< 1 ^^^ h1 >>> 31, h3 <<< 1 ^^^ h2 >>> 31 ^^^ dn32 (h3 >>> 31)⟩

theorem add_self (v : BitVec 32) : v + v = v <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- A rotation of one bit. -/
theorem ror_bit (v : BitVec 32) {k : Nat} (h0 : 0 < k) (hk : k < 32) : (v >>> 31).rotateRight k = v >>> 31 <<< (32 - k) := by
  rw [ror_eq _ h0 hk, ← BitVec.shiftRight_add, BitVec.ushiftRight_eq_zero (by omega), BitVec.zero_xor]

theorem adjust_ok (a : A) :
    WA adjust a fun a' => (let k := kws (a.g .eax) (a.g .ebx) (a.g .esi) (a.g .edi)
      a'.g .eax = k.w3 ∧ a'.g .ebx = k.w2 ∧ a'.g .esi = k.w1 ∧ a'.g .edi = k.w0) ∧ Keeps work a a' ∧ a'.m = a.m := by
  have r1 : ∀ v : BitVec 32, (v.rotateRight 1).rotateRight 1 = v.rotateRight 2 := fun v =>
    ror_ror v (by decide) (by decide) (by decide)
  have r2 : ∀ v : BitVec 32, (v.rotateRight 2).rotateRight 5 = v.rotateRight 7 := fun v =>
    ror_ror v (by decide) (by decide) (by decide)
  have b1 : ∀ v : BitVec 32, (v >>> 31).rotateRight 1 = v >>> 31 <<< 31 := fun v => ror_bit v (by decide) (by decide)
  have b2 : ∀ v : BitVec 32, (v >>> 31).rotateRight 2 = v >>> 31 <<< 30 := fun v => ror_bit v (by decide) (by decide)
  have b7 : ∀ v : BitVec 32, (v >>> 31).rotateRight 7 = v >>> 31 <<< 25 := fun v => ror_bit v (by decide) (by decide)
  simp only [WA, adjust, mv, shr, ror, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, Nat.reduceLeDiff, and_self, not_true_eq_false, ite_false, ite_true, Option.some.injEq,
    exists_eq_left', r1, r2, add_self, kws, dn32]
  refine ⟨⟨?_, trivial⟩, fun r hr => ?_, trivial⟩
  · rw [b1, b2, b7]; simp only [BitVec.xor_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem keyWord_ok (t : Nat) (r : Reg) (hr : r ≠ .edx) (ht : t < 9) (a : A) :
    WA (keyWord t r) a fun a' => Cls a' (4 * t) (a.g r) ∧ (∀ k, k < 4 * t ∨ 4 * t + 4 ≤ k → a'.m k = a.m k) ∧
      Keeps [.edx] a a' := split_ok (4 * t) r (by omega) hr a

/-- The words the code multiplies by. -/
def kt (k : W4) (t : Nat) : BitVec 32 :=
  match t with
  | 0 => k.w0 | 1 => k.w1 | 2 => k.w0 ^^^ k.w1 | 3 => k.w2 | 4 => k.w3 | 5 => k.w2 ^^^ k.w3
  | 6 => k.w0 ^^^ k.w2 | 7 => k.w1 ^^^ k.w3 | _ => (k.w0 ^^^ k.w2) ^^^ (k.w1 ^^^ k.w3)

/-- The first `n` of them are in place. -/
def KeysTo (a : A) (k : W4) (n : Nat) : Prop := ∀ t < n, Cls a (4 * t) (kt k t)

theorem KeysTo.word {a b : A} {k : W4} {n : Nat} (h : KeysTo a k n) (hk : Cls b (4 * n) (kt k n))
    (hm : ∀ j, j < 4 * n ∨ 4 * n + 4 ≤ j → b.m j = a.m j) : KeysTo b k (n + 1) := by
  intro t ht
  by_cases e : t = n
  · subst e; exact hk
  · exact fun j hj => by rw [hm _ (by omega), h t (by omega) j hj]

theorem KeysTo.mem {a b : A} {k : W4} {n : Nat} (h : KeysTo a k n) (hm : b.m = a.m) : KeysTo b k n := by
  intro t ht; rw [Cls, hm]; exact h t ht

theorem step_key {a : A} {k : W4} {n : Nat} {r : Reg} {is : List Instr} {Q : A → Prop} (h : KeysTo a k n) (hn : n < 9)
    (hr : r ≠ .edx) (hv : a.g r = kt k n)
    (hq : ∀ b, KeysTo b k (n + 1) → Keeps [.edx] a b → (∀ j, 36 ≤ j → b.m j = a.m j) → WA is b Q) :
    WA (keyWord n r ++ is) a Q :=
  WA.append ((keyWord_ok n r hr hn a).mono fun b ⟨e, m, g⟩ =>
    hq b (h.word (hv ▸ e) m) g fun j hj => m j (by omega))

theorem step_sum {a : A} {is : List Instr} {Q : A → Prop} (n m : Reg) (hm : m ≠ .ebp)
    (hq : ∀ b, b.g .ebp = a.g n ^^^ a.g m → Keeps [.ebp] a b → b.m = a.m → WA is b Q) : WA (keySum n m ++ is) a Q := by
  refine WA.append (WA.mono (Q := fun b => b.g .ebp = a.g n ^^^ a.g m ∧ Keeps [.ebp] a b ∧ b.m = a.m) ?_
    fun b ⟨e, g, m⟩ => hq b e g m)
  simp only [WA, keySum, mv, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set, hm,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_set, hr, ite_false]

theorem keyCode_ok (a : A) :
    WA keyCode a fun a' => KeysTo a' (kws (a.g .eax) (a.g .ebx) (a.g .esi) (a.g .edi)) 9 ∧
      (∀ j, 36 ≤ j → a'.m j = a.m j) ∧ Keeps work a a' := by
  rw [keyCode]
  simp only [List.append_assoc]
  refine WA.append ((adjust_ok a).mono fun b ⟨⟨e3, e2, e1, e0⟩, gb, mb⟩ => ?_)
  generalize hk : kws (a.g .eax) (a.g .ebx) (a.g .esi) (a.g .edi) = k at e3 e2 e1 e0 ⊢
  refine step_key (k := k) (n := 0) (fun t ht => absurd ht (Nat.not_lt_zero t)) (by decide) (by decide) e0 fun b₀ K₀ g₀ m₀ => ?_
  refine step_key K₀ (by decide) (by decide) (by rw [g₀ _ (by decide), e1]; rfl) fun b₁ K₁ g₁ m₁ => ?_
  have G₁ := g₀.trans g₁
  refine step_sum _ _ (by decide) fun b₂ e₂ g₂ m₂ => ?_
  rw [G₁ _ (by decide), G₁ _ (by decide), e0, e1] at e₂
  have G₂ : Keeps [.edx, .ebp] b b₂ := (G₁.mono (by decide)).trans (g₂.mono (by decide))
  refine step_key (K₁.mem m₂) (by decide) (by decide) (by rw [e₂]; rfl) fun b₃ K₃ g₃ m₃ => ?_
  have G₃ : Keeps [.edx, .ebp] b b₃ := G₂.trans (g₃.mono (by decide))
  refine step_key K₃ (by decide) (by decide) (by rw [G₃ _ (by decide), e2]; rfl) fun b₄ K₄ g₄ m₄ => ?_
  have G₄ : Keeps [.edx, .ebp] b b₄ := G₃.trans (g₄.mono (by decide))
  refine step_key K₄ (by decide) (by decide) (by rw [G₄ _ (by decide), e3]; rfl) fun b₅ K₅ g₅ m₅ => ?_
  have G₅ : Keeps [.edx, .ebp] b b₅ := G₄.trans (g₅.mono (by decide))
  refine step_sum _ _ (by decide) fun b₆ e₆ g₆ m₆ => ?_
  rw [G₅ _ (by decide), G₅ _ (by decide), e2, e3] at e₆
  have G₆ : Keeps [.edx, .ebp] b b₆ := G₅.trans (g₆.mono (by decide))
  refine step_key (K₅.mem m₆) (by decide) (by decide) (by rw [e₆]; rfl) fun b₇ K₇ g₇ m₇ => ?_
  have G₇ : Keeps [.edx, .ebp] b b₇ := G₆.trans (g₇.mono (by decide))
  refine step_sum _ _ (by decide) fun b₈ e₈ g₈ m₈ => ?_
  rw [G₇ _ (by decide), G₇ _ (by decide), e0, e2] at e₈
  have G₈ : Keeps [.edx, .ebp] b b₈ := G₇.trans (g₈.mono (by decide))
  refine step_key (K₇.mem m₈) (by decide) (by decide) (by rw [e₈]; rfl) fun b₉ K₉ g₉ m₉ => ?_
  have G₉ : Keeps [.edx, .ebp] b b₉ := G₈.trans (g₉.mono (by decide))
  refine WA.append (WA.mono (Q := fun c => c.g .edi = k.w0 ^^^ k.w2 ∧ Keeps [.edi] b₉ c ∧ c.m = b₉.m) ?_
    fun c₀ ⟨f₀, h₀, n₀⟩ => ?_)
  · refine ⟨_, rfl, ?_, fun r hr => ?_, rfl⟩
    · simp only [A.g_set, ite_true]; rw [g₉ _ (by decide), e₈]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [A.g_set, hr, ite_false]
  have H₀ : Keeps [.edx, .ebp, .edi] b c₀ := (G₉.mono (by decide)).trans (h₀.mono (by decide))
  refine step_sum _ _ (by decide) fun c₁ f₁ h₁ n₁ => ?_
  rw [H₀ _ (by decide), H₀ _ (by decide), e1, e3] at f₁
  refine step_key ((K₉.mem n₀).mem n₁) (by decide) (by decide) (by rw [f₁]; rfl) fun c₂ L₂ h₂ n₂ => ?_
  refine WA.append (WA.mono (Q := fun c => c.g .ebp = kt k 8 ∧ Keeps [.ebp] c₂ c ∧ c.m = c₂.m) ?_
    fun c₃ ⟨f₃, h₃, n₃⟩ => ?_)
  · refine ⟨_, rfl, ?_, fun r hr => ?_, rfl⟩
    · simp only [A.g_set, ite_true]
      rw [h₂ _ (by decide), f₁, h₂ _ (by decide), h₁ _ (by decide), f₀, BitVec.xor_comm]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [A.g_set, hr, ite_false]
  refine (keyWord_ok 8 .ebp (by decide) (by decide) c₃).mono fun c₄ ⟨f₄, n₄, h₄⟩ => ⟨?_, fun j hj => ?_, ?_⟩
  · exact (L₂.mem n₃).word ((congrArg (Cls c₄ (4 * 8)) f₃).mp f₄) n₄
  · rw [n₄ j (by omega), n₃, n₂ j hj, n₁, n₀, m₉ j hj, m₈, m₇ j hj, m₆, m₅ j hj, m₄ j hj, m₃ j hj, m₂, m₁ j hj,
      m₀ j hj, mb]
  · exact gb.trans <| (H₀.mono (by decide)).trans <| (h₁.mono (by decide)).trans <| (h₂.mono (by decide)).trans <|
      (h₃.mono (by decide)).trans (h₄.mono (by decide))

/-! ## The whole function -/

section
variable (s₀ : State)

abbrev hA : Addr := (hP s₀).setWidth 64
abbrev yA : Addr := (yP s₀).setWidth 64
abbrev dA : Addr := (dP s₀).setWidth 64
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yA s₀)

/-- The address of block `i`, in 32 bits. -/
abbrev blk (i : Nat) : BitVec 32 := dP s₀ + BitVec.ofNat 32 (16 * i)

/-- The words of a block. -/
abbrev wd (p : Addr) (o : Nat) : BitVec 32 := bswap (s₀.mem.readW (p + BitVec.ofNat 64 o) 32)

end

/-- The block of four words. -/
abbrev w4 (a b c d : BitVec 32) : BitVec 128 := a ++ b ++ c ++ d

theorem w4_eq (a b c d : BitVec 32) : w4 a b c d = ((a ++ b : BitVec 64) ++ (c ++ d : BitVec 64) : BitVec 128) :=
  words4 a b c d

theorem wd_mem (m : Mem) (p : Addr) :
    w4 (bswap (m.readW (p + BitVec.ofNat 64 0) 32)) (bswap (m.readW (p + BitVec.ofNat 64 4) 32))
      (bswap (m.readW (p + BitVec.ofNat 64 8) 32)) (bswap (m.readW (p + BitVec.ofNat 64 12) 32)) = blockAt m p := by
  have h : Spec.Aes.bytesAt m p 16 =
      [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2), m (p + BitVec.ofNat 64 3),
        m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5), m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7),
        m (p + BitVec.ofNat 64 8), m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
        m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
        m (p + BitVec.ofNat 64 15)] := rfl
  have e : ∀ j : Nat, p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) := fun j => Offset.add_add p j 1
  simp only [bswap_readW, e, Nat.reduceAdd]
  rw [blockAt, h, ofBytes_16, w4_eq, bytes8, bytes8]

theorem wd_block (s₀ : State) (p : Addr) : w4 (wd s₀ p 0) (wd s₀ p 4) (wd s₀ p 8) (wd s₀ p 12) = blockAt s₀.mem p :=
  wd_mem s₀.mem p

theorem w4_xor (a b c d e f g h : BitVec 32) :
    w4 (a ^^^ e) (b ^^^ f) (c ^^^ g) (d ^^^ h) = w4 a b c d ^^^ w4 e f g h := by
  rw [w4_eq, w4_eq, w4_eq, ← Spread.xor_append', ← Spread.xor_append']
  exact BitVec.xor_append.symm

namespace GPre
variable {s₀ : State} (h : GPre s₀)
include h

theorem toScr : Scr s₀ := ⟨by rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..), h.fS⟩
theorem mem_h : hR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.rd]; exact List.mem_cons_self ..
theorem mem_d : dR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.rd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem mem_a : aR s₀ ∈ s₀.rd ++ s₀.wr := by
  rw [h.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem mem_y : yR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.wr]; exact List.mem_append_right _ (List.mem_cons_self ..)

theorem arg_in {i : Nat} (hi : i < 5) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  have hs := h.fSp
  have e : ∀ k < 5, argAddr s₀ k = (s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * k) := fun k hk =>
    addr_eq (x := s₀.gpr .esp) (k := 4 + 4 * k) (by omega)
  rw [e i hi, ← Offset.add_add _ 4 (4 * i)]
  show Region.Contains ⟨argAddr s₀ 0, 20⟩ _ _
  rw [e 0 (by decide)]
  exact Offset.contains_base _ (by omega) (by omega)

end GPre

/-- A load from a region disjoint from `scratch`. -/
theorem ext_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {d : Reg} (hd : ¬ (d = .ecx ∨ d = .esp)) (op : MemOp) {R : Region}
    {p : Addr} (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (sR s₀)) (hp : s.ea op = p) (hc : R.Contains p 4)
    {is : List Instr} {Q : State → Prop}
    (hq : ∀ s', Rel s₀ s' (a.set d (s₀.mem.readW p 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem op) :: is)) s Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, hq _ (h.set hd _)⟩
  show (readSrc s (.mem op)).map _ = _
  rw [readSrc, State.load32, hp, ite_eq_left ⟨R, by rw [h.rd, h.wr]; exact hR, hc⟩,
    h.m.frame.readW hc (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hdis) (by decide)]
  rfl

/-- A load of an argument. -/
theorem arg_ok {s₀ s : State} {a : A} (hp : GPre s₀) (h : Rel s₀ s a) (i : Nat) (hi : i < 5) :
    WP isa (.block [.mov .edx (.mem (argOp i))]) s fun s' => Rel s₀ s' (a.set .edx (arg s₀ i)) :=
  ext_ok h (by decide) (argOp i) hp.mem_a hp.aS (p := argAddr s₀ i)
    (by rw [State.ea, argOp, at_, h.g, h.esp]; rfl) (hp.arg_in hi) fun _ r => WP.block_nil r

/-- The four words of a block, as loaded. -/
structure Blk (s₀ : State) (p : Addr) (a a' : A) : Prop where
  w3 : bswap (a'.g .eax) = wd s₀ p 0
  w2 : bswap (a'.g .ebx) = wd s₀ p 4
  w1 : bswap (a'.g .esi) = wd s₀ p 8
  w0 : bswap (a'.g .edi) = wd s₀ p 12
  k : Keeps [.eax, .ebx, .esi, .edi] a a'
  m : a'.m = a.m

theorem loadBlk_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {R : Region}
    {p : BitVec 32} (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (sR s₀)) (hp : a.g .edx = p) (hf : p.toNat + 16 ≤ 2 ^ 32)
    (hc : ∀ o ≤ 12, R.Contains (p.setWidth 64 + BitVec.ofNat 64 o) 4) :
    WP isa (.block loadBlk) s fun s' => ∃ a', Rel s₀ s' a' ∧ Blk s₀ (p.setWidth 64) a a' := by
  have he : ∀ {s' : State} {a' : A} (o : Nat), o ≤ 12 → Rel s₀ s' a' → a'.g .edx = p →
      s'.ea (at_ .edx o) = p.setWidth 64 + BitVec.ofNat 64 o := fun o ho h' hp' => by
    rw [State.ea, at_, h'.g, hp']; exact addr_eq (x := p) (k := o) (by omega)
  refine ext_ok h (by decide) (at_ .edx 0) hR hdis (he 0 (by decide) h hp) (hc 0 (by decide)) fun s₁ r₁ => ?_
  refine ext_ok r₁ (by decide) (at_ .edx 4) hR hdis (he 4 (by decide) r₁ hp) (hc 4 (by decide)) fun s₂ r₂ => ?_
  refine ext_ok r₂ (by decide) (at_ .edx 8) hR hdis (he 8 (by decide) r₂ hp) (hc 8 (by decide)) fun s₃ r₃ => ?_
  refine ext_ok r₃ (by decide) (at_ .edx 12) hR hdis (he 12 (by decide) r₃ hp) (hc 12 (by decide))
    fun s₄ r₄ => WP.block_nil ⟨_, r₄, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

/-! ### The invariant -/

/-- The block of the words `y₃` to `y₀` in `scratch`. -/
def yOf (a : A) : BitVec 128 := w4 (a.m 43) (a.m 42) (a.m 41) (a.m 40)

structure InvA (s₀ : State) (i : Nat) (a : A) : Prop where
  key : KeysTo a (kws (wd s₀ (hA s₀) 0) (wd s₀ (hA s₀) 4) (wd s₀ (hA s₀) 8) (wd s₀ (hA s₀) 12)) 9
  sav : ∀ q ∈ saved, a.m q.2 = s₀.gpr q.1
  y : yOf a = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dA s₀) i)
  dp : a.m dpS = blk s₀ i
  n : a.m nS = BitVec.ofNat 32 (nBlk s₀ - i)

def Inv (s₀ : State) (i : Nat) (s : State) : Prop := i ≤ nBlk s₀ ∧ ∃ a, Rel s₀ s a ∧ InvA s₀ i a

/-- A block's arithmetic, its words in registers. -/
def core : List Instr :=
  addX ++ mul64 [yS] [yS + 1] 0 lS ++ mul64 [yS + 2] [yS + 3] 3 hS ++ mul64 [yS, yS + 2] [yS + 1, yS + 3] 6 cS ++ reduce

theorem core_ok {a : A} {h3 h2 h1 h0 : BitVec 32} (hK : KeysTo a (kws h3 h2 h1 h0) 9) :
    WA core a fun a' =>
      yOf a' = Spec.Gcm.mul (w4 (bswap (a.g .eax) ^^^ a.m 43) (bswap (a.g .ebx) ^^^ a.m 42) (bswap (a.g .esi) ^^^ a.m 41)
        (bswap (a.g .edi) ^^^ a.m 40)) (w4 h3 h2 h1 h0) ∧
      (∀ k, k < 36 ∨ 56 ≤ k → a'.m k = a.m k) ∧ Keeps work a a' := by
  have hKm : ∀ {b : A}, (∀ k < 36, b.m k = a.m k) → KeysTo b (kws h3 h2 h1 h0) 9 := fun {b} hb t ht j hj => by
    rw [hb _ (by omega), hK t ht j hj]
  have ys : ∀ x : Nat, 40 ≤ x ∧ x < 44 → Ys [x] := fun x hx k hk => by
    rw [List.mem_singleton] at hk; subst hk; exact hx
  have ys2 : ∀ x y : Nat, 40 ≤ x ∧ x < 44 → 40 ≤ y ∧ y < 44 → Ys [x, y] := fun x y hx hy k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hx
    · exact hy
  rw [core, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append ((addX_ok a).mono fun b ⟨⟨x3, x2, x1, x0⟩, mb, gb⟩ => ?_)
  have Kb := hKm (b := b) fun k hk => mb k (.inl (by omega))
  refine WA.append ((mul64_ok 40 [] 41 [] 0 44 (by decide) (.inl rfl) _ _ b (ys 40 (by decide)) (ys 41 (by decide))
    ⟨Kb 0 (by decide), Kb 1 (by decide), Kb 2 (by decide)⟩ rfl).mono fun c ⟨pc, gc, mc⟩ => ?_)
  have Kc := hKm (b := c) fun k hk => by rw [mc k (by omega) (by omega), mb k (by omega)]
  refine WA.append ((mul64_ok 42 [] 43 [] 3 48 (by decide) (.inr (.inl rfl)) _ _ c (ys 42 (by decide)) (ys 43 (by decide))
    ⟨Kc 3 (by decide), Kc 4 (by decide), Kc 5 (by decide)⟩ rfl).mono fun d ⟨pd, gd, md⟩ => ?_)
  have Kd := hKm (b := d) fun k hk => by rw [md k (by omega) (by omega), mc k (by omega) (by omega), mb k (by omega)]
  have Md : ∀ k, 40 ≤ k → k < 44 → d.m k = b.m k := fun k h h' => by
    rw [md k (by omega) (by omega), mc k (by omega) (by omega)]
  refine WA.append ((mul64_ok 40 [42] 41 [43] 6 52 (by decide) (.inr (.inr rfl)) _ _ d (ys2 40 42 (by decide) (by decide))
    (ys2 41 43 (by decide) (by decide)) ⟨Kd 6 (by decide), Kd 7 (by decide), Kd 8 (by decide)⟩
    (BitVec.xor_assoc (d.m 40 ^^^ d.m 42) (d.m 41) (d.m 43))).mono fun e ⟨pe, ge, me⟩ => ?_)
  have pc' : At e 44 _ := ⟨by rw [me _ (by decide) (by decide), md _ (by decide) (by decide)]; exact pc.1,
    by rw [me _ (by decide) (by decide), md _ (by decide) (by decide)]; exact pc.2.1,
    by rw [me _ (by decide) (by decide), md _ (by decide) (by decide)]; exact pc.2.2.1,
    by rw [me _ (by decide) (by decide), md _ (by decide) (by decide)]; exact pc.2.2.2⟩
  have pd' : At e 48 _ := ⟨by rw [me _ (by decide) (by decide)]; exact pd.1, by rw [me _ (by decide) (by decide)]; exact pd.2.1,
    by rw [me _ (by decide) (by decide)]; exact pd.2.2.1, by rw [me _ (by decide) (by decide)]; exact pd.2.2.2⟩
  refine (reduce_ok pc' pd' pe).mono fun f ⟨⟨z0, z1, z2, z3⟩, mf, gf⟩ => ⟨?_, fun k hk => ?_, ?_⟩
  · have y42 : sumOf c.m [42] = b.m 42 := mc _ (by decide) (by decide)
    have y43 : sumOf c.m [43] = b.m 43 := mc _ (by decide) (by decide)
    have y4 : sumOf d.m [40, 42] = b.m 40 ^^^ b.m 42 := by
      show d.m 40 ^^^ d.m 42 = _
      rw [Md _ (by decide) (by decide), Md _ (by decide) (by decide)]
    have y5 : sumOf d.m [41, 43] = b.m 41 ^^^ b.m 43 := by
      show d.m 41 ^^^ d.m 43 = _
      rw [Md _ (by decide) (by decide), Md _ (by decide) (by decide)]
    rw [y42, y43, y4, y5] at z0 z1 z2 z3
    rw [yOf, z0, z1, z2, z3, ← x3, ← x2, ← x1, ← x0, w4_eq, w4_eq, w4_eq]
    exact mul_words32 Spread.isMul_mul32x ..
  · rw [mf k (by omega), me k (by omega) (by omega), md k (by omega) (by omega), mc k (by omega) (by omega), mb k (by omega)]
  · exact gb.trans (gc.trans (gd.trans (ge.trans gf)))

/-- A test of `eax`. -/
theorem test_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {k : Nat} (hk : k < 2 ^ 32) (hn : a.g .eax = BitVec.ofNat 32 k) :
    WP isa (.block test) s fun s' => Rel s₀ s' a ∧ s'.zf = some (decide (k = 0)) := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨h.flags .., ?_⟩⟩
  show some (s.gpr .eax &&& s.gpr .eax == 0) = _
  rw [BitVec.and_self, h.g, hn, Wp.ofNat_beq_zero hk]

theorem load_ok (d : Reg) (hd : ¬ (d = .ecx ∨ d = .esp)) (k : Nat) (hk : k < 64) (a : A) :
    WA [ld d k] a fun a' => a'.g d = a.m k ∧ Keeps [d] a a' ∧ a'.m = a.m := by
  simp only [WA, ld, evalA, stepA, srcA, hd, slotOf_slot hk, Option.map_some, Option.bind_some, A.g_set, A.m_set, ite_false,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_set, hr, ite_false]

theorem advance_ok (a : A) :
    WA [.alu .add .edx (.imm 16), st dpS .edx] a fun a' => a'.m dpS = a.g .edx + 16 ∧
      (∀ k, k ≠ dpS → a'.m k = a.m k) ∧ Keeps [.edx] a a' := by
  simp only [WA, st, dpS, evalA, stepA, srcA, slotOf_slot (show 60 < 64 by decide), reduceCtorEq, or_self, Option.map_some,
    Option.bind_some, A.g_set, A.m_set, A.m_put, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun k hk => ite_eq_right hk, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_put, A.g_set, hr, ite_false]

theorem next_ok (a : A) :
    WA next a fun a' => a'.m nS = a.m nS + 0xffffffff ∧ a'.g .eax = a.m nS + 0xffffffff ∧
      (∀ k, k ≠ nS → a'.m k = a.m k) ∧ Keeps [.eax] a a' := by
  simp only [WA, next, ld, st, nS, evalA, stepA, srcA, slotOf_slot (show 61 < 64 by decide), reduceCtorEq, or_self,
    Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, fun k hk => ite_eq_right hk, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_put, A.g_set, hr, ite_false]

theorem ofNat_dec {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 32) : BitVec.ofNat 32 k + 0xffffffff = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xffffffff : BitVec 32).toNat = 2 ^ 32 - 1 from rfl]
  omega

theorem body_ok {s₀ : State} (hp : GPre s₀) {i : Nat} (hi : i < nBlk s₀) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (i + 1) = 0)) := by
  have hf := hp.fD
  have hn : nBlk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  obtain ⟨-, a, hr, ha⟩ := hI
  have hbody : body = [ld .edx dpS] ++ (loadBlk ++ ([.alu .add .edx (.imm 16), st dpS .edx] ++
      (core ++ (next ++ test)))) := by simp only [body, core, loadX, List.append_assoc]
  obtain ⟨hba, hbf⟩ : (blk s₀ i).setWidth 64 = dA s₀ + BitVec.ofNat 64 (16 * i) ∧ (blk s₀ i).toNat + 16 ≤ 2 ^ 32 := by
    have e : (blk s₀ i).toNat = (dP s₀).toNat + 16 * i := by
      rw [blk, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact ⟨addr_eq (by omega), by omega⟩
  rw [hbody, WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr hr (load_ok .edx (by decide) dpS (by decide) a)) fun s₁ ⟨a₁, r₁, e₁, k₁, m₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadBlk_ok r₁ hp.mem_d hp.dDS (e₁.trans ha.dp) hbf (fun o ho => by
    rw [hba, Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega))) fun s₂ ⟨a₂, r₂, B⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₂ (advance_ok a₂)) fun s₃ ⟨a₃, r₃, e₃, m₃, k₃⟩ => ?_
  have m₃' : ∀ k, k ≠ dpS → a₃.m k = a.m k := fun k hk => by rw [m₃ k hk, B.m, m₁]
  have key₃ : KeysTo a₃ _ 9 := fun t ht j hj => by
    rw [m₃' _ (by unfold dpS; omega), ha.key t ht j hj]
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₃ (core_ok key₃)) fun s₄ ⟨a₄, r₄, y₄, m₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₄ (next_ok a₄)) fun s₅ ⟨a₅, r₅, n₅, n₅', m₅, k₅⟩ => ?_
  have hcnt : a₄.m nS + 0xffffffff = BitVec.ofNat 32 (nBlk s₀ - (i + 1)) := by
    rw [m₄ nS (by decide), m₃' nS (by decide), ha.n]
    exact ofNat_dec (by omega) (by omega)
  have m₅' : ∀ k, 56 ≤ k → k ≠ dpS → k ≠ nS → a₅.m k = a.m k := fun k h1 h2 h3 => by
    rw [m₅ k h3, m₄ k (.inr h1), m₃' k h2]
  have m₅'' : ∀ k, k < 36 → a₅.m k = a.m k := fun k h => by
    rw [m₅ k (by unfold nS; omega), m₄ k (.inl h), m₃' k (by unfold dpS; omega)]
  refine WP.mono (test_ok r₅ (by omega) (n₅'.trans hcnt)) fun s₆ ⟨r₆, z₆⟩ => ⟨⟨hi, a₅, r₆, ?_⟩, z₆⟩
  refine ⟨fun t ht j hj => ?_, fun q hq => ?_, ?_, ?_, n₅.trans hcnt⟩
  · rw [m₅'' _ (by omega), ha.key t ht j hj]
  · have hq' : ∀ q ∈ saved, 56 ≤ q.2 ∧ q.2 ≠ dpS ∧ q.2 ≠ nS := by decide
    obtain ⟨h1, h2, h3⟩ := hq' q hq
    rw [m₅' _ h1 h2 h3, ha.sav q hq]
  · have e : yOf a₅ = yOf a₄ := by
      rw [yOf, m₅ 43 (by decide), m₅ 42 (by decide), m₅ 41 (by decide), m₅ 40 (by decide)]; rfl
    rw [e, y₄, m₃' 43 (by decide), m₃' 42 (by decide), m₃' 41 (by decide), m₃' 40 (by decide), k₃ _ (by decide),
      k₃ _ (by decide), k₃ _ (by decide), k₃ _ (by decide), B.w3, B.w2, B.w1, B.w0, w4_xor, wd_block, wd_block, hba,
      ghashFrom_blocksAt_succ, ← ha.y, BitVec.xor_comm]
    rfl
  · rw [m₅ dpS (by decide), m₄ dpS (by decide), e₃, B.k _ (by decide), e₁, ha.dp, blk, blk, BitVec.add_assoc, Nat.mul_succ,
      BitVec.ofNat_add]
    rfl

/-! ### The prologue and the epilogue -/

theorem save_ok (a : A) : WA save a fun a' => (∀ q ∈ saved, a'.m q.2 = a.g q.1) ∧ a'.g = a.g := by
  simp (config := {decide := true}) only [WA, save, saved, st, List.map_cons, List.map_nil, evalA, stepA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left', List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ite_true, ite_false, and_self]

theorem st_ok (k : Nat) (hk : k < 64) (r : Reg) (a : A) :
    WA [st k r] a fun a' => a'.m k = a.g r ∧ (∀ j, j ≠ k → a'.m j = a.m j) ∧ a'.g = a.g := by
  simp only [WA, st, evalA, stepA, slotOf_slot hk, Option.map_some, Option.bind_some, A.g_put, A.m_put,
    Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun j hj => ite_eq_right hj, trivial⟩

theorem rev_ok (a : A) :
    WA revBlk a fun a' => (a'.g .eax = bswap (a.g .eax) ∧ a'.g .ebx = bswap (a.g .ebx) ∧ a'.g .esi = bswap (a.g .esi) ∧
      a'.g .edi = bswap (a.g .edi)) ∧ Keeps [.eax, .ebx, .esi, .edi] a a' ∧ a'.m = a.m := by
  simp only [WA, revBlk, evalA, stepA, reduceCtorEq, or_self, Option.bind_some, A.g_set, A.m_set, ite_false, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨trivial, trivial, trivial, trivial⟩, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [A.g_set, hr, ite_false]

theorem storeYs_ok (a : A) :
    WA storeYs a fun a' => yOf a' = w4 (a.g .eax) (a.g .ebx) (a.g .esi) (a.g .edi) ∧
      (∀ k, k < 40 ∨ 44 ≤ k → a'.m k = a.m k) ∧ a'.g = a.g := by
  simp (config := {decide := true}) only [WA, storeYs, yOf, st, yS, evalA, stepA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun k hk => ?_, trivial⟩
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem revKey_ok {s₀ : State} {a₁ a : A} {p : Addr} (B : Blk s₀ p a₁ a) :
    WA (revBlk ++ keyCode) a fun a' => KeysTo a' (kws (wd s₀ p 0) (wd s₀ p 4) (wd s₀ p 8) (wd s₀ p 12)) 9 ∧
      (∀ j, 36 ≤ j → a'.m j = a.m j) ∧ Keeps work a a' := by
  refine WA.append ((rev_ok a).mono fun b ⟨⟨e3, e2, e1, e0⟩, gb, mb⟩ => ?_)
  refine (keyCode_ok b).mono fun c ⟨K, mc, gc⟩ => ⟨?_, fun j hj => by rw [mc j hj, mb], (gb.mono (by decide)).trans gc⟩
  rwa [e3, e2, e1, e0, B.w3, B.w2, B.w1, B.w0] at K

theorem revY_ok {s₀ : State} {a₁ a : A} {p : Addr} (B : Blk s₀ p a₁ a) :
    WA (revBlk ++ (storeYs ++ [ld .eax nS])) a fun a' => yOf a' = w4 (wd s₀ p 0) (wd s₀ p 4) (wd s₀ p 8) (wd s₀ p 12) ∧
      (∀ k, k < 40 ∨ 44 ≤ k → a'.m k = a.m k) ∧ a'.g .eax = a.m nS := by
  refine WA.append ((rev_ok a).mono fun b ⟨⟨e3, e2, e1, e0⟩, _, mb⟩ => ?_)
  refine WA.append ((storeYs_ok b).mono fun c ⟨y, mc, _⟩ => ?_)
  refine (load_ok .eax (by decide) nS (by decide) c).mono fun d ⟨e, _, md⟩ => ⟨?_, fun k hk => by rw [md, mc k hk, mb], ?_⟩
  · rw [yOf, md]; refine Eq.trans y ?_
    rw [e3, e2, e1, e0, B.w3, B.w2, B.w1, B.w0]
  · rw [e, mc _ (by decide), mb]

theorem prologue_ok {s₀ : State} (hp : GPre s₀) :
    WP isa (.block prologue) s₀ fun s' => Inv s₀ 0 s' ∧ s'.zf = some (decide (nBlk s₀ = 0)) := by
  have hpr : prologue = .mov .ecx (.mem (argOp 4)) :: (save ++ ([.mov .edx (.mem (argOp 2))] ++ ([st dpS .edx] ++
      ([.mov .edx (.mem (argOp 3))] ++ ([st nS .edx] ++ ([.mov .edx (.mem (argOp 0))] ++ (loadBlk ++ ((revBlk ++ keyCode) ++
      ([.mov .edx (.mem (argOp 1))] ++ (loadBlk ++ ((revBlk ++ (storeYs ++ [ld .eax nS])) ++ test))))))))))) := by
    simp only [prologue, List.append_assoc, List.cons_append, List.nil_append]
  have h0 : exec (.mov .ecx (.mem (argOp 4))) s₀ = some (s₀.setReg .ecx (sP s₀)) := by
    show (readSrc s₀ (.mem (argOp 4))).map _ = _
    rw [readSrc, State.load32, show s₀.ea (argOp 4) = argAddr s₀ 4 from rfl,
      ite_eq_left ⟨aR s₀, hp.mem_a, hp.arg_in (by decide)⟩]
    rfl
  have r₀ : Rel s₀ (s₀.setReg .ecx (sP s₀)) ⟨(s₀.setReg .ecx (sP s₀)).gpr,
      fun k => s₀.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32⟩ :=
    ⟨rfl, Slots32.init _ _ _, rfl, rfl, rfl, rfl⟩
  have gs : ∀ r, r ≠ .ecx → (s₀.setReg .ecx (sP s₀)).gpr r = s₀.gpr r := fun r hr => ite_eq_right hr
  rw [hpr]
  refine WP.block_cons_iff.mpr ⟨_, h0, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₀ (save_ok _)) fun s₁ ⟨a₁, r₁, hs, hg⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hp r₁ 2 (by decide)) fun s₂ r₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₂ (st_ok dpS (by decide) .edx _)) fun s₃ ⟨a₃, r₃, d₃, m₃, g₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hp r₃ 3 (by decide)) fun s₄ r₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₄ (st_ok nS (by decide) .edx _)) fun s₅ ⟨a₅, r₅, n₅, m₅, g₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hp r₅ 0 (by decide)) fun s₆ r₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadBlk_ok r₆ hp.mem_h hp.dHS (p := hP s₀) rfl hp.fH
    (fun o ho => Offset.contains_base _ (by omega) (by omega))) fun s₇ ⟨a₇, r₇, B⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₇ (revKey_ok B)) fun s₈ ⟨a₈, r₈, K₈, m₈, g₈⟩ => ?_
  rw [B.m] at m₈
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hp r₈ 1 (by decide)) fun s₉ r₉ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadBlk_ok r₉ hp.mem_y hp.dYS (p := yP s₀) rfl hp.fY
    (fun o ho => Offset.contains_base _ (by omega) (by omega))) fun s₁₀ ⟨a₁₀, r₁₀, C⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₁₀ (revY_ok C)) fun s₁₁ ⟨a₁₁, r₁₁, y₁₁, m₁₁, n₁₁⟩ => ?_
  rw [C.m] at m₁₁ n₁₁
  have hm : ∀ k, 44 ≤ k → a₁₁.m k = a₅.m k := fun k hk => (m₁₁ k (.inr hk)).trans (m₈ k (by omega))
  have hn₅ : a₅.m nS = BitVec.ofNat 32 (nBlk s₀) := by
    rw [n₅, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine WP.mono (test_ok r₁₁ (arg s₀ 3).isLt (n₁₁.trans ((m₈ nS (by decide)).trans hn₅))) fun s₁₂ ⟨r₁₂, z₁₂⟩ =>
    ⟨⟨Nat.zero_le _, a₁₁, r₁₂, fun t ht j hj => ?_, fun q hq => ?_, ?_, ?_, (hm _ (by decide)).trans hn₅⟩, z₁₂⟩
  · exact (m₁₁ _ (by omega)).trans (K₈ t ht j hj)
  · have hq' : ∀ q ∈ saved, 44 ≤ q.2 ∧ q.1 ≠ .ecx ∧ q.2 ≠ nS ∧ q.2 ≠ dpS := by decide
    obtain ⟨h1, h2, h3, h4⟩ := hq' q hq
    rw [hm _ h1, m₅ _ h3]
    refine (m₃ _ h4).trans ((hs q hq).trans (gs _ h2))
  · rw [ghashFrom_blocksAt_zero]; exact y₁₁.trans (wd_block s₀ (yA s₀))
  · rw [hm _ (by decide), m₅ _ (by decide)]
    refine Eq.trans d₃ ?_
    rw [blk, Nat.mul_zero]; exact (BitVec.add_zero _).symm

theorem finish_ok (a : A) :
    WA finish a fun a' => (a'.m 40 = bswap (a.m 43) ∧ a'.m 41 = bswap (a.m 42) ∧ a'.m 42 = bswap (a.m 41) ∧
        a'.m 43 = bswap (a.m 40)) ∧ (∀ q ∈ saved, a'.g q.1 = a.m q.2) ∧ Keeps work a a' := by
  simp (config := {decide := true}) only [WA, finish, revBlk, restore, saved, ld, st, yS, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, evalA, stepA, srcA, slotOf_slot, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_self, true_and]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [A.g_put, A.g_set, hr, ite_false]

theorem epilogue_ok {s₀ : State} (hp : GPre s₀) {s : State} (hI : Inv s₀ (nBlk s₀) s) :
    WP isa (.block epilogue) s fun s' => abiPreserved s₀ s' ∧ ghashX86.post s₀ s' := by
  obtain ⟨-, a, r, ha⟩ := hI
  have hfs := hp.fS
  have hfy := hp.fY
  have hfp := hp.fSp
  rw [epilogue, WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r (finish_ok a)) fun s₁ ⟨a₁, r₁, ⟨m0, m1, m2, m3⟩, hs, hk⟩ => ?_
  refine (WP.block_append_iff (l₁ := [_])).mpr ?_
  refine WP.mono (arg_ok hp r₁ 1 (by decide)) fun s₂ r₂ => ?_
  have hsc : s₂.ea (slot yS) = (sP s₀).setWidth 64 + BitVec.ofNat 64 160 := by
    rw [State.ea, slot, at_, r₂.g, r₂.ecx]; exact addr_eq (x := sP s₀) (k := 160) (by omega)
  have hl : exec (.movdquLoad .xmm0 (slot yS)) s₂ = some (s₂.setXmm .xmm0
      (s₂.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 160) 128)) := by
    show (State.load128 _ _).map _ = _
    rw [State.load128, hsc, ite_eq_left ⟨sR s₀, List.mem_append_right _ (by rw [r₂.wr]; exact hp.toScr.mem),
      Offset.contains_base _ (by decide) (by decide)⟩]
    rfl
  refine WP.block_cons_iff.mpr ⟨_, hl, ?_⟩
  generalize hv : s₂.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 160) 128 = v
  have hst : exec (.movdquStore (at_ .edx 0) .xmm0) (s₂.setXmm .xmm0 v) =
      some { s₂.setXmm .xmm0 v with mem := s₂.mem.writeW (yA s₀) v } := by
    show State.store128 _ _ _ = _
    have he : (s₂.setXmm .xmm0 v).ea (at_ .edx 0) = yA s₀ := by
      show (s₂.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
      rw [r₂.g]
      exact congrArg _ (BitVec.add_zero _)
    rw [State.store128, he, ite_eq_left ⟨yR s₀, by
      show _ ∈ s₂.wr; rw [r₂.wr, hp.wr]; exact List.mem_cons_self .., Region.contains_self _ _⟩]
    rfl
  refine WP.block_cons_iff.mpr ⟨_, hst, WP.block_nil ⟨⟨fun q hq => ?_, ?_⟩, ?_⟩⟩
  · have hsv : ∀ p ∈ saved, a₁.g p.1 = s₀.gpr p.1 := fun p hp => by rw [hs p hp, ha.sav p hp]
    have hq' : ∀ q ∈ calleeSaved, q ≠ .edx ∧ (q = .esp ∨ ∃ p ∈ saved, p.1 = q) := by decide
    show s₂.gpr q = _
    obtain ⟨hne, rfl | ⟨p, hp', rfl⟩⟩ := hq' q hq
    · rw [r₂.g, r₂.esp]
    · rw [r₂.g, A.g_set, ite_eq_right hne, hsv p hp']
  · show (s₂.mem.writeW (yA s₀) v).readW _ _ = _
    rw [Mem.readW_writeW_sep (hp.rY.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
      r₂.m.frame.readW (r := rR s₀) (Region.contains_self _ _)
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.rS) (by decide)]
  · show blockAt (s₂.mem.writeW (yA s₀) v) (yA s₀) = _
    rw [blockAt_eq, show (s₂.mem.writeW (yA s₀) v).readW (yA s₀) 128 = v from Mem.readW_writeW_self _ _ 16 v (by decide), ← hv, ← blockAt_eq, ← wd_mem, Offset.add_add, Offset.add_add, Offset.add_add,
      Offset.add_add]
    have bb : ∀ v : BitVec 32, bswap (bswap v) = v := Proof.Cmac.byteRev32_byteRev32
    have g : ∀ k < 64, s₂.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32 = a₁.m k := r₂.m.get
    rw [show 160 + 0 = 4 * 40 from rfl, show 160 + 4 = 4 * 41 from rfl, show 160 + 8 = 4 * 42 from rfl,
      show 160 + 12 = 4 * 43 from rfl, g 40 (by decide), g 41 (by decide), g 42 (by decide), g 43 (by decide), m0, m1, m2, m3,
      bb, bb, bb, bb]
    exact ha.y

theorem correct {s₀ : State} (hp : GPre s₀) :
    WP isa ghash s₀ fun s' => abiPreserved s₀ s' ∧ ghashX86.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (nBlk s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (nBlk s₀ = 0)) (by simp only [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nBlk s₀ = 0 := of_decide_eq_true h
    exact WP.block_nil (h0.symm ▸ hI)
  · have h0 : 0 < nBlk s₀ := Nat.pos_of_ne_zero (of_decide_eq_false h)
    let I : Nat → State → Prop := fun m s => ∃ i, m = nBlk s₀ - i ∧ i < nBlk s₀ ∧ Inv s₀ i s
    have hstep : ∀ m s, I m s → WP isa (.block body) s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (nBlk s₀) s') ∨ (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body_ok hp hi hI) fun s' ⟨hI', hz'⟩ => ?_
      by_cases hl : nBlk s₀ - (i + 1) = 0
      · have : i + 1 = nBlk s₀ := by omega
        exact .inl ⟨by simp only [eval, hz', hl, decide_true, Option.map_some, Bool.not_true], this ▸ hI'⟩
      · exact .inr ⟨by simp only [eval, hz', hl, decide_false, Option.map_some, Bool.not_false], nBlk s₀ - (i + 1),
          by omega, i + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (nBlk s₀) s₁ ⟨0, rfl, h0, hI⟩

theorem ghash_correct (s : State) (hs : ghashX86.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86.ghash s t s' ∧ abiPreserved s s' ∧ ghashX86.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (GPre.of hs)
  exact ⟨t, s', he, h.1, h.2⟩

theorem ghash_ct : ConstantTime isa ghashX86.pre ghashX86.pub Impl.Gcm.X86.ghash :=
  VG.Taint.constantTime (A := sseTaint) ghτ₀ (fun _ _ h₁ h₂ hp => gh_agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Gcm.X86
