module

import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Cmp
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Sha1
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Pbkdf2.Sha1.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.Sha1Words

/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the frame

Untrusted: everything here is checked by Lean. The precondition is the one
of every Merkle–Damgård hash function's iteration (`Pre`,
`Proof/Pbkdf2/RISCV64/Iterate.lean`), for SHA-1's sizes (`Sha1.it`), and so
are the parts of the scratch space (`sc`, `sc_contains`, …): the frame is
`scratch` rounded up to a multiple of 8, of which the code uses 164 bytes.
`Hs` says the frame holds the key's two hash values; `LI` is the loop's
invariant, with `m` steps left, `U`'s words in `A` and `T`'s in the frame.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes key up tp scr nn sc scR keyR uR tR sc_contains sc_al sc_add pad_le)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word)
open VG.Proof.Pbkdf2.Sha1Words (wstep wIter)

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := Spec.Sha1.stateAt s₀.mem (key s₀)
abbrev Ho : HashValue := Spec.Sha1.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 84)

/-- The word at offset `d` of the frame. -/
abbrev fw (m : Mem) (d : Nat) : Word := m.readW (sc s₀ + BitVec.ofNat 64 d) 32

end

/-- The frame holds the key's two hash values. -/
structure Hs (s₀ : State) (m : Mem) : Prop where
  hi : ∀ k < 5, fw s₀ m (hiO + 4 * k) = (Hi s₀)[k]!
  ho : ∀ k < 5, fw s₀ m (hoO + 4 * k) = (Ho s₀)[k]!

/-- The loop's invariant, with `m` steps left before the final `T`, `R`. -/
structure LI (Wi : Nat) (s₀ : State) (R : HashValue) (m : Nat) (s : State) : Prop where
  b : s.gpr B = sc s₀
  n : s.gpr N = BitVec.ofNat 64 m
  tp : s.gpr TP = tp s₀
  xy : ∃ x y : HashValue, (∀ k < 5, (s.gpr (A.getD k .t0)).setWidth 32 = x[k]!) ∧
    (∀ k < 5, fw s₀ s.mem (tO + 4 * k) = y[k]!) ∧ wIter (Hi s₀) (Ho s₀) m x y = R
  hs : Hs s₀ s.mem
  saved : Spill.Saved (sc s₀) s₀.gpr saved s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scR Wi s₀] s₀.mem s.mem

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

omit hp in
theorem fc {d n : Nat} (h : d + n ≤ 164) : (scR Wi s₀).Contains (sc s₀ + BitVec.ofNat 64 d) n :=
  sc_contains hz (by have := hz.fits; simp only [it] at this; omega)

theorem fin {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (h : d + n ≤ 164) :
    InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) n :=
  ⟨scR Wi s₀, by rw [hwr, hp.wr]; simp, fc hz h⟩

theorem frd {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat} (h : d + n ≤ 164) :
    InRegions (s.rd ++ s.wr) (sc s₀ + BitVec.ofNat 64 d) n :=
  ⟨scR Wi s₀, by rw [hrd, hwr, hp.rd, hp.wr]; simp, fc hz h⟩

end

theorem fal (s₀ : State) {d : Nat} (h : d % 4 = 0) : (sc s₀ + BitVec.ofNat 64 d).toNat % 4 = 0 :=
  Align.al_add sc_al (by decide) h

theorem fsep (s₀ : State) {a b : Nat} (h : a + 4 ≤ b ∨ b + 4 ≤ a) (ha : a + 4 ≤ 164) (hb : b + 4 ≤ 164) :
    Mem.Sep (sc s₀ + BitVec.ofNat 64 a) 4 (sc s₀ + BitVec.ofNat 64 b) 4 :=
  Offset.sep _ h (by omega) (by omega)

/-- A word of the frame after a word written elsewhere in it. -/
theorem fw_write (s₀ : State) (m : Mem) {a b : Nat} (v : Word) (h : a + 4 ≤ b ∨ b + 4 ≤ a) (ha : a + 4 ≤ 164)
    (hb : b + 4 ≤ 164) : fw s₀ (m.writeW (sc s₀ + BitVec.ofNat 64 b) v) a = fw s₀ m a :=
  Mem.readW_writeW_sep (fsep s₀ h ha hb) (by decide)

/-- The saved registers' slots, apart from the words. -/
theorem slot_word (s₀ : State) {d a : Nat} (hd : d + 8 ≤ 104) (ha : 104 ≤ a) (ha' : a + 4 ≤ 164) :
    Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 d, 8⟩ ⟨sc s₀ + BitVec.ofNat 64 a, 4⟩ :=
  Offset.disjoint _ (by omega) (by omega) (by omega)

theorem saved_bound : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 104 := by decide

/-- A word written in the frame keeps the saved registers. -/
theorem saved_write {s₀ : State} {m : Mem} (h : Spill.Saved (sc s₀) s₀.gpr saved m) {a : Nat} (v : Word)
    (ha : 104 ≤ a) (ha' : a + 4 ≤ 164) :
    Spill.Saved (sc s₀) s₀.gpr saved (m.writeW (sc s₀ + BitVec.ofNat 64 a) v) :=
  h.frame (rs := [⟨sc s₀ + BitVec.ofNat 64 a, 4⟩])
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact slot_word s₀ (saved_bound p hp).2 ha ha'

end VG.Proof.Pbkdf2.Sha1.RISCV64
