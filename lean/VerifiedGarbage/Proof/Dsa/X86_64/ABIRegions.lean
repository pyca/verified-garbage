module
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! # Scratch prefixes and stack-argument regions used by the DSA ABI -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem source_shrink {s : State} {B p : Addr} {Z n : Nat} {bs : List Byte}
    (h : Src s B Z p bs) (hn : n ≤ Z) : Src s B n p bs :=
  ⟨h.rd, h.val, fun i hi => Nat.le_trans hn (h.out i hi)⟩

theorem scratch_prefix {s : State} {B : Addr} {Z n : Nat} (h : Scr s B Z) (hn : n ≤ Z) (hp : 0 < n) :
    Scr s B n := by
  have hs := h.sub (o := 0) (by omega : 0 + n ≤ Z) hp
  simpa [off] using hs

theorem stackWord_address (s : State) {j : Nat} (hj : 1 ≤ j) :
    off (s.gpr .rsp) (8 * j) = stackArgAddr s (j - 1) := by
  unfold off stackArgAddr
  congr 1
  congr 1
  omega

theorem stackArg_base (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega]

theorem stackArg_byte (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [stackArg_base, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem stackWord_read {s : State} {count j : Nat}
    (h : (⟨stackArgAddr s 0, 8 * count⟩ : Region) ∈ s.rd ++ s.wr)
    (hj : 1 ≤ j) (hbound : j ≤ count) (hn : 8 * count ≤ 2 ^ 64) :
    InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * j)) 8 := by
  rw [stackWord_address s hj, stackArg_base s (j - 1)]
  exact ⟨_, h, Offset.contains_base _ (by omega) (by omega)⟩

theorem stackWord_separate {s : State} {B : Addr} {Z count j : Nat}
    (h : (⟨B, Z⟩ : Region).Disjoint ⟨stackArgAddr s 0, 8 * count⟩)
    (hj : 1 ≤ j) (hbound : j ≤ count) (hn : 8 * count ≤ 2 ^ 64) :
    ∀ i < 8, Z ≤ ofs B (off (s.gpr .rsp) (8 * j) + BitVec.ofNat 64 i) := by
  intro i hi
  have ho := out_scr h.symm (contains_byte (stackArgAddr s 0) (i := 8 * (j - 1) + i)
    (len := 8 * count) (by omega) hn)
  rw [← stackArg_byte s (j - 1) i, ← stackWord_address s hj] at ho
  exact ho

end VG.Proof.Dsa.X86_64
