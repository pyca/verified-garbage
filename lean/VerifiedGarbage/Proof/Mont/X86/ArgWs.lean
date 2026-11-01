module

public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.MontMulContract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Omega

/-! # A working space given as an argument

`wsOf`: the working space's address, the first argument; `ofs_far`: a byte
outside it lies past it, in offsets from its base; `numAt_eq8`, `numAt_eq4`:
the specification's numbers as the proofs' words.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.Proof.Mont

/-- The working space, from the first argument. -/
abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64

theorem numAt_eq8 (m : Mem) (base : Addr) (d n : Nat) :
    Proof.Rsa.MontMul.numAt m base d (8 * n) = wordsVal m base d n := read_eq_wordsVal m base n d

theorem numAt_eq4 (m : Mem) (base : Addr) (d : Nat) : Proof.Rsa.MontMul.numAt m base d 4 = w32 m base d := by
  simp only [Proof.Rsa.MontMul.numAt, w32, off]; rfl

/-- A byte apart from the working space lies past it, in offsets from its base. -/
theorem ofs_far {base : Addr} {size : Nat} {x : Addr}
    (h : ¬ (⟨base, size⟩ : Region).Contains x 1) : size ≤ ofs base x := by
  simp only [Region.Contains, ofs] at h ⊢
  omega

end VG.Proof.Mont.X86.Dynamic
