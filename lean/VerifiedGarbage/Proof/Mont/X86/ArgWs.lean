module

public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.MontMulContract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Omega

/-! # A working space given as an argument

`ofs_far`: a byte outside the working space lies past it, in offsets from
its base.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.Proof.Mont

/-- A byte apart from the working space lies past it, in offsets from its base. -/
theorem ofs_far {base : Addr} {size : Nat} {x : Addr}
    (h : ¬ (⟨base, size⟩ : Region).Contains x 1) : size ≤ ofs base x := by
  simp only [Region.Contains, ofs] at h ⊢
  omega

end VG.Proof.Mont.X86.Dynamic
