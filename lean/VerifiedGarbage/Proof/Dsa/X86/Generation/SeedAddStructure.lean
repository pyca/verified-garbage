module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline

/-! # Wrapped addition changes only the carry and byte registers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem seedAdd_noClobber (n : Nat) (r : Reg) (ha : r ≠ .eax) (hc : r ≠ .ecx) :
    ∀ i ∈ instrs (seedAdd n), Taint.clobbers i r = false := by
  have all : (seedAdd n).allInstrs (fun i => !Taint.clobbers i r) = true := by
    induction n with
    | zero => rfl
    | succ n ih => cases r <;> simp_all [seedAdd, seedAddByte, Code.allInstrs, Taint.clobbers, Taint.dst]
  rw [Code.allInstrs_eq, List.all_eq_true] at all
  intro i hi
  simpa using all i hi

theorem seedAdd_keeps {n : Nat} {s t : State} {trace : List Leak} (E : Exec isa (seedAdd n) s trace t) :
    Keeps [.eax, .ecx] s t := by
  refine ⟨?_, Exec.rdwr E⟩
  intro r hr
  exact Exec.gpr (seedAdd_noClobber n r (by simp_all) (by simp_all)) E
end VG.Proof.Dsa.X86.Generation
