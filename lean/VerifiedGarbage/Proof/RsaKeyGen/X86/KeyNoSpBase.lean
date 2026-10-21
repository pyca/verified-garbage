module

import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm

/-! # Native key word loops and inverse steps preserve ESP -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyNoSp
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key
open VG.Impl.Mont.X86.Dynamic

theorem checked {c : Prog isa} (H : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [H i hi]
  rfl

theorem sequence {a b : Prog isa} (A : NoSp a) (B : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact A i hi
  · exact B i hi

theorem constant (n out value : Nat) : NoSp (setConstW n out value) := by
  unfold setConstW
  apply sequence (NoSp.of_all (by rfl))
  intro i hi
  obtain ⟨j, _, hi⟩ := List.mem_flatMap.mp hi
  split at hi
  · simp only [List.not_mem_nil] at hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl

theorem constArray (n j value : Nat) : NoSp (VG.Impl.RsaKeyGen.X86.Key.constArray n j value) := constant (n + 2) (slot n j) value

theorem sub3 (n o a b : Nat) : NoSp (VG.Impl.Rsa.X86.Keys.sub3 n o a b) := NoSp.of_all (by rfl)
theorem sel (n o a b sl : Nat) : NoSp (VG.Impl.Rsa.X86.Keys.sel n o a b sl) := NoSp.of_all (by rfl)
theorem half (n j : Nat) : NoSp (VG.Impl.Rsa.X86.Keys.half n j) := NoSp.of_all (by rfl)
theorem eqS (n d a b t : Nat) : NoSp (VG.Impl.Rsa.X86.Keys.eqS n d a b t) := NoSp.of_all (by rfl)
theorem copy (n o a : Nat) : NoSp (VG.Impl.Rsa.X86.Keys.copy n o a) := NoSp.of_all (by rfl)
theorem widenCopy (n k out src : Nat) : NoSp (VG.Impl.RsaKeyGen.X86.Key.widenCopy n k out src) := NoSp.of_all (by rfl)
theorem product (l r out a b mult : Nat) : NoSp (VG.Impl.RsaKeyGen.X86.Product.code l r out a b mult) := NoSp.of_all (by rfl)
theorem divisionFrom (n src divisor q r : Nat) : NoSp (VG.Impl.RsaKeyGen.X86.Key.divisionFrom n src divisor q r) := NoSp.of_all (by rfl)

theorem invStep (n a b : Nat) : NoSp (VG.Impl.Rsa.X86.Keys.invStep n a b) := by
  apply NoSp.of_all
  simp only [VG.Impl.Rsa.X86.Keys.invStep, subModP, seqs, List.cons_append, List.nil_append, Code.allInstrs,
    checked (sub3 _ _ _ _), checked (sel _ _ _ _ _), checked (half _ _)]
  rfl

theorem inverseFrom (n src mo : Nat) : NoSp (VG.Impl.RsaKeyGen.X86.Key.inverseFrom n src mo) := by
  apply NoSp.of_all
  simp only [VG.Impl.RsaKeyGen.X86.Key.inverseFrom, inverseSetup, inverseLoad, inverseBank, inverse,
    seqs, Code.allInstrs, checked (copy _ _ _), checked (sub3 _ _ _ _), checked (invStep _ _ _)]
  rfl

end VG.Proof.RsaKeyGen.X86.KeyNoSp
