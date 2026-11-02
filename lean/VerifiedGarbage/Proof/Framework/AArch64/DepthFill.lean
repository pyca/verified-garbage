module

public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Framework.CallFill

/-! The stack depth of code with its holes filled (`Code.fillHoles`) is at most
that of the code with the holes and that of the callee filled in. -/

@[expose] public section

namespace VG

theorem Code.aarch64Depth_fillHoles_le (n : String) (b e : Prog AArch64.isa) :
    (Code.fillHoles n b e).aarch64Depth ≤ e.aarch64Depth + b.aarch64Depth := by
  induction e with
  | block is => exact Nat.zero_le _
  | seq x y ihx ihy =>
    simp only [Code.fillHoles, Code.aarch64Depth]
    omega
  | ite cd t e iht ihe =>
    simp only [Code.fillHoles, Code.aarch64Depth]
    omega
  | loop x cd ih => simpa only [Code.fillHoles, Code.aarch64Depth] using ih
  | call m body ih =>
    cases body with
    | block is =>
      cases is with
      | nil => exact Nat.le_add_left _ _
      | cons i is => exact Nat.le_add_right _ _
    | _ => exact Nat.le_add_right _ _
  | frame i x j ih =>
    simp only [Code.fillHoles, Code.aarch64Depth]
    omega
  | icall i m x y => simp only [Code.fillHoles]; exact Nat.le_add_right _ _

/-- Code that is the code with holes `e` with them filled by a callee without
frames has at most the depth of `e`. -/
theorem Code.aarch64Depth_le_of_fillHoles {a e : Prog AArch64.isa} {n : String} {b : Prog AArch64.isa}
    {d : Nat} (ha : a = Code.fillHoles n b e) (hb : b.aarch64Depth = 0) (he : e.aarch64Depth ≤ d) :
    a.aarch64Depth ≤ d := by
  have := Code.aarch64Depth_fillHoles_le n b e
  rw [ha]
  omega

end VG
