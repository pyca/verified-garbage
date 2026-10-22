module

public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The DSA widths fit the existing runtime arithmetic representation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Rsa.X86.KeyRt

theorem factor_width (n : Nat) : kw (8 * n) = 2 * n := by
  simp only [kw, Spec.Rsa.modulusWords]
  omega

theorem factor_geometry {n : Nat} (lower : 4 ≤ n) (upper : n ≤ 48) :
    8 * n ≤ 1024 ∧ 0 < kw (8 * n) ∧ kw (8 * n) ≤ 1024 ∧
      32 * kw (8 * n) ≤ 16384 ∧
      VG.Proof.Rsa.X86.Keys.arr (kw (8 * n)) 3 ≤ Impl.Dsa.Generation.Layout.arithmeticBytes := by
  rw [factor_width]
  simp only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S,
    Impl.Rsa.X86.Keys.hdr, Impl.Dsa.Generation.Layout.arithmeticBytes]
  omega

end VG.Proof.Dsa.X86.Generation
