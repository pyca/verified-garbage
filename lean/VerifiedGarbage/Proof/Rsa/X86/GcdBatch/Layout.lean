module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear

/-! # Layout of RSA GCD matrix rows -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.Impl.Rsa.X86.GcdBatch
open VG.Proof.Weierstrass.X86.Inv

theorem row_layout {size n : Nat} (hn : 16 ≤ n) (hs : offset n 15 ≤ size)
    (row : Nat) (hr : row < 2) :
    LinearLay size (offset n 3+12+8*row) (offset n 3+16+8*row)
      (offset n 11) (offset n 4) (offset n 5) (offset n 13) (n+1) (n-1) := by
  have r : row = 0 ∨ row = 1 := by omega
  rcases r with rfl | rfl <;>
    constructor <;> dsimp only [offset] at * <;> omega

end VG.Proof.Rsa.X86.GcdBatch
