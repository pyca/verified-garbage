module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
public import VerifiedGarbage.Proof.Weierstrass.X86.InvRed
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear

/-! # Full workspace strides with half-width inversion rows -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Weierstrass.X86.Inv VG.Impl.Mont

def model (w n iv : Nat) : Mod := {n:=n/2,mo:=offset w 2,tmp:=offset w 12,minv:=iv}

 theorem fg_layout {size w n : Nat} (hn : 16≤n) (hw : w=2*n) (hs : offset w 15≤size)
    (row : Nat) (hr : row<2) :
    LinearLay size (offset w 3+12+8*row) (offset w 3+16+8*row)
      (offset w 11) (offset w 4) (offset w 5) (offset w 12) (n+1) (n-1) := by
  rcases (show row=0 ∨ row=1 by omega_arith) with rfl | rfl <;>
    constructor <;> dsimp only [offset] at * <;> omega_arith

 theorem ab_layout {size w n : Nat} (hn : 16≤n) (hw : w=2*n) (hs : offset w 15≤size)
    (row : Nat) (hr : row<2) :
    LinearLay size (offset w 3+12+8*row) (offset w 3+16+8*row)
      (offset w 11) (offset w 6) (offset w 7) (offset w 12) n (n-1) := by
  rcases (show row=0 ∨ row=1 by omega_arith) with rfl | rfl <;>
    constructor <;> dsimp only [offset] at * <;> omega_arith

 theorem red_layout {size w n iv : Nat} (hn : 16≤n) (hw : w=2*n) (he : n%2=0)
    (hs : offset w 15≤size) (row : Nat) (hr : row<2) :
    RedLay (model w n iv) size (offset w 11) (offset w 12) (offset w (13+row)) n := by
  rcases (show row=0 ∨ row=1 by omega_arith) with rfl | rfl
  all_goals
    constructor
    · dsimp only [VG.Impl.Mont.X86.words,model]; omega_arith
    all_goals dsimp only [model,offset] at *; omega_arith

 theorem reduce_eq (w n out iv : Nat) : VG.Impl.Rsa.X86.InvBatch.reduce w n out=
    VG.Impl.Rsa.X86.InvBatch.reduceLoaded (model w n iv) (offset w 11) (offset w 12) out (offset w 3+28) := rfl

end VG.Proof.Rsa.X86.InvBatch
