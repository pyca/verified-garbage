module

import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Layout
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Half
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear

/-! # A full-width RSA GCD matrix row -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass

-- The two row outputs and the product temporaries fit the existing inverse bank.
def writes (n : Nat) : List (Nat × Nat) :=
 [(offset n 4,4*(4*n+8)),(offset n 11,3*(4*n+8))]

theorem row_ok {s : State} {base : Addr} {size n p r : Nat} {u v f g : Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size) (hr : r < 2)
    (hu : s.mem.readW (VG.Proof.Mont.off base (offset n 3+12+8*r)) 32 = BitVec.ofInt 32 u)
    (hv : s.mem.readW (VG.Proof.Mont.off base (offset n 3+16+8*r)) 32 = BitVec.ofInt 32 v)
    (huv : |u|+|v| ≤ 2^30)
    (hf : (val32 s.mem base (offset n 4) (n+1) : Int) % 2^(32*(n+1)) = f % 2^(32*(n+1)))
    (hg : (val32 s.mem base (offset n 5) (n+1) : Int) % 2^(32*(n+1)) = g % 2^(32*(n+1)))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2^(32*n+1))
    (hdiv : 2^30 ∣ u*f+v*g) :
    WP isa (.block (row n r)) s fun z =>
      (val32 z.mem base (offset n (6+r)) (n+1) : Int) % 2^(32*(n+1)) =
        ((u*f+v*g)/2^30) % 2^(32*(n+1)) ∧
      Keeps clob s z ∧
      Unch base [(offset n 11,4*(n+3)),(offset n 13,4*n),(offset n (6+r),4*(n+1))] s.mem z.mem := by
  have e : n-1+2=n+1 := by omega
  have e1 : n-1+1=n := by omega
  have L := row_layout hn hz r hr
  have dst : offset n (6+r)+4*(n+1) ≤ size := by
    dsimp only [offset] at *
    rcases (show r=0 ∨ r=1 by omega) with rfl | rfl <;> omega
  have sep : offset n (6+r)+4*(n+1) ≤ offset n 11 ∨ offset n 11+4*(n+1) ≤ offset n (6+r) := by
    dsimp only [offset]; rcases (show r=0 ∨ r=1 by omega) with rfl | rfl <;> omega
  have H := half_wide_ok (k:=n-1) (p:=p) hs
    (by simpa only [e] using L) (by simpa only [e] using dst)
    (by simpa only [e] using sep) hu hv huv
    (by simpa only [e] using hf) (by simpa only [e] using hg) hfb hgb
    (by simpa only [e1] using hp) hdiv
  simpa only [VG.Impl.Rsa.X86.GcdBatch.row,e,e1,show n+1+2=n+3 by omega] using H

end VG.Proof.Rsa.X86.GcdBatch
