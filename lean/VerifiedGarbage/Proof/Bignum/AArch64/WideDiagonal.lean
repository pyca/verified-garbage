module

public import VerifiedGarbage.Impl.Bignum.AArch64.WideLoops
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChain

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WideLoops
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.Square
open VG.Proof.MlKem.AArch64 (Keep)

/-- All doubled cross products and diagonal squares, including the high word. -/
theorem diagonal_ok {s : State} {B : Addr} {Z A eb k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B A) (h9 : s.gpr .x9 = off B eb)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (4*k)) (h7 : s.gpr .x7 = 0)
    (hk0 : 0 < k) (hk : k < 2 ^ 58)
    (hA : A+16*(4*k)+8 ≤ Z) (hb : eb+8*(4*k) ≤ Z)
    (sb : eb+8*(4*k) ≤ A ∨ A+16*(4*k)+8 ≤ eb) :
    WP isa VG.Impl.Bignum.AArch64.WideLoops.diagonal s fun t =>
      wv t.mem B A (2*(4*k)+1) = 2*wv s.mem B A (2*(4*k)) + diagonalValue s.mem B eb (4*k) ∧
      Outside B A (16*(4*k)+8) s.mem t.mem ∧ t.gpr .x16 = off B (A+16*(4*k)) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x14, .x16] s t := by
  exact DiagonalChain.diagonal_ok hs h8 h9 h12 h7 hk0 hk hA hb sb

end VG.Proof.Bignum.AArch64.WideLoops
