module

public import VerifiedGarbage.Spec.Rsa.Mont

public import Init.Data.BitVec.BasicAux

public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout

/-! # The symmetric product fits exactly in the two prepared scratch arrays -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Spec.Rsa.Mont

theorem layout_bounds {w L a : Nat} (fit : arrAt w 8 ≤ L) (left : Operand a) :
    Lay L (2 * w) (arrAt w 2) 256 56 (arrAt w a) (arrAt w a) := by
  have scratch := Compact.array_fit fit (j := 4) (by decide)
  have modulus := Compact.array_fit fit (j := 0) (by decide)
  have input := Compact.array_fit fit left.1
  have apart := Compact.operand_apart (w := w) left
  have product : arrAt w 2 + 8 * (2 * w) + 32 = arrAt w 4 := by unfold arrAt hdrBytes; omega
  have header : 128 ≤ arrAt w 2 := by unfold arrAt hdrBytes; omega
  have m : arrAt w 0 = 256 := by simp [arrAt, hdrBytes]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · left
    unfold arrAt hdrBytes
    omega
  · left; omega
  · omega
  · omega

def cacheValues (A : Nat → BitVec 32) (width : BitVec 32) (S o a : Nat) : Nat → BitVec 32
  | 0 => A 0
  | 1 => A 1
  | 2 => width
  | 3 => BitVec.ofNat 32 256
  | 4 => BitVec.ofNat 32 56
  | 5 => BitVec.ofNat 32 S
  | 6 => BitVec.ofNat 32 o
  | 7 => BitVec.ofNat 32 a
  | 8 => BitVec.ofNat 32 a
  | _ => 0

theorem cacheValues_ok {A : Nat → BitVec 32} {width : BitVec 32} {W : Addr} {N S o a : Nat}
    (base : (A 0).toNat = W.toNat) (n : width.toNat * 8 = 4 * N)
    (s : S < 2 ^ 32) (out : o < 2 ^ 32) (input : a < 2 ^ 32) :
    ArgVals (cacheValues A width S o a) W N S 256 56 o a a := by
  refine ⟨base, n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (256 : BitVec 32).toNat = 256
    decide
  · change (56 : BitVec 32).toNat = 56
    decide
  · exact Nat.mod_eq_of_lt s
  · exact Nat.mod_eq_of_lt out
  · exact Nat.mod_eq_of_lt input
  · exact Nat.mod_eq_of_lt input

end VG.Proof.Mont.X86.PreparedSquare
