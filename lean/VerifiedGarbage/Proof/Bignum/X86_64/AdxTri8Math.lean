import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Sum
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCross

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum

theorem rowSum_words (m : Mem) (B : Addr) (e i n : Nat) :
    rowSum m B e i n=Triangular.rows (2^64) (fun j => (word m B (e+8*(i+j))).toNat) n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have shift : (fun j => (word m B (e+8*(i+(j+1)))).toNat)=
        (fun j => (word m B (e+8*(i+1)+8*j)).toNat) := by
      funext j
      rw [show e+8*(i+(j+1))=e+8*(i+1)+8*j by omega]
    have shift' : (fun j => (word m B (e+8*(i+1)+8*j)).toNat)=
        (fun j => (word m B (e+8*((i+1)+j))).toNat) := by
      funext j
      rw [show e+8*(i+1)+8*j=e+8*((i+1)+j) by omega]
    rw [rowSum,Triangular.rows]
    simp only [Nat.add_zero]
    rw [shift,AdxSquare.value_words,shift',← ih,← Nat.pow_add]

theorem rowSum_cross (m : Mem) (B : Addr) (e n : Nat) :
    2^64*rowSum m B e 0 n=AdxSquare.crossValue m B e (n+1) := by
  rw [rowSum_words,Triangular.rows_cross]
  simp only [Nat.zero_add,AdxSquare.crossValue]

end VG.Proof.Bignum.X86_64.AdxTri8
