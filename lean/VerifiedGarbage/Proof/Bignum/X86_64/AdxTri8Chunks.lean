import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Blocks

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem crossValue_add (m : Mem) (B : Addr) (e p q : Nat) :
    AdxSquare.crossValue m B e (p+q)=AdxSquare.crossValue m B e p+
      2^(128*p)*AdxSquare.crossValue m B (e+8*p) q+
      2^(64*p)*wv m B e p*wv m B (e+8*p) q := by
  have shift : (fun i => (word m B (e+8*(p+i))).toNat)=
      (fun i => (word m B (e+8*p+8*i)).toNat) := by
    funext i
    rw [show e+8*(p+i)=e+8*p+8*i by omega]
  unfold AdxSquare.crossValue
  rw [Triangular.cross_add,shift,AdxSquare.value_words,AdxSquare.value_words,
    ← Nat.pow_mul,← Nat.pow_mul,show 64*(2*p)=128*p by omega]

def chunks (m : Mem) (B : Addr) (e : Nat) (j : Nat) := wv m B (e+64*j) 8

theorem chunks_value (m : Mem) (B : Addr) (e n : Nat) :
    Square.value (2^512) (chunks m B e) n=wv m B e (8*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Square.value,ih,show 8*(n+1)=8*n+8 by omega,wv_add,← Nat.pow_mul]
    simp only [chunks,show 8*(8*n)=64*n by omega,show 64*(8*n)=512*n by omega]
    rw [Nat.mul_comm (wv m B (e+64*n) 8)]

private theorem sum_chunks {A C P D Q X Y : Nat} :
    (A+C)+P*D+Q*X*Y=(A+P*D)+(C+X*Y*Q) := by grind

theorem chunks_cross (m : Mem) (B : Addr) (e n : Nat) :
    AdxSquare.crossValue m B e (8*n)=blockCross m B e n+Square.cross (2^512) (chunks m B e) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 8*(n+1)=8*n+8 by omega,crossValue_add,ih,blockCross,Square.cross,chunks_value,← Nat.pow_mul]
    simp only [chunks,show 8*(8*n)=64*n by omega,show 128*(8*n)=1024*n by omega,
      show 64*(8*n)=512*n by omega]
    exact sum_chunks

end VG.Proof.Bignum.X86_64.AdxTri8
