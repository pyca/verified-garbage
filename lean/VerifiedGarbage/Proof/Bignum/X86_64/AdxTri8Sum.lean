import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Rotate
import VerifiedGarbage.Proof.Bignum.Triangular

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def rowSum (m : Mem) (B : Addr) (e : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | i, n+1 => (word m B (e+8*i)).toNat*wv m B (e+8*(i+1)) (n+1)+2^128*rowSum m B e (i+1) n

theorem rowSum_congr {m m' : Mem} {B : Addr} {e i n : Nat}
    (h : ∀ j≤n, word m' B (e+8*(i+j))=word m B (e+8*(i+j))) : rowSum m' B e i n=rowSum m B e i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have w : wv m' B (e+8*(i+1)) (n+1)=wv m B (e+8*(i+1)) (n+1) := by
      apply wv_congr
      intro k hk
      rw [show e+8*(i+1)+8*k=e+8*(i+(k+1)) by omega]
      exact h (k+1) (by omega)
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [rowSum,rowSum,h0,w,ih (by
      intro j hj
      rw [show (i+1)+j=i+(j+1) by omega]
      exact h (j+1) (by omega))]

end VG.Proof.Bignum.X86_64.AdxTri8
