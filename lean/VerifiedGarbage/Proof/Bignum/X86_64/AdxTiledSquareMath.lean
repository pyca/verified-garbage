import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Chunks

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTri8 (chunks blockCross)

theorem chunks_tail_value (m : Mem) (B : Addr) (e k n : Nat) :
    Square.value (2^512) (fun j => chunks m B e (k+j)) n=wv m B (e+64*k) (8*n) := by
  have f : (fun j => chunks m B e (k+j))=chunks m B (e+64*k) := by
    funext j
    unfold chunks
    rw [show e+64*(k+j)=e+64*k+64*j by omega]
  rw [f,AdxTri8.chunks_value]

def remaining (m : Mem) (B : Addr) (e n k : Nat) :=
  2^(1024*k)*Square.cross (2^512) (fun j => chunks m B e (k+j)) (n-k)

private theorem distribute {P R X V C : Nat} :
    P*(R*X*V+R*R*C)=(P*R)*X*V+(P*(R*R))*C := by grind

theorem remaining_step (m : Mem) (B : Addr) (e n k : Nat) (hk : k+1<n) :
    remaining m B e n k=2^(512*(2*k+1))*chunks m B e k*wv m B (e+64*(k+1)) (8*(n-k-1))+
      remaining m B e n (k+1) := by
  have shift : (fun j => chunks m B e (k+(j+1)))=(fun j => chunks m B e ((k+1)+j)) := by
    funext j
    rw [show k+(j+1)=(k+1)+j by omega]
  have p1 : (2 : Nat)^(512*(2*k+1))=2^(1024*k)*2^512 := by
    rw [← Nat.pow_add]
    apply congrArg (fun n : Nat => (2 : Nat)^n)
    omega
  have p2 : (2 : Nat)^(1024*(k+1))=2^(1024*k)*(2^512*2^512) := by
    rw [← Nat.pow_add 2 512 512,← Nat.pow_add]
    apply congrArg (fun n : Nat => (2 : Nat)^n)
    omega
  unfold remaining
  rw [show n-k=(n-k-1)+1 by omega,Triangular.cross_head,shift,chunks_tail_value]
  simp only [Nat.add_zero]
  rw [show n-(k+1)=n-k-1 by omega,p1,p2]
  exact distribute

theorem remaining_end (m : Mem) (B : Addr) (e n : Nat) (hn : 0<n) : remaining m B e n (n-1)=0 := by
  unfold remaining
  rw [show n-(n-1)=1 by omega]
  simp only [Square.cross,Square.value,Nat.zero_mul,Nat.add_zero,Nat.mul_zero]

end VG.Proof.Bignum.X86_64.AdxTiledSquare
