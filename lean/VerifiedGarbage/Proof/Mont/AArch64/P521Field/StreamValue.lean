module

public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega

/-! Integer invariants of the streamed product's sixteen-byte chunks. -/

-- separate module: memory-prefix arithmetic independent of machine execution
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.Proof.Mont

theorem wordsVal_split (m : Mem) (p : Addr) (d i j : Nat) :
    wordsVal m p d (i+j) = wordsVal m p d i+2^(64*i)*wordsVal m p (d+8*i) j := by
  induction i generalizing d with
  | zero => simp only [Nat.zero_add,wordsVal,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.add_zero]
  | succ i ih =>
    rw [Nat.succ_add,wordsVal,ih,wordsVal,pow64_succ,Nat.mul_add,Nat.mul_assoc]
    have he : d+8+8*i=d+8*(i+1) := by omega_arith
    rw [he]
    omega_arith

theorem spill_prefix {m n : Mem} {p : Addr} {i : Nat}
    (hi : 8*(i+2)≤2^64) (h : Outside p (8*i) 16 m n) :
    wordsVal n p 0 (i+2)=wordsVal m p 0 i+2^(64*i)*wordsVal n p (8*i) 2 := by
  rw [wordsVal_split,Nat.zero_add,h.wordsVal (d:=0) (k:=i)
    (Or.inl (by omega_arith)) (by omega_arith)]

theorem extend_product {S F T A B L N C R : Nat}
    (hp : S+F*T=A*B) (hc : L+R*N=T+C*B) :
    (S+F*L)+(F*R)*N=(A+F*C)*B := by
  calc
    (S+F*L)+(F*R)*N = S+F*(L+R*N) := by
      rw [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]
    _ = S+F*(T+C*B) := by rw [hc]
    _ = (S+F*T)+F*(C*B) := by rw [Nat.mul_add,Nat.add_assoc]
    _ = (A+F*C)*B := by rw [hp,Nat.add_mul,Nat.mul_assoc]

theorem last_limb_identity {S R T A top B N : Nat}
    (hp : S+R*T=A*B) (hn : N=T+top*B) : S+R*N=(A+R*top)*B := by
  rw [hn,Nat.mul_add,←Nat.add_assoc,hp,Nat.add_mul,Nat.mul_assoc]

end VG.Proof.Mont.AArch64.P521Field
