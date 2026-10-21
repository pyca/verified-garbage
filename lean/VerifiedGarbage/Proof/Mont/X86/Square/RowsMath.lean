module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.ColumnSquare
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
public import VerifiedGarbage.Proof.Mont.X86.Square.MemStep
public import VerifiedGarbage.Proof.Mont.X86.Square.RedMath
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont

 theorem coeff_congr {a b a' b' : Nat → Nat} {N k : Nat}
    (ha : ∀ i<N, a i=a' i) (hb : ∀ i<N, b i=b' i) :
    Column.coeff a b N k=Column.coeff a' b' N k := by
  unfold Column.coeff
  apply NatSum.congr
  intro i hi
  apply NatSum.congr
  intro j hj
  rw [ha i (hi), hb j (hj)]

theorem digits_frame {mem mem' : Mem} {W : Addr} {L S N x : Nat} (nw : W.toNat+L≤2^32)
    (xl : x+4*N≤L) (sep : x+4*N≤S ∨ S+12*N+56≤x) (out : Outside W S (12*N+56) mem mem') :
    ∀ i<N, w32 mem' W (x+4*i)=w32 mem W (x+4*i) := by
  intro i hi
  exact out.w32 (by omega) (by omega)

theorem qPart_memstep {s t : State} {W : Addr} {L S N k lo q : Nat}
    (nw : W.toNat+L≤2^32) (scr : S+12*N+56≤L) (hk : k<2*N) (hq : q<2^32)
    (qz : N≤k → q=0)
    (mem : t.mem=stepMem s.mem W S k lo (if k<N then q else lo)) (M : Nat → Nat) :
    Column.partSum (2^32) (Column.prefixDigits (qDigits t W S) (k+1)) M N (k+1) =
      Column.partSum (2^32) (Column.prefixDigits (qDigits s W S) k) M N k +
      (Column.coeff (Column.prefixDigits (qDigits s W S) k) M N k+q*M 0)*(2^32)^k := by
  apply Column.qPart_step
  · intro i hi ik
    unfold qDigits
    rw [mem]
    have v := stepMem_word s.mem W nw (by omega : S+52+4*k+4≤L) (by omega : S+52+4*i+4≤L) lo (if k<N then q else lo)
    simpa only [show i≠k by omega, ↓reduceIte] using v
  · intro small
    unfold qDigits
    rw [mem]
    have v := stepMem_word s.mem W nw (by omega : S+52+4*k+4≤L) (by omega : S+52+4*k+4≤L) lo (if k<N then q else lo)
    simpa only [small, ↓reduceIte, Nat.mod_eq_of_lt hq] using v
  · exact qz

theorem output_memstep {s t : State} {W : Addr} {L S N k lo q residue : Nat}
    (nw : W.toNat+L≤2^32) (scr : S+12*N+56≤L) (hk : k<2*N)
    (small : k<N → residue=0) (large : N≤k → residue=lo%2^32)
    (mem : t.mem=stepMem s.mem W S k lo (if k<N then q else lo)) :
    (2^32)^N*val32 t.mem W (S+52+4*N) (k+1-N) =
      (2^32)^N*val32 s.mem W (S+52+4*N) (k-N)+(2^32)^k*residue := by
  by_cases kn : k<N
  · rw [show k+1-N=0 by omega, show k-N=0 by omega, small kn]
    simp [val32]
  · have ge : N≤k := by omega
    have out := stepMem_output s.mem W nw (by omega : S+52+4*k+4≤L) ge lo (if k<N then q else lo)
    rw [← mem] at out
    simp only [kn, ↓reduceIte] at out
    rw [out, large ge, ← pow32, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, show N+(k-N)=k by omega]

end VG.Proof.Mont.X86.Square
