module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.CarryOut
public import VerifiedGarbage.Proof.Mont.ColumnSquare
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Quotient digits, output digits and the stored carry -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont

def stepMem (mem : Mem) (W : Addr) (S k word c : Nat) : Mem :=
 carryMem (mem.writeW (off W (S+52+4*k)) (BitVec.ofNat 32 word)) W S c

 theorem stepMem_outside (mem : Mem) (W : Addr) {L S N k : Nat} (nw : W.toNat+L≤2^32)
    (scr : S+12*N+56≤L) (hk : k<2*N) (word c : Nat) :
    Outside W S (12*N+56) mem (stepMem mem W S k word c) := by
  unfold stepMem
  exact ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
    ((carryMem_frame _ _ nw (by omega) c).mono (by omega) (by omega))

 theorem stepMem_frame (mem : Mem) (W : Addr) {L S N k : Nat} (nw : W.toNat+L≤2^32)
    (scr : S+12*N+56≤L) (hk : k<2*N) (word c : Nat) :
    Outs W [(S+8,8),(S+52,8*N+8)] mem (stepMem mem W S k word c) := by
  have O1 : Outside W (S+52) (8*N+8) mem
      (mem.writeW (off W (S+52+4*k)) (BitVec.ofNat 32 word)) :=
    (writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)
  have O2 := carryMem_frame (mem.writeW (off W (S+52+4*k)) (BitVec.ofNat 32 word)) W (S:=S) nw (by omega) c
  exact (Outs.of_outside O1 (by simp)).trans (Outs.of_outside O2 (by simp))

 theorem stepMem_word (mem : Mem) (W : Addr) {L S k i : Nat} (nw : W.toNat+L≤2^32)
    (ki : S+52+4*k+4≤L) (ii : S+52+4*i+4≤L) (word c : Nat) :
    w32 (stepMem mem W S k word c) W (S+52+4*i)=
      if i=k then word%2^32 else w32 mem W (S+52+4*i) := by
  have OC := carryMem_frame (mem.writeW (off W (S+52+4*k)) (BitVec.ofNat 32 word)) W (S:=S) nw (by omega) c
  unfold stepMem
  rw [OC.w32 (by omega) (by omega)]
  by_cases e : i=k
  · subst i
    rw [ite_eq_left rfl,w32_write_self,BitVec.toNat_ofNat]
  · rw [ite_eq_right e]
    exact (writeW32_outside mem W (d:=S+52+4*k) (BitVec.ofNat 32 word) (by omega)).w32 (by omega) (by omega)

 theorem stepMem_output (mem : Mem) (W : Addr) {L S N k : Nat} (nw : W.toNat+L≤2^32)
    (ki : S+52+4*k+4≤L) (large : N≤k) (word c : Nat) :
    val32 (stepMem mem W S k word c) W (S+52+4*N) (k+1-N)=
      val32 mem W (S+52+4*N) (k-N)+2^(32*(k-N))*(word%2^32) := by
  have OC := carryMem_frame (mem.writeW (off W (S+52+4*k)) (BitVec.ofNat 32 word)) W (S:=S) nw (by omega) c
  have OD := writeW32_outside mem W (d:=S+52+4*k) (BitVec.ofNat 32 word) (by omega : S+52+4*k+4≤2^64)
  rw [show k+1-N=(k-N)+1 by omega,val32_succ]
  have vals : val32 (stepMem mem W S k word c) W (S+52+4*N) (k-N)=
      val32 mem W (S+52+4*N) (k-N) :=
    (OC.val32 (by omega) (by omega)).trans (OD.val32 (by omega) (by omega))
  rw [vals,show S+52+4*N+4*(k-N)=S+52+4*k by omega]
  rw [stepMem_word mem W (S:=S) nw ki ki word c,ite_eq_left rfl]

 theorem qPart_memstep {s t : State} {W : Addr} {L S N k q c word : Nat}
    (nw : W.toNat+L≤2^32) (scr : S+12*N+56≤L) (hk : k<2*N) (hq : q<2^32)
    (qz : N≤k → q=0) (digit : k<N → word=q)
    (mem : t.mem=stepMem s.mem W S k word c) (M : Nat → Nat) :
    Column.partSum (2^32) (Column.prefixDigits (fun i => w32 t.mem W (S+52+4*i)) (k+1)) M N (k+1)=
      Column.partSum (2^32) (Column.prefixDigits (fun i => w32 s.mem W (S+52+4*i)) k) M N k+
      (Column.coeff (Column.prefixDigits (fun i => w32 s.mem W (S+52+4*i)) k) M N k+q*M 0)*(2^32)^k := by
  apply Column.qPart_step
  · intro i hi ik
    rw [mem]
    rw [stepMem_word s.mem W (S:=S) nw (by omega) (by omega) word c,ite_eq_right (by omega)]
  · intro small
    rw [mem,stepMem_word s.mem W (S:=S) nw (by omega) (by omega) word c,ite_eq_left rfl,digit small,Nat.mod_eq_of_lt hq]
  · exact qz

end VG.Proof.Mont.X86.StaticSquare
