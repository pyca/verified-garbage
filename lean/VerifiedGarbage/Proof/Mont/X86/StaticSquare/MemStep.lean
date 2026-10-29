module

public import VerifiedGarbage.Proof.Mont.ColumnSquare
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum

import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Digit
/-! # Quotient digits, output digits and the stored carry -/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/StaticSquare/CarryOut.lean`, which only this module imported.
section

/-! # Saving the two-word carry for the following column -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def carryMem (mem : Mem) (W : Addr) (S c : Nat) : Mem :=
 (mem.writeW (off W (S+8)) (BitVec.ofNat 32 c)).writeW
   (off W (S+12)) (BitVec.ofNat 32 (c/2^32))

 theorem carryOut_ok {s : State} {W : Addr} {L S : Nat}
    (hw : Ws s W L) (ps : PtrAt s W .edi S) (fits : S+16≤L) :
    WP isa (.block VG.Impl.Mont.X86.Rt.StaticSquare.carryOut) s fun t =>
      Keeps [] s t ∧ t.mem=carryMem s.mem W S (value s/2^32) := by
  have low : s.gpr .ebx=BitVec.ofNat 32 (value s/2^32) := by
    apply BitVec.eq_of_toNat_eq
    rw [value_high,BitVec.toNat_ofNat]
    have := (s.gpr .ebx).isLt
    omega
  have high : s.gpr .ecx=BitVec.ofNat 32 (value s/2^32/2^32) := by
    apply BitVec.eq_of_toNat_eq
    rw [value_high,BitVec.toNat_ofNat]
    have := (s.gpr .ebx).isLt
    have := (s.gpr .ecx).isLt
    omega
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.carryOut
  refine wp_storeS (ea_ptr hw ps (by omega)) (ws_write hw (by omega)) fun u U => ?_
  have hu := hw.of_keeps (U.keeps [])
  have pu : PtrAt u W .edi S := by rw [PtrAt,U.gpr]; exact ps
  refine wp_storeS (ea_ptr hu pu (by omega)) (ws_write hu (by omega)) fun t T => WP.block_nil ?_
  refine ⟨(U.keeps []).trans (T.keeps []),?_⟩
  rw [T.mem,U.mem,U.gpr,low,high]
  rfl

 theorem carryMem_frame (mem : Mem) (W : Addr) {L S : Nat} (nw : W.toNat+L≤2^32)
    (fits : S+16≤L) (c : Nat) : Outside W (S+8) 8 mem (carryMem mem W S c) := by
  unfold carryMem
  exact ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
    ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))

 theorem carryMem_value (mem : Mem) (W : Addr) {L S : Nat} (nw : W.toNat+L≤2^32)
    (fits : S+16≤L) {c : Nat} (hc : c<2^64) :
    w32 (carryMem mem W S c) W (S+8)+2^32*w32 (carryMem mem W S c) W (S+12)=c := by
  have O := writeW32_outside (mem.writeW (off W (S+8)) (BitVec.ofNat 32 c)) W
    (d:=S+12) (BitVec.ofNat 32 (c/2^32)) (by omega : S+12+4≤2^64)
  unfold carryMem
  rw [O.w32 (by omega) (by omega),w32_write_self,w32_write_self,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
  have hdiv : c/2^32<2^32 := by omega
  rw [Nat.mod_eq_of_lt hdiv]
  exact Nat.mod_add_div c (2^32)

end VG.Proof.Mont.X86.StaticSquare
end

end

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
