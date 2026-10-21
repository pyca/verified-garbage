module

import VerifiedGarbage.Proof.Mont.X86.Square.ColumnStep
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont

def stepMem (mem : Mem) (W : Addr) (S k lo word : Nat) : Mem :=
  (mem.writeW (off W (S+20)) (BitVec.ofNat 64 lo)).writeW (off W (S+52+4*k)) (BitVec.ofNat 32 word)

theorem stepMem_outside (mem : Mem) (W : Addr) {L S N k : Nat} (nw : W.toNat+L≤2^32)
    (scr : S+12*N+56≤L) (hk : k<2*N) (lo word : Nat) :
    Outside W S (12*N+56) mem (stepMem mem W S k lo word) := by
  unfold stepMem
  exact ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
    ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))

theorem stepMem_frame (mem : Mem) (W : Addr) {L S N k : Nat} (nw : W.toNat+L≤2^32)
    (scr : S+12*N+56≤L) (hk : k<2*N) (lo word : Nat) :
    Outs W [(S+20,8),(S+52,8*N+8)] mem (stepMem mem W S k lo word) := by
  have O1 : Outside W (S+20) 8 mem (mem.writeW (off W (S+20)) (BitVec.ofNat 64 lo)) :=
    writeW_outside _ _ _ (by omega)
  have O2 : Outside W (S+52) (8*N+8) (mem.writeW (off W (S+20)) (BitVec.ofNat 64 lo))
      (stepMem mem W S k lo word) := by
    unfold stepMem
    exact (writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)
  exact (Outs.of_outside O1 (by simp)).trans (Outs.of_outside O2 (by simp))

theorem stepMem_word (mem : Mem) (W : Addr) {L S k i : Nat} (nw : W.toNat+L≤2^32)
    (ki : S+52+4*k+4≤L) (ii : S+52+4*i+4≤L) (lo word : Nat) :
    w32 (stepMem mem W S k lo word) W (S+52+4*i) =
      if i=k then word%2^32 else w32 mem W (S+52+4*i) := by
  by_cases e : i=k
  · subst i
    simp only [stepMem, w32_write_self, BitVec.toNat_ofNat, ↓reduceIte]
  · rw [ite_eq_right e]
    have O1 := writeW_outside mem W (d := S+20) (BitVec.ofNat 64 lo) (by omega)
    have O2 := writeW32_outside (mem.writeW (off W (S+20)) (BitVec.ofNat 64 lo)) W
      (d := S+52+4*k) (BitVec.ofNat 32 word) (by omega)
    exact (O2.w32 (by omega) (by omega)).trans (O1.w32 (by omega) (by omega))

theorem stepMem_output (mem : Mem) (W : Addr) {L S N k : Nat} (nw : W.toNat+L≤2^32)
    (ki : S+52+4*k+4≤L) (large : N≤k) (lo word : Nat) :
    val32 (stepMem mem W S k lo word) W (S+52+4*N) (k+1-N) =
      val32 mem W (S+52+4*N) (k-N)+2^(32*(k-N))*(word%2^32) := by
  have O1 := writeW_outside mem W (d := S+20) (BitVec.ofNat 64 lo) (by omega)
  have O2 := writeW32_outside (mem.writeW (off W (S+20)) (BitVec.ofNat 64 lo)) W
    (d := S+52+4*k) (BitVec.ofNat 32 word) (by omega)
  rw [show k+1-N=(k-N)+1 by omega, val32_succ]
  have vals : val32 (stepMem mem W S k lo word) W (S+52+4*N) (k-N) =
      val32 mem W (S+52+4*N) (k-N) := by
    unfold stepMem
    exact (O2.val32 (by omega) (by omega)).trans (O1.val32 (by omega) (by omega))
  rw [vals]
  rw [show S+52+4*N+4*(k-N)=S+52+4*k by omega]
  have wordeq := stepMem_word mem W nw ki ki lo word
  rw [ite_eq_left rfl] at wordeq
  rw [wordeq]

end VG.Proof.Mont.X86.Square
