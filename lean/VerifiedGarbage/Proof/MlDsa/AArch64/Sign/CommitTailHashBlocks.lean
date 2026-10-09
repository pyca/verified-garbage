import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailHashFirst

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3
open VG.Proof.MlKem (bytesAt_take bytesAt_drop bytesAt_slice)

def hashMessage (m : Mem) (mu w1 : Addr) (wlen : Nat) : List Byte :=
  bytesAt m mu 64++bytesAt m w1 wlen

theorem hashMessage_length (m : Mem) (mu w1 : Addr) (wlen : Nat) :
    (hashMessage m mu w1 wlen).length=64+wlen := by simp [hashMessage,bytesAt]

theorem hashMessage_first (m : Mem) (mu w1 : Addr) {wlen : Nat} (hw : 72≤wlen) :
    block 136 (hashMessage m mu w1 wlen) 0=bytesAt m mu 64++bytesAt m w1 72 := by
  simp only [block,hashMessage,Nat.mul_zero,List.drop_zero,List.take_append]
  rw [List.take_of_length_le (by simp [bytesAt]),show (bytesAt m mu 64).length=64 by simp [bytesAt]]
  exact congrArg (bytesAt m mu 64++·) (bytesAt_take m w1 hw)

theorem hashMessage_block (m : Mem) (mu w1 : Addr) {wlen i : Nat}
    (hi : 136*(i+1)+136≤64+wlen) :
    block 136 (hashMessage m mu w1 wlen) (i+1)=
      bytesAt m (w1+BitVec.ofNat 64 (72+136*i)) 136 := by
  simp only [block,hashMessage,List.drop_append]
  rw [List.drop_eq_nil_of_le (by simp [bytesAt];omega),List.nil_append,
    show (bytesAt m mu 64).length=64 by simp [bytesAt],
    bytesAt_slice m w1 (by omega : 136*(i+1)-64+136≤wlen),
    show 136*(i+1)-64=72+136*i by omega]

theorem hashMessage_tail (m : Mem) (mu w1 : Addr) {wlen n : Nat} (hn : 0<n)
    (hle : 136*n≤64+wlen) :
    (hashMessage m mu w1 wlen).drop (136*n)=
      bytesAt m (w1+BitVec.ofNat 64 (136*n-64)) (64+wlen-136*n) := by
  simp only [hashMessage,List.drop_append]
  rw [List.drop_eq_nil_of_le (by simp [bytesAt];omega),List.nil_append,
    show (bytesAt m mu 64).length=64 by simp [bytesAt],
    bytesAt_drop m w1 (by omega : 136*n-64≤wlen)]
  congr 1
  omega

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
