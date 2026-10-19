module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SeedSpec
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant

/-! # Relate bounded continuation blocks to the 840-byte SHAKE stream -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.Spec.MlKem VG.Proof.MlKem VG.Proof.Sha3

def shakeStream (A : Spec.Sha3.State) (i : Nat) : Byte := byteOf (iterF (i/168+1) A) (i%168)
def accepted (A : Spec.Sha3.State) (blocks : Nat) : List Zq := sampleAfter [] (shakeStream A) (56*blocks)

theorem shakeStream_block (A : Spec.Sha3.State) (b : Nat) {i : Nat} (hi : i<168) :
    shakeStream A (168*b+i)=byteOf (iterF (b+1) A) i := by
  unfold shakeStream
  have hd : (168*b+i)/168=b := by omega
  have hm : (168*b+i)%168=i := by omega
  rw [hd,hm]

theorem accepted_next (A : Spec.Sha3.State) (b : Nat) :
    sampleAfter (accepted A b) (byteOf (iterF (b+1) A)) 56=accepted A (b+1) := by
  rw [sampleAfter_congr _ (out' := fun i=>shakeStream A (3*(56*b)+i)) (fun i hi=>by
    rw [show 3*(56*b)=168*b by omega]
    exact (shakeStream_block A b (by omega)).symm),accepted,Rej8.sampleAfter_add]
  congr 1 <;> omega

theorem accepted_length (A : Spec.Sha3.State) (b : Nat) : (accepted A b).length≤256 :=
  sampleAfter_length_le (by simp) _ _

theorem accepted_full {A : Spec.Sha3.State} {b k : Nat} (h : (accepted A b).length=256) (hk : b≤k) :
    accepted A k=accepted A b := sampleAfter_full h (56*k) (by omega)

theorem shakeStream_seed (m : Mem) (p : Addr) {k : Nat} (hk : 0<k) (hk256 : k≤256) (a i : Nat) :
    shakeStream (seedState m p a k) i=xofByte (seedBytes m p a k) i :=
  stream_seedState m p hk hk256 i

end VG.Proof.MlKem.AArch64.Paired
