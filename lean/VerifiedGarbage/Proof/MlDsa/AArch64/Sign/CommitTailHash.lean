import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailHashRun
import VerifiedGarbage.Spec.MlDsa

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3

theorem squeeze_small (A : Spec.Sha3.State) {d : Nat} (hd : d≤136) :
    squeeze 136 A d=(toBytes A).take d := by
  by_cases hz : d=0
  · subst d; simp [squeeze]
  · rw [squeeze,show (d+136-1)/136=1 by omega,squeezeBlocks,squeezeBlocks,List.append_nil,
      List.take_take,Nat.min_eq_left hd]

theorem lowRun_hash (m : Mem) (mu w1 : Addr) {wlen d : Nat}
    (hw : wlen=768 ∨ wlen=1024) (hd : d≤136) :
    (toBytes (lowRun wlen m w1 (firstState m mu w1) ((64+wlen)/136+1))).take d=
      Spec.MlDsa.H (bytesAt m mu 64++bytesAt m w1 wlen) d := by
  change _=squeeze 136 (absorb 136 (pad 136 shakeSuffix (hashMessage m mu w1 wlen))) d
  rw [squeeze_small _ hd]
  rcases hw with rfl|rfl
  · rw [show (64+768)/136+1=7 by decide,lowRun_pad65]
  · rw [show (64+1024)/136+1=9 by decide,lowRun_pad87]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
