import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailHashBlocks

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords_eq)

theorem lowRun_full (m : Mem) (mu w1 : Addr) {wlen : Nat} (hw : 72≤wlen)
    {i : Nat} (hi : i<(64+wlen)/136) :
    keccakF (lowRun wlen m w1 (firstState m mu w1) i)=
      absorbN 136 (hashMessage m mu w1 wlen) (i+1) := by
  induction i with
  | zero =>
    rw [lowRun,absorbN_succ,hashMessage_first m mu w1 hw,firstState_eq]
    rfl
  | succ i ih =>
    rw [lowRun,absorbAfter,ite_eq_left (by omega : i<(64+wlen)/136-1),xorWords_eq,
      ih (by omega),absorbN_succ 136 (hashMessage m mu w1 wlen) (i+1),
      hashMessage_block m mu w1 (wlen:=wlen) (i:=i) (by omega)]

theorem lowRun_pad65 (m : Mem) (mu w1 : Addr) :
    lowRun 768 m w1 (firstState m mu w1) 7=
      absorb 136 (pad 136 shakeSuffix (hashMessage m mu w1 768)) := by
  have hf := lowRun_full m mu w1 (wlen:=768) (by decide) (i:=5) (by decide)
  have hr : Rep 136 (hashMessage m mu w1 768)=
      VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords (absorbN 136 (hashMessage m mu w1 768) 6)
        m (w1+752) 2 := by
    rw [Rep,absorb_eq,hashMessage_length,hashMessage_tail m mu w1 (n:=6) (by decide) (by decide),xorWords_eq]
    rfl
  rw [absorb_pad (by decide : 1<136) (by decide : 136≤200),hashMessage_length,hr]
  rw [lowRun,absorbAfter,ite_eq_right (by decide : ¬(6:Nat)<(64+768)/136-1),
    ite_eq_right (by decide : ¬(6:Nat)=(64+768)/136-1)]
  rw [lowRun,absorbAfter,ite_eq_right (by decide : ¬(5:Nat)<(64+768)/136-1),
    ite_eq_left (by decide : (5:Nat)=(64+768)/136-1),ite_eq_left rfl,hf,paddedState_bytes]
  rfl

theorem lowRun_pad87 (m : Mem) (mu w1 : Addr) :
    lowRun 1024 m w1 (firstState m mu w1) 9=
      absorb 136 (pad 136 shakeSuffix (hashMessage m mu w1 1024)) := by
  have hf := lowRun_full m mu w1 (wlen:=1024) (by decide) (i:=7) (by decide)
  have hr : Rep 136 (hashMessage m mu w1 1024)=absorbN 136 (hashMessage m mu w1 1024) 8 := by
    rw [Rep,absorb_eq,hashMessage_length,hashMessage_tail m mu w1 (n:=8) (by decide) (by decide)]
    exact xorBytes_nil _
  rw [absorb_pad (by decide : 1<136) (by decide : 136≤200),hashMessage_length,hr]
  rw [lowRun,absorbAfter,ite_eq_right (by decide : ¬(8:Nat)<(64+1024)/136-1),
    ite_eq_right (by decide : ¬(8:Nat)=(64+1024)/136-1)]
  rw [lowRun,absorbAfter,ite_eq_right (by decide : ¬(7:Nat)<(64+1024)/136-1),
    ite_eq_left (by decide : (7:Nat)=(64+1024)/136-1),ite_eq_right (by decide : (1024:Nat)≠768),hf,paddedState_bytes]
  rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
