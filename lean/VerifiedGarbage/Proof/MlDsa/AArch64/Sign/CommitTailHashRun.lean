import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailModel
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailFirst
import VerifiedGarbage.Proof.MlKem.Mem

/-! ## From `CommitTailHashPadding.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3
open VG.Proof.Sha3

theorem xorWord_byte (A : Spec.Sha3.State) (j k : Nat) (b : Byte) (w : BitVec 64)
    (hk : k<8) (hw : ∀r<8,w.extractLsb' (8*r) 8=if r=k then b else 0) :
    xorWord A j w=xorByte A (8*j+k) b := by
  apply ext_bytes
  intro i hi
  rw [byteOf_xorByte _ _ _ hi]
  simp only [byteOf,xorWord_get _ _ _ _ (by omega : i/8<25)]
  by_cases he : i/8=j
  · rw [ite_eq_left he,BitVec.extractLsb'_xor,hw _ (by omega)]
    by_cases hr : i%8=k
    · rw [ite_eq_left hr,ite_eq_left (by omega : i=8*j+k)]
    · rw [ite_eq_right hr,ite_eq_right (by omega : i≠8*j+k)]
      exact BitVec.xor_zero
  · rw [ite_eq_right he,ite_eq_right (by omega : i≠8*j+k)]

theorem xorWord_suffix (A : Spec.Sha3.State) (j : Nat) :
    xorWord A j 0x1f=xorByte A (8*j) 0x1f := by
  simpa only [Nat.add_zero] using xorWord_byte A j 0 0x1f 0x1f (by decide) (by
    intro r hr
    rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 by omega) with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)

theorem xorWord_terminal (A : Spec.Sha3.State) :
    xorWord A 16 0x8000000000000000=xorByte A 135 0x80 := by
  exact xorWord_byte A 16 7 0x80 0x8000000000000000 (by decide) (by
    intro r hr
    rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 by omega) with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel)

theorem paddedState_bytes (A : Spec.Sha3.State) (j : Nat) :
    paddedState A j=xorByte (xorByte A (8*j) 0x1f) 135 0x80 := by
  rw [paddedState,xorWord_suffix,xorWord_terminal]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailHashFirst.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3

theorem firstState_byte (m : Mem) (mu w1 : Addr) {j : Nat} (hj : j<200) :
    byteOf (firstState m mu w1) j=
      if j<64 then m (mu+BitVec.ofNat 64 j)
      else if j<136 then m (w1+BitVec.ofNat 64 (j-64)) else 0 := by
  rw [byteOf_eq' _ hj]
  simp only [firstState,Vector.getElem_ofFn]
  by_cases h64 : j<64
  · rw [ite_eq_left (by omega : j/8<8),ite_eq_left h64]
    simp only [Mem.readW,BitVec.setWidth_eq]
    rw [Mem.extractLsb'_read _ _ (by omega : j%8<64/8)]
    simp only [laneAddr,BitVec.add_assoc,←BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega]
  · rw [ite_eq_right (by omega : ¬j/8<8),ite_eq_right h64]
    by_cases h136 : j<136
    · rw [ite_eq_left (by omega : j/8<17),ite_eq_left h136]
      simp only [Mem.readW,BitVec.setWidth_eq]
      rw [Mem.extractLsb'_read _ _ (by omega : j%8<64/8)]
      simp only [laneAddr,BitVec.add_assoc,←BitVec.ofNat_add,show 8*(j/8-8)+j%8=j-64 by omega]
    · rw [ite_eq_right (by omega : ¬j/8<17),ite_eq_right h136]
      exact BitVec.extractLsb'_zero

theorem firstState_eq (m : Mem) (mu w1 : Addr) :
    firstState m mu w1=xorBytes zero (bytesAt m mu 64++bytesAt m w1 72) := by
  apply ext_bytes
  intro j hj
  rw [firstState_byte m mu w1 hj,byteOf_xorBytes _ _ hj]
  have hz : byteOf zero j=0 := by
    rw [byteOf_eq' _ hj]
    simp [zero]
  rw [hz]
  change _=(0#8) ^^^ _
  rw [BitVec.zero_xor]
  by_cases h64 : j<64
  · rw [ite_eq_left h64]
    simp only [bytesAt,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_map,List.length_range,
      h64,↓reduceIte,List.getElem?_map,List.getElem?_range h64,Option.map_some,Option.getD_some]
  · rw [ite_eq_right h64]
    simp only [bytesAt,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_map,List.length_range,
      h64,↓reduceIte,List.getElem?_map]
    by_cases h136 : j<136
    · rw [ite_eq_left h136,List.getElem?_range (by omega : j-64<72)]
      rfl
    · rw [ite_eq_right h136,List.getElem?_eq_none (by simp;omega)]
      rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailHashBlocks.lean` -/

section

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

end

/-! ## From `CommitTailHashRun.lean` -/

section

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

end
