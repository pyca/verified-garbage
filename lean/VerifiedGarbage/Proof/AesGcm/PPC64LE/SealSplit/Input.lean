module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.PartialCopy
public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: connect the split-block contract to the existing byte-stream seal proofs.
/-! # The plaintext assembled from source blocks and a destination suffix -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.Input
open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blocksAt toBytes)


def blocks (m : Mem) (S D : Addr) (total count : Nat) : List Spec.Gcm.Block :=
  blocksAt m S (count/16) ++ (blocksAt m D (total/16)).drop (count/16)


theorem bytes_blocksAt (m : Mem) (D : Addr) (n : Nat) :
    (blocksAt m D n).flatMap toBytes=bytesAt m D (16*n) := by
  apply VG.Proof.Gcm.list_ext (by rw [VG.Proof.Gcm.length_flatMap_toBytes,VG.Proof.Gcm.length_blocksAt,length_bytesAt])
  intro k hk
  have hk : k<16*n := by simpa only [VG.Proof.Gcm.length_flatMap_toBytes,VG.Proof.Gcm.length_blocksAt] using hk
  rw [VG.Proof.Gcm.getD_flatMap_toBytes _ _ (by rw [VG.Proof.Gcm.length_blocksAt]; exact hk),
    VG.Proof.Gcm.blocksAt_getD _ _ _ (by omega),VG.Proof.Gcm.getD_bytesAt' _ _ hk]
  have he : D+BitVec.ofNat 64 k=D+BitVec.ofNat 64 (16*(k/16))+BitVec.ofNat 64 (k%16) := by
    rw [Offset.add_add]
    congr 2
    omega
  rw [he,VG.Proof.Gcm.bytes_toBytes_blockAt m (D+BitVec.ofNat 64 (16*(k/16))) (k := k%16) (by omega)]


theorem blocks_drop (m : Mem) (D : Addr) (n k : Nat) (hk : k≤n) :
    (blocksAt m D n).drop k=blocksAt m (D+BitVec.ofNat 64 (16*k)) (n-k) := by
  have he := VG.Proof.Gcm.blocksAt_add m D k (n-k)
  rw [show k+(n-k)=n by omega] at he
  rw [he]
  exact List.drop_left' (VG.Proof.Gcm.length_blocksAt _ _ _)


theorem flat_blocks (m : Mem) (S D : Addr) (total count : Nat) (hc : count≤total) :
    (blocks m S D total count).flatMap toBytes=
      bytesAt m S (16*(count/16)) ++
        bytesAt m (D+BitVec.ofNat 64 (16*(count/16))) (16*(total/16-count/16)) := by
  rw [blocks,List.flatMap_append,blocks_drop _ _ _ _ (by omega),bytes_blocksAt,bytes_blocksAt]


theorem complete (m : Mem) (S D : Addr) (total count : Nat) (hc : count≤total) :
    (blocks m S D total count).flatMap toBytes ++
      bytesAt m (D+BitVec.ofNat 64 (16*(total/16))) (total%16)=
    bytesAt m S (count-count%16) ++ (bytesAt m D total).drop (count-count%16) := by
  rw [flat_blocks _ _ _ _ _ hc,List.append_assoc,PartialCopy.bytes_drop _ _ _ _ (by omega)]
  have hcount : 16*(count/16)=count-count%16 := by omega
  rw [← hcount]
  have hp : D+BitVec.ofNat 64 (16*(total/16))=
      D+BitVec.ofNat 64 (16*(count/16))+BitVec.ofNat 64 (16*(total/16-count/16)) := by
    rw [Offset.add_add]
    congr 2
    omega
  rw [hp,← bytesAt_add]
  congr 2
  omega


theorem copied {base s : State} {total count : Nat} (cfg : PartialCopy.Config base total count)
    (hs : PartialCopy.Result base count s) :
    (blocks s.mem (base.gpr .r7) (base.gpr .r27) total count).flatMap toBytes ++
      bytesAt s.mem (base.gpr .r27+BitVec.ofNat 64 (16*(total/16))) (total%16)=
      bytesAt base.mem (base.gpr .r7) count ++ (bytesAt base.mem (base.gpr .r27) total).drop count := by
  rw [complete _ _ _ _ _ cfg.bound]
  exact PartialCopy.Result.input cfg hs


theorem blocksAt_frame {rs : List Region} {m m' : Mem} {D : Addr} {n : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨D,16*n⟩ : Region).Disjoint r) :
    blocksAt m' D n=blocksAt m D n := by
  unfold blocksAt
  apply List.map_congr_left
  intro i hi
  have hi : i<n := List.mem_range.mp hi
  exact blockAt_frame hf (fun r hr => (hd r hr).sub_left
    (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*n) (by omega)))


end VG.Proof.AesGcm.PPC64LE.SealSplit.Input
