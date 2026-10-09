import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFirstBlocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F F_block)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (StreamOutput)

theorem firstStream_byte {σ s : State} {k : Nat}
    (h : StreamOutput s.mem (bufP σ k) 10 5 (A0 σ k)) {j : Nat} (hj : j<840) :
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j := by
  have hb := (h (j/168) (by omega)).byte (j := j%168) (by omega)
  change s.mem ((bufP σ k+BitVec.ofNat 64 (168*(j/168)))+BitVec.ofNat 64 (j%168)) = _ at hb
  rw [Offset.add_add,Nat.div_add_mod] at hb
  rw [hb,Resident.permuted_eq_iterF]
  exact (F_block σ k (by omega : j/168<6) (by omega : j%168<168)).symm.trans
    (congrArg (F σ k) (Nat.div_add_mod j 168))

theorem FirstBlocks.byte {v : Nat} {σ s : State} (h : FirstBlocks v σ s)
    {k j : Nat} (hk : k<v) (hj : j<840) :
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j :=
  firstStream_byte (h.bytes k hk) hj

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
