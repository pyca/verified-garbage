module

public import VerifiedGarbage.Proof.Gcm.Ctr

/-! # Use one bitsliced CTR operation beginning at J₀ for both tag and payload -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32 inc32 gctr)
open VG.Proof.Gcm

/-- A contiguous sequence of masks produced by applying CTR to zero blocks. -/
structure Masks (m : Mem) (out : Addr) (ciph : Block → Block) (j0 : Block) (n : Nat) : Prop where
  tag : blockAt m out = ciph j0
  stream : ∀ (d : List Byte), d.length ≤ n →
    List.zipWith (· ^^^ ·) d (bytesAt m (out+16) d.length) = gctr ciph (inc32 j0) d

theorem masks_of_ctr {m : Mem} {out : Addr} {ciph : Block → Block} {j0 : Block} {n : Nat}
    (run : blocksAt m out ((n+15)/16+1) = ctr32 ciph j0 (List.replicate ((n+15)/16+1) 0)) :
    Masks m out ciph j0 n := by
  have block (i : Nat) (hi : i < (n+15)/16+1) :
      blockAt m (out+BitVec.ofNat 64 (16*i)) = ciph (Nat.repeat inc32 i j0) := by
    have e := congrArg (fun xs => xs.getD i 0) run
    rw [blocksAt_getD _ _ _ hi,ctr32_getD _ _ _ (by simpa using hi)] at e
    simpa [List.getD_eq_getElem?_getD,hi] using e
  refine ⟨by simpa [Nat.repeat] using block 0 (by omega),fun d bound => ?_⟩
  rw [gctr_eq]
  refine zipWith_eq_xorKs (by simp [bytesAt]) fun k hk => ?_
  rw [getD_bytesAt' _ _ hk,Nat.zero_add,ksByte]
  have ptr : out + 16 + BitVec.ofNat 64 k =
      out+BitVec.ofNat 64 (16*(k/16+1)) + BitVec.ofNat 64 (k%16) := by
    change out + BitVec.ofNat 64 16 + _ = _
    rw [BitVec.add_assoc,BitVec.add_assoc,← BitVec.ofNat_add,← BitVec.ofNat_add]
    congr 2; omega
  rw [ptr,bytes_toBytes_blockAt m (out+BitVec.ofNat 64 (16*(k/16+1))) (Nat.mod_lt k (by decide)),block _ (by omega),repeat_add]
  rfl

end VG.Proof.AesGcm.RISCV64.Contiguous
