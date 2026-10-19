module

public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.Mem

/-! # Boolean masks of RSA output bytes -/

@[expose] public section
namespace VG.Proof.Rsa
open VG

theorem acceptance_byte_mask (b : Bool) (v : Byte) :
    v &&& (-BitVec.ofNat 32 b.toNat).setWidth 8 = if b then v else 0 := by
  cases b
  · change v &&& 0#8 = 0#8
    exact BitVec.and_zero
  · change v &&& BitVec.allOnes 8 = v
    exact BitVec.and_allOnes

theorem acceptance_bytes_mask (b : Bool) (bs : List Byte) :
    bs.map (· &&& (-BitVec.ofNat 32 b.toNat).setWidth 8) = if b then bs else List.replicate bs.length 0 := by
  simp only [acceptance_byte_mask]
  cases b
  · exact List.map_const'
  · simp

end VG.Proof.Rsa
