import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackGroupMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackGroup

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Proof.MlDsa.Pack
open VG.Proof.MlKem (digits)

theorem group_written (signed : Bool) (b d c : Nat) (hd : d≤20) (hc : c≤8)
    (halign : d*c%8=0) (ht : TailWidth (d*c/8)) (m : Mem) (input out : Addr)
    (V : Nat → Nat) (hV : ∀j<c,V j<2^d)
    (hin : ∀j<c,inputValue signed b m input j=BitVec.ofNat 64 (V j)) :
    Written m (groupResult signed b d c m input out).1 out (d*c/8)
      (byteOf (digits d ((List.range c).map V))) := by
  let G := digits d ((List.range c).map V)
  have hf := fieldsRun_values d out (inputValue signed b m input)
    (fun j=>BitVec.ofNat 64 (G/2^(d*j)%2^d)) ⟨m,0⟩ (fun j hj=>by
      rw [hin j hj,digits_range_get hV hj])
  unfold groupResult
  rw [hf]
  exact stream_written G d c hd hc halign ht (digits_range_lt hV) m out 0

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
