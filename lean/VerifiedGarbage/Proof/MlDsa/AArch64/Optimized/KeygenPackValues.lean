import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackGroupBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack

def fieldValueNat (signed : Bool) (b : Nat) (x : BitVec 32) : Nat :=
  if signed then VG.Proof.MlDsa.AArch64.Pack.bpVal b x else x.toNat

theorem inputValue_nat (signed : Bool) (b : Nat) (m : Mem) (input : Addr) (j : Nat)
    (hb : b<q) (hx : (coeffAt m input j).toNat<q) :
    inputValue signed b m input j=BitVec.ofNat 64 (fieldValueNat signed b (coeffAt m input j)) := by
  cases signed
  · simp [inputValue,fieldValueNat]
  · simp only [inputValue,fieldValueNat,↓reduceIte]
    rw [show (encoded b (coeffAt m input j)).setWidth 64=
      BitVec.ofNat 64 (encoded b (coeffAt m input j)).toNat by simp,
      encoded_bpVal hb hx]

theorem inputValue_shift (signed : Bool) (b : Nat) (m : Mem) (input : Addr) (k j : Nat) :
    inputValue signed b m (input+BitVec.ofNat 64 (4*k)) j=inputValue signed b m input (k+j) := by
  unfold inputValue coeffAt
  rw [BitVec.add_assoc,←BitVec.ofNat_add,←Nat.mul_add]

theorem inputValue_frame (signed : Bool) (b : Nat) {m t : Mem} {input : Addr}
    {rs : List Region} (h : Frame rs m t)
    (hs : ∀r∈rs,(polyRegion input).Disjoint r) {j : Nat} (hj : j<256) :
    inputValue signed b t input j=inputValue signed b m input j := by
  unfold inputValue
  rw [coeffAt_frame h hs hj]

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
