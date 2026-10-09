import VerifiedGarbage.Proof.MlDsa.Pack.Written
import VerifiedGarbage.Proof.MlDsa.Pack.Stream

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.Proof.MlDsa.Pack

theorem written_word (m : Mem) (out : Addr) (n : Nat) (v : BitVec (8*n)) :
    Written m (m.writeW out v) out n (fun j=>v.extractLsb' (8*j) 8) := by
  intro x
  simp only [Mem.writeW,show 8*n/8=n by omega,Mem.write]
  have h : 8*(8*n/8)=8*n := by omega
  rw [h,BitVec.setWidth_eq]

theorem written_of_frame {m t : Mem} {out : Addr} {n : Nat} {v : Nat → Byte}
    (hf : Frame [⟨out,n⟩] m t) (hb : ∀j<n,t (out+BitVec.ofNat 64 j)=v j) :
    Written m t out n v := by
  intro x
  split
  · rename_i h
    have ha : out+BitVec.ofNat 64 (x-out).toNat=x := by
      rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_comm,BitVec.sub_add_cancel]
    simpa only [ha] using hb (x-out).toNat h
  · rename_i h
    apply hf x
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    simp only [Region.Contains]
    omega

theorem written_append {m a t : Mem} {out : Addr} {n k : Nat} {v : Nat → Byte}
    (h : Written m a out n v)
    (ht : Written a t (out+BitVec.ofNat 64 n) k (fun j=>v (n+j)))
    (hn : n+k<2^64) : Written m t out (n+k) v := by
  have hf : Frame [⟨out,n+k⟩] m a := h.frame (by
    simpa only [BitVec.add_zero] using Offset.contains_base out (d:=0) (by omega : 0+n≤n+k) (by omega))
  have hb : ∀j<n,a (out+BitVec.ofNat 64 j)=v j := by
    intro j hj
    rw [h,Mem.sub_ofNat_toNat out (by omega),ite_eq_left hj]
  obtain ⟨hf',hb'⟩ := Written.step hf hb ht (Nat.le_refl _) hn
  exact written_of_frame hf' hb'

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
