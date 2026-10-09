import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskAccess

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def maskPoly (m : Mem) (a : Addr) (d : Nat) : Spec.MlDsa.Poly :=
  Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack (Spec.MlDsa.H (Spec.Sha3.bytesAt m a 66) (32*d))
    (2^(d-1)-1) (2^(d-1)))

def Decoded (σ t : State) (d : Nat) : Prop := Env σ t ∧
  Spec.MlDsa.PolyIs t.mem (σ.gpr .x2) (maskPoly σ.mem (σ.gpr .x0) d) ∧
  Spec.MlDsa.PolyIs t.mem (σ.gpr .x3) (maskPoly σ.mem (σ.gpr .x0+66) d)

theorem decode_ok {σ s : State} {d : Nat} (hp : Pre σ) (hd : d=18 ∨ d=20)
    (hs : SpongePost σ s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentMask.parseBoth d) s fun t => Decoded σ t d := by
  obtain ⟨he,hleft,hright⟩ := hs
  refine WP.mono (parseBoth_ok s hd (pairAccess_ok hp he hd)) ?_
  intro t ht
  have hk : RegKeep [.x0,.x4,.x9,.x11] s t := by
    refine ⟨?_,ht.rd,ht.wr,ht.sp⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact ht.gpr r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hf : Frame [⟨σ.gpr .x2,1024⟩,⟨σ.gpr .x3,1024⟩] s.mem t.mem := by
    simpa only [he.out1,he.out2] using ht.frame
  have ho : ∀ r∈[Region.mk (σ.gpr .x2) 1024,⟨σ.gpr .x3,1024⟩],
      (Region.mk (σ.gpr .x4) 8192).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.out1Sep.symm
    · exact hp.out2Sep.symm
  refine ⟨he.step hk hf (by decide) ?_ ?_ ?_,?_,?_⟩
  · intro r hr; exact ⟨r,List.mem_cons_of_mem _ hr,fun _ hx => hx⟩
  · intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by decide))
  · intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by decide))
  · have hv := ht.left.poly hd
    rw [he.out1,he.base] at hv
    rw [seedState_eq] at hleft
    rw [stream_mask_bytes hd (VG.Proof.Sha3.bytesAt_length _ _ _) hleft] at hv
    exact hv
  · have hv := ht.right.poly hd
    rw [he.out2,he.base] at hv
    rw [seedState_eq] at hright
    rw [stream_mask_bytes hd (VG.Proof.Sha3.bytesAt_length _ _ _) hright] at hv
    exact hv

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
