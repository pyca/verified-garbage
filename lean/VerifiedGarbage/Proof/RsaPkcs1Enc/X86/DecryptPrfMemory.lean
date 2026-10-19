module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfBody

/-! # A PRF iteration keeps KDK and every earlier output block -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem prfBody_bytes {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d n dst : Nat}
    (h : Context g bs s) (lower : 208 ≤ d) (upper : d + n ≤ sHash)
    (dstUpper : dst + 32 ≤ sHash) (apart : d + n ≤ dst ∨ dst + 32 ≤ d)
    (F : Frame (prfBodyWrites g dst) s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (g.scratch d n).base n = Spec.Rsa.bytesAt s.mem (g.scratch d n).base n := by
  have fit : d + n ≤ 8448 := by unfold sHash at upper; omega
  have dstFit : dst + 32 ≤ 8448 := by unfold sHash at dstUpper; omega
  apply VG.Proof.Rsa.rsa_bytes_frame F (by omega)
  intro r hr
  simp only [prfBodyWrites, prfMacWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact scratchDisjoint g (Or.inr (by unfold sMsg; omega)) fit (by decide)
  · exact ((h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x
      (Offset.sub_base _ (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) x hx))).sub_right
        (h.valid.scratchSub fit)).symm
  · exact scratchDisjoint g (Or.inr (by unfold sSt; omega)) fit (by decide)
  · exact scratchDisjoint g (Or.inr (by unfold sOuter; omega)) fit (by decide)
  · exact scratchDisjoint g (Or.inl upper) fit (by decide)
  · exact scratchDisjoint g apart fit dstFit
  · exact (h.argsScratch (by decide : 80 ≤ 160) fit).symm
  · exact (h.calleeScratch fit).symm

theorem prfBodyFrame_rejection {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {dst : Nat}
    (h : Context g bs s) (dstFit : dst + 32 ≤ sHash)
    (F : Frame (prfBodyWrites g dst) s.mem t.mem) : Frame (rejectionWrites g) s.mem t.mem := F.sub (by
  intro r hr
  simp only [prfBodyWrites, prfMacWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g.workspaceRegion, by simp [rejectionWrites], h.valid.scratchSub (by decide : sMsg + 16 ≤ 8448)⟩
  · exact ⟨_, by simp [rejectionWrites], fun _ hx => hx⟩
  · exact ⟨g.workspaceRegion, by simp [rejectionWrites], h.valid.scratchSub (by decide : sSt + 96 ≤ 8448)⟩
  · exact ⟨g.workspaceRegion, by simp [rejectionWrites], h.valid.scratchSub (by decide : sOuter + 96 ≤ 8448)⟩
  · exact ⟨g.workspaceRegion, by simp [rejectionWrites], h.valid.scratchSub (by decide : sHash + 832 ≤ 8448)⟩
  · exact ⟨g.workspaceRegion, by simp [rejectionWrites], h.valid.scratchSub (by unfold sHash at dstFit; omega)⟩
  · exact ⟨_, by simp [rejectionWrites], fun _ hx => hx⟩
  · exact ⟨g.calleeRegion, by simp [rejectionWrites], fun _ hx => hx⟩)

end VG.Proof.RsaPkcs1Enc.X86.Dec
