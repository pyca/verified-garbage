module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfBodyFrames

/-! # Rejection PRFs keep the RSA result, returned status and length output -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem rejectionFrame_output {g : Geometry} {bs : Fin 9 → List Byte} {s t : State}
    (h : Context g bs s) (F : Frame (rejectionWrites g) s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.length = Spec.Rsa.bytesAt s.mem (byteAddr g.output) g.length := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by have := h.valid.maxLength; omega)
  intro r hr
  simp only [rejectionWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.valid.outputWorkspace
  · exact (h.valid.stackOutput.sub_left h.valid.calleeSub).symm
  · exact (h.valid.stackOutput.sub_left (fun x hx => h.valid.innerSub x (h.outgoingSub x hx))).symm
  · exact (h.valid.stackOutput.sub_left (fun x hx => h.valid.innerSub x
      (Offset.sub_base _ (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) x hx))).symm
  · exact (h.valid.stackOutput.sub_left (fun x hx => h.valid.innerSub x
      (Offset.sub_base _ (by decide : oNB + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) x hx))).symm

theorem rejectionFrame_status {g : Geometry} {bs : Fin 9 → List Byte} {s t : State}
    (h : Context g bs s) (F : Frame (rejectionWrites g) s.mem t.mem) : savedStatus g t = savedStatus g s := by
  have slot : (⟨byteAddr g.stack + BitVec.ofNat 64 oR, 4⟩ : Region).Sub g.innerRegion := Offset.sub_base _ (by decide)
  apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 oR, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [rejectionWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (slot x hx))
  · exact (h.valid.calleeInner.sub_right slot).symm
  · exact Offset.disjoint_base _ (by decide : 80 ≤ oR) (by decide)
  · exact Offset.disjoint _ (Or.inl (by decide : oR + 4 ≤ oI)) (by decide) (by decide)
  · exact Offset.disjoint _ (Or.inl (by decide : oR + 4 ≤ oNB)) (by decide) (by decide)

end VG.Proof.RsaPkcs1Enc.X86.Dec
