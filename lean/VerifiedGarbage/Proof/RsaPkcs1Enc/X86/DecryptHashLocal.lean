module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashFrames

/-! # Hash calls preserve local counters beyond the outgoing call area -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem hash_local {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d : Nat}
    (h : Context g bs s) (F : Frame (hashWrites g) s.mem t.mem)
    (lower : 80 ≤ d) (upper : d + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) :
    t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 d) 32 =
      s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 d) 32 := by
  have slot : (⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩ : Region).Sub g.innerRegion := Offset.sub_base _ upper
  apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (slot x hx))
  · exact (h.valid.calleeInner.sub_right slot).symm
  · exact Offset.disjoint_base _ lower (by unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes at upper; omega)

end VG.Proof.RsaPkcs1Enc.X86.Dec
