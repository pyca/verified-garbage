module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfFrames
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMessage

/-! # A PRF body changes only its message, HMAC work, digest and counter -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def rejectionWrites (g : Geometry) : List Region :=
  [g.workspaceRegion, g.calleeRegion, ⟨byteAddr g.stack, 80⟩,
    ⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩, ⟨byteAddr g.stack + BitVec.ofNat 64 oNB, 4⟩]

def prfBodyWrites (g : Geometry) (dst : Nat) : List Region :=
  g.scratch sMsg 16 :: (⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩ :: prfMacWrites g dst)

theorem messageFrame_hash {g : Geometry} {bs : Fin 9 → List Byte} {s t : State}
    (h : Context g bs s) (F : Frame [g.scratch sMsg 16] s.mem t.mem) :
    Frame (hashWrites g) s.mem t.mem := F.sub (by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sMsg + 16 ≤ 8448)⟩)

theorem messageFrame_key {g : Geometry} {m m' : Mem}
    (F : Frame [g.scratch sMsg 16] m m') :
    Spec.Rsa.bytesAt m' (g.scratch sKDK 32).base 32 = Spec.Rsa.bytesAt m (g.scratch sKDK 32).base 32 := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact scratchDisjoint g (Or.inr (by decide : sMsg + 16 ≤ sKDK)) (by decide) (by decide)

theorem incrementFrame_scratch {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d n : Nat}
    (h : Context g bs s) (fit : d + n ≤ 8448)
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩] s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (g.scratch d n).base n = Spec.Rsa.bytesAt s.mem (g.scratch d n).base n := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by omega)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ((h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x
    (Offset.sub_base _ (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) x hx))).sub_right
      (h.valid.scratchSub fit)).symm

end VG.Proof.RsaPkcs1Enc.X86.Dec
