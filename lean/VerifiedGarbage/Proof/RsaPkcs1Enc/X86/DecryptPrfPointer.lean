module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfFinalizeArgs

/-! # Load the public PRF counter and message-buffer pointer -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem prfMsgPtr_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {i : Nat}
    (h : Context g bs s)
    (counter : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i) :
    WP isa (.block msgPtr) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.edi, .ebx, .edx] s t ∧ t.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg ∧
      t.gpr .ebx = BitVec.ofNat 32 i ∧ t.gpr .edx = BitVec.ofNat 32 g.length := by
  unfold msgPtr incoming stackAt
  refine wp_ldm rfl (h.readArg (by decide : 21 < 23)) fun a A => ?_
  refine wp_addS rfl fun b B _ => ?_
  have Kb : Keeps [.edi] s b := A.keeps.trans B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.after (by rw [Mb]; exact Frame.refl _ _) Kb (Kb.1 .esp (by decide))
  refine wp_ldm rfl (by
    rw [hb.address (by decide : oI < VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92)]
    exact hb.inner.read (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) fun c C => ?_
  have Kc : Keeps [.edi, .ebx] s c := (Kb.mono (by decide)).trans (C.keeps.mono (by decide))
  have Mc : c.mem = s.mem := C.mem.trans Mb
  have hc := h.after (by rw [Mc]; exact Frame.refl _ _) Kc (Kc.1 .esp (by decide))
  refine wp_ldm rfl (hc.readArg (by decide : 4 < 23)) fun t T => WP.block_nil ?_
  have K : Keeps [.edi, .ebx, .edx] s t := (Kc.mono (by decide)).trans (T.keeps.mono (by decide))
  have M : t.mem = s.mem := T.mem.trans Mc
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_, ?_, ?_⟩
  · rw [T.other .edi (by decide), C.other .edi (by decide), B.gpr, A.gpr,
      h.argumentValue (by decide : 21 < 23)]
    rfl
  · rw [T.other .ebx (by decide), C.gpr, Mb,
      hb.address (by decide : oI < VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92), counter]
  · rw [T.gpr, hc.argumentValue (by decide : 4 < 23)]
    rfl

end VG.Proof.RsaPkcs1Enc.X86.Dec
