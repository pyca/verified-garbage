module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptMask
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptWipe

/-! # Mask the public result and erase the private encoding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

theorem afterPub_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa afterPub s fun t => Context g bs t ∧
      Frame [g.innerRegion, g.outputRegion] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t ∧
      t.gpr .eax = (s.gpr .eax &&& (savedFlag g s - 1)) &&& 1 ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.length =
        (Spec.Rsa.bytesAt s.mem (byteAddr g.output) g.length).map
          (fun b => b &&& (savedFlag g s - 1).setWidth 8) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.temporary) g.length = List.replicate g.length 0 := by
  unfold afterPub
  refine WP.seq (WP.mono (maskArgs_ok h) ?_)
  rintro u ⟨hu, M, K, mask, status, src, count⟩
  refine WP.seq (WP.mono (mask_ok hu src count) ?_)
  rintro v ⟨hv, Fv, Kv, bytes⟩
  refine WP.mono (wipe_ok hv) ?_
  rintro t ⟨ht, zero, result, Ft, Kt⟩
  have Kall := K.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))
  have frameOut : Frame [g.innerRegion, g.outputRegion] u.mem v.mem :=
    Fv.sub (by intro r hr; obtain rfl := List.mem_singleton.mp hr
               exact ⟨_, by simp, fun _ hx => hx⟩)
  have frameWipe : Frame [g.innerRegion, g.outputRegion] v.mem t.mem :=
    Ft.sub (by intro r hr; obtain rfl := List.mem_singleton.mp hr
               exact ⟨_, by simp, fun _ hx => hx⟩)
  have frameAll : Frame [g.innerRegion, g.outputRegion] s.mem t.mem := by
    rw [M] at frameOut
    exact frameOut.trans frameWipe
  have outputPreserved : Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.length =
      Spec.Rsa.bytesAt v.mem (byteAddr g.output) g.length := by
    apply VG.Proof.Rsa.rsa_bytes_frame Ft (by have := h.valid.maxLength; omega)
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.valid.stackOutput.sub_left h.valid.innerSub).symm
  refine ⟨ht, frameAll, Kall, ?_, ?_, zero⟩
  · rw [result, Kv.1 .ebx (by decide), status]
  · rw [outputPreserved, bytes, M, mask]

end VG.Proof.RsaPkcs1Enc.X86.Enc
