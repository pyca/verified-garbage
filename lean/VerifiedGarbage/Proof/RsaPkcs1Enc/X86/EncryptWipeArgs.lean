module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEncodingRegions
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptStackWord

/-! # Prepare to erase the encoding while retaining the masked status -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaPkcs1Enc.X86.Encrypt

theorem wipeArgs_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block wipeArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.eax, .esi, .ecx] s t ∧ t.gpr .eax = 0 ∧ t.gpr .esi = g.temporary ∧
      t.gpr .ecx = BitVec.ofNat 32 g.length := by
  unfold wipeArgs incoming stackAt
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  have K₁ : Keeps [.esi] s b := A.keeps.trans B.keeps
  have M₁ : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.after (by rw [M₁]; exact Frame.refl _ _) K₁ (K₁.1 .esp (by decide))
  refine wp_ldm rfl (hb.readArg (by decide : 3 < 14)) fun c C => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.eax, .esi, .ecx] s t := (K₁.mono (by decide)).trans
    ((C.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))
  have M : t.mem = s.mem := T.mem.trans (C.mem.trans M₁)
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, T.gpr, ?_, ?_⟩
  · rw [T.other .esi (by decide), C.other .esi (by decide), B.gpr, A.gpr, h.sp]
    rfl
  · rw [T.other .ecx (by decide), C.gpr, hb.argumentValue (by decide : 3 < 14)]
    rfl

end VG.Proof.RsaPkcs1Enc.X86.Enc
