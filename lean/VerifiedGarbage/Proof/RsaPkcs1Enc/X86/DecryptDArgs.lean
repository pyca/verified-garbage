module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptLocal
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptScratch

/-! # Save private RSA's status and prepare the padded private exponent -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def savedStatus (g : Geometry) (s : State) : BitVec 32 :=
  s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oR) 32

theorem dZero_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block dZero) s fun t => Context g bs t ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oR, 4⟩] s.mem t.mem ∧
      Keeps [.eax, .esi, .ecx] s t ∧ savedStatus g t = s.gpr .eax ∧
      t.gpr .esi = g.workspace + BitVec.ofNat 32 sD ∧
      t.gpr .ecx = BitVec.ofNat 32 g.length ∧ t.gpr .eax = 0 := by
  have code : dZero = [.store (stackAt oR) .eax] ++
      [.mov .esi (.mem (incoming 21)), .alu .add .esi (.imm (BitVec.ofNat 32 sD)),
        .mov .ecx (.mem (incoming 4)), .mov .eax (.imm 0)] := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono (storeLocal_ok h .eax (by decide : oR + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) ?_
  rintro a ⟨ha, Ma, Fa, Ka⟩
  unfold incoming stackAt
  refine wp_ldm rfl (ha.readArg (by decide : 21 < 23)) fun b B => ?_
  refine wp_addS rfl fun c C _ => ?_
  have Kpre : Keeps [.esi] a c := B.keeps.trans C.keeps
  have Mpre : c.mem = a.mem := C.mem.trans B.mem
  have hc := ha.after (by rw [Mpre]; exact Frame.refl _ _) Kpre (Kpre.1 .esp (by decide))
  refine wp_ldm rfl (hc.readArg (by decide : 4 < 23)) fun d D => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.eax, .esi, .ecx] s t := (Ka.mono (by simp)).trans
    ((Kpre.mono (by decide)).trans ((D.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))
  have M : t.mem = a.mem := T.mem.trans (D.mem.trans Mpre)
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oR, 4⟩] s.mem t.mem := by rw [M]; exact Fa
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), F, K, ?_, ?_, ?_, T.gpr⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by decide)⟩
  · unfold savedStatus
    rw [M, Ma, Mem.readW_writeW_self32]
  · rw [T.other .esi (by decide), D.other .esi (by decide), C.gpr, B.gpr,
      ha.argumentValue (by decide : 21 < 23)]
    rfl
  · rw [T.other .ecx (by decide), D.gpr, hc.argumentValue (by decide : 4 < 23)]
    rfl

theorem dCopy_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block dCopy) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .esi] s t ∧
      t.gpr .ebx = g.workspace + BitVec.ofNat 32 (sD + g.length - g.privateLength) ∧
      t.gpr .esi = g.sources 2 ∧ t.gpr .ecx = BitVec.ofNat 32 g.privateLength := by
  unfold dCopy
  refine wp_ldm rfl (h.readArg (by decide : 21 < 23)) fun a A => ?_
  refine wp_addS rfl fun b B _ => ?_
  have K₁ : Keeps [.ebx] s b := A.keeps.trans B.keeps
  have M₁ : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.after (by rw [M₁]; exact Frame.refl _ _) K₁ (K₁.1 .esp (by decide))
  refine wp_ldm rfl (hb.readArg (by decide : 4 < 23)) fun c C => ?_
  refine wp_addS rfl fun d D _ => ?_
  have K₂ : Keeps [.eax, .ebx] s d := (K₁.mono (by decide)).trans
    ((C.keeps.mono (by decide)).trans (D.keeps.mono (by decide)))
  have M₂ : d.mem = s.mem := D.mem.trans (C.mem.trans M₁)
  have hd := h.after (by rw [M₂]; exact Frame.refl _ _) K₂ (K₂.1 .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 8 < 23)) fun e E => ?_
  refine wp_subS rfl fun f F _ => ?_
  have K₃ : Keeps [.eax, .ebx, .ecx] s f := (K₂.mono (by decide)).trans
    ((E.keeps.mono (by decide)).trans (F.keeps.mono (by decide)))
  have M₃ : f.mem = s.mem := F.mem.trans (E.mem.trans M₂)
  have hf := h.after (by rw [M₃]; exact Frame.refl _ _) K₃ (K₃.1 .esp (by decide))
  refine wp_ldm rfl (hf.readArg (by decide : 7 < 23)) fun t T => WP.block_nil ?_
  have K : Keeps [.eax, .ebx, .ecx, .esi] s t := (K₃.mono (by decide)).trans (T.keeps.mono (by decide))
  have M : t.mem = s.mem := T.mem.trans M₃
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_, ?_, ?_⟩
  · rw [T.other .ebx (by decide), F.gpr, E.other .ebx (by decide), D.gpr, C.other .ebx (by decide),
      B.gpr, A.gpr, C.gpr, hb.argumentValue (by decide : 4 < 23), E.gpr,
      hd.argumentValue (by decide : 8 < 23), h.argumentValue (by decide : 21 < 23)]
    change (g.workspace + BitVec.ofNat 32 sD + BitVec.ofNat 32 g.length) - BitVec.ofNat 32 g.privateLength = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show (g.workspace + BitVec.ofNat 32 (sD + g.length)) - BitVec.ofNat 32 g.privateLength =
      g.workspace + (BitVec.ofNat 32 (sD + g.length) - BitVec.ofNat 32 g.privateLength) by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc],
      BitVec.ofNat_sub_ofNat_of_le _ _ (by have := h.valid.maxLength; have := h.valid.privateFits; omega)
        (by have := h.valid.privateFits; omega)]
  · rw [T.gpr, hf.argumentValue (by decide : 7 < 23)]
    rfl
  · rw [T.other .ecx (by decide), F.other .ecx (by decide), E.gpr,
      hd.argumentValue (by decide : 8 < 23)]
    rfl

end VG.Proof.RsaPkcs1Enc.X86.Dec
