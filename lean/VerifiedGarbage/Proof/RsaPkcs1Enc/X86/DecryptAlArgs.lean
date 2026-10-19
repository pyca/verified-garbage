module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfInit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMaskLoop

/-! # Prepare the public mask and alternative-length candidate scan -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem maskInit_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block maskInit) s fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx] s t ∧
      t.gpr .eax = 0 ∧ t.gpr .ecx = BitVec.ofNat 32 (g.length - 11) := by
  unfold maskInit incoming
  refine wp_ldm rfl (h.readArg (by decide : 4 < 23)) fun a A => ?_
  refine wp_subS rfl fun b B _ => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx] s t := (A.keeps.mono (by decide)).trans
    ((B.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))
  have M : t.mem = s.mem := T.mem.trans (B.mem.trans A.mem)
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, T.gpr, ?_⟩
  rw [T.other .ecx (by decide), B.gpr, A.gpr, h.argumentValue (by decide : 4 < 23)]
  change BitVec.ofNat 32 g.length - BitVec.ofNat 32 11 = _
  exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide : 11 < 2 ^ 32) (by have := h.valid.minLength; omega)

theorem alInit_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block alInit) s fun t => Context g bs t ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oMK, 4⟩] s.mem t.mem ∧
      Keeps [.ebx, .ebp, .esi, .edi, .ecx] s t ∧
      t.gpr .ebx = s.gpr .eax ∧ t.gpr .ebp = s.gpr .ecx ∧
      t.gpr .esi = g.workspace + BitVec.ofNat 32 sCL ∧ t.gpr .edi = 0 ∧ t.gpr .ecx = 128 := by
  have code : alInit = [.store (stackAt oMK) .eax] ++
      [.mov .ebx (.reg .eax), .mov .ebp (.reg .ecx), .mov .esi (.mem (incoming 21)),
        .alu .add .esi (.imm (BitVec.ofNat 32 sCL)), .mov .edi (.imm 0), .mov .ecx (.imm 128)] := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono (storeLocal_ok h .eax (by decide : oMK + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) ?_
  rintro a ⟨ha, _, Fa, Ka⟩
  refine wp_movS rfl fun b B _ => ?_
  refine wp_movS rfl fun c C _ => ?_
  have Kc : Keeps [.ebx, .ebp] a c := (B.keeps.mono (by decide)).trans (C.keeps.mono (by decide))
  have Mc : c.mem = a.mem := C.mem.trans B.mem
  have hc := ha.after (by rw [Mc]; exact Frame.refl _ _) Kc (Kc.1 .esp (by decide))
  unfold incoming
  refine wp_ldm rfl (hc.readArg (by decide : 21 < 23)) fun d D => ?_
  refine wp_addS rfl fun e E _ => ?_
  refine wp_movS rfl fun f F _ => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.ebx, .ebp, .esi, .edi, .ecx] s t := (Ka.mono (by simp)).trans
    ((Kc.mono (by decide)).trans ((D.keeps.mono (by decide)).trans
      ((E.keeps.mono (by decide)).trans ((F.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))))
  have M : t.mem = a.mem := T.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans Mc)))
  have Ft : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oMK, 4⟩] s.mem t.mem := by rw [M]; exact Fa
  refine ⟨h.after (Ft.sub ?_) K (K.1 .esp (by decide)), Ft, K, ?_, ?_, ?_, (T.other .edi (by decide)).trans F.gpr, T.gpr⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by decide : oMK + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)⟩
  · rw [T.other .ebx (by decide), F.other .ebx (by decide), E.other .ebx (by decide), D.other .ebx (by decide),
      C.other .ebx (by decide), B.gpr, Ka.1 .eax (by decide)]
  · rw [T.other .ebp (by decide), F.other .ebp (by decide), E.other .ebp (by decide), D.other .ebp (by decide),
      C.gpr, B.other .ecx (by decide), Ka.1 .ecx (by decide)]
  · rw [T.other .esi (by decide), F.other .esi (by decide), E.gpr, D.gpr, hc.argumentValue (by decide : 21 < 23)]
    rfl

end VG.Proof.RsaPkcs1Enc.X86.Dec
