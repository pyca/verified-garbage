module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptSaveFlag
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptPublicCall

/-! # Restore the padding flag and combine it with checked RSA's status -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

theorem savedFlag_publicFrame {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (h : Context g bs s) (F : Frame (publicWr g ++ [g.calleeRegion]) s.mem t.mem) :
    savedFlag g t = savedFlag g s := by
  have sub : (⟨byteAddr g.stack + BitVec.ofNat 64 zeroOffset, 4⟩ : Region).Sub g.innerRegion :=
    Offset.sub_base _ (by decide)
  apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 zeroOffset, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [publicWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact (h.valid.stackOutput.sub_left (fun x hx => h.valid.innerSub x (sub x hx)))
  · exact (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (sub x hx)))
  · exact Offset.disjoint_base _ (by decide : 40 ≤ zeroOffset) (by decide)
  · exact (h.valid.calleeInner.sub_right sub).symm

theorem maskArgs_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block maskArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t ∧
      t.gpr .edx = savedFlag g s - 1 ∧
      t.gpr .ebx = (s.gpr .eax &&& (savedFlag g s - 1)) &&& 1 ∧
      t.gpr .esi = g.output ∧ t.gpr .ecx = BitVec.ofNat 32 g.length := by
  unfold maskArgs stackAt incoming
  refine wp_ldm rfl
    (by rw [h.address (by decide)]; exact h.inner.read (by decide)) fun a A => ?_
  refine wp_subS rfl fun b B _ => ?_
  refine wp_logicS (Or.inl rfl) rfl fun c C => ?_
  refine wp_logicS (Or.inl rfl) rfl fun d D => ?_
  refine wp_movS rfl fun e E _ => ?_
  have K₁ : Keeps [.eax, .ebx, .edx] s e :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans
      ((C.keeps.mono (by decide)).trans ((D.keeps.mono (by decide)).trans (E.keeps.mono (by decide)))))
  have M₁ : e.mem = s.mem := E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem)))
  have he : Context g bs e := h.after (by rw [M₁]; exact Frame.refl _ _) K₁ (K₁.1 .esp (by decide))
  refine wp_ldm rfl (he.readArg (by decide : 0 < 14)) fun f F => ?_
  have hf := he.after (by rw [F.mem]; exact Frame.refl _ _) F.keeps (F.other .esp (by decide))
  refine wp_ldm rfl (hf.readArg (by decide : 3 < 14)) fun t T => WP.block_nil ?_
  have K : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t :=
    (K₁.mono (by decide)).trans ((F.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))
  have M : t.mem = s.mem := T.mem.trans (F.mem.trans M₁)
  have mask : b.gpr .edx = savedFlag g s - 1 := by
    rw [B.gpr, A.gpr, h.address (by decide)]
    rfl
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_, ?_, ?_, ?_⟩
  · rw [T.other .edx (by decide), F.other .edx (by decide), E.other .edx (by decide),
      D.other .edx (by decide), C.other .edx (by decide), mask]
  · rw [T.other .ebx (by decide), F.other .ebx (by decide), E.gpr, D.gpr, C.gpr,
      B.other .eax (by decide), A.other .eax (by decide), mask]
    rfl
  · rw [T.other .esi (by decide), F.gpr, he.argumentValue (by decide : 0 < 14)]
    rfl
  · rw [T.gpr, hf.argumentValue (by decide : 3 < 14)]
    rfl

end VG.Proof.RsaPkcs1Enc.X86.Enc
