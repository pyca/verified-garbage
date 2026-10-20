module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContext

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass

/-! # Load the public encoder arguments without changing memory -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Mont.X86

theorem encArgs_ok {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block encArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.edi, .ecx, .edx, .esi, .ebp] s t ∧
      t.gpr .edi = g.temporary ∧ t.gpr .ecx = BitVec.ofNat 32 g.length ∧
      t.gpr .edx = g.hash ∧ t.gpr .esi = g.sources 2 ∧ t.gpr .ebp = BitVec.ofNat 32 g.digestLength := by
  unfold encArgs incoming stackAt
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  have hb : Context g bs b := h.after (by rw [B.mem, A.mem]; exact Frame.refl _ _)
    (A.keeps.widen B.keeps (by decide)) (by rw [B.other .esp (by decide), A.other .esp (by decide)])
  refine wp_ldm rfl (hb.readArg (by decide : 3 < 21)) fun c C => ?_
  have hc : Context g bs c := hb.after (by rw [C.mem]; exact Frame.refl _ _) C.keeps (C.other .esp (by decide))
  refine wp_ldm rfl (hc.readArg (by decide : 6 < 21)) fun d D => ?_
  have hd : Context g bs d := hc.after (by rw [D.mem]; exact Frame.refl _ _) D.keeps (D.other .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 7 < 21)) fun e E => ?_
  have he : Context g bs e := hd.after (by rw [E.mem]; exact Frame.refl _ _) E.keeps (E.other .esp (by decide))
  refine wp_ldm rfl (he.readArg (by decide : 8 < 21)) fun t T => WP.block_nil ?_
  have K : Keeps [.edi, .ecx, .edx, .esi, .ebp] s t :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans
      ((C.keeps.mono (by decide)).trans ((D.keeps.mono (by decide)).trans
        ((E.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))))
  have M : t.mem = s.mem := T.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem))))
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_, ?_, ?_, ?_, ?_⟩
  · rw [T.other .edi (by decide), E.other .edi (by decide), D.other .edi (by decide), C.other .edi (by decide), B.gpr, A.gpr, h.sp]
    rfl
  · rw [T.other .ecx (by decide), E.other .ecx (by decide), D.other .ecx (by decide), C.gpr, hb.argumentValue (by decide : 3 < 21)]
    rfl
  · rw [T.other .edx (by decide), E.other .edx (by decide), D.gpr, hc.argumentValue (by decide : 6 < 21)]
    rfl
  · rw [T.other .esi (by decide), E.gpr, hd.argumentValue (by decide : 7 < 21)]
    rfl
  · rw [T.gpr, he.argumentValue (by decide : 8 < 21)]
    rfl

end VG.Proof.RsaPkcs1Sig.X86.Sgn
