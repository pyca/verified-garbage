module
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContext

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass

/-! # Retain the checked RSA status while preparing to erase the encoding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaPkcs1Sig.X86.Sign

theorem wipeArgs_ok {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block [.mov .ebx (.reg .eax), .mov .eax (.imm 0), .mov .esi (.reg .esp),
      .alu .add .esi (.imm (BitVec.ofNat 32 emOffset)), .mov .ecx (.mem (incoming 3))]) s
      fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps [.ebx, .eax, .esi, .ecx] s t ∧
        t.gpr .ebx = s.gpr .eax ∧ t.gpr .eax = 0 ∧ t.gpr .esi = g.temporary ∧
        t.gpr .ecx = BitVec.ofNat 32 g.length := by
  unfold incoming stackAt
  refine wp_movS rfl fun a A _ => ?_
  refine wp_movS rfl fun b B _ => ?_
  refine wp_movS rfl fun c C _ => ?_
  refine wp_addS rfl fun d D _ => ?_
  have K : Keeps [.ebx, .eax, .esi, .ecx] s d :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans
      ((C.keeps.mono (by decide)).trans (D.keeps.mono (by decide))))
  have M : d.mem = s.mem := D.mem.trans (C.mem.trans (B.mem.trans A.mem))
  have hd := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 3 < 21)) fun t T => WP.block_nil ?_
  have kt := K.trans (T.keeps.mono (by decide))
  have mt := T.mem.trans M
  refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)), mt, kt, ?_, ?_, ?_, ?_⟩
  · rw [T.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide), B.other .ebx (by decide), A.gpr]
  · rw [T.other .eax (by decide), D.other .eax (by decide), C.other .eax (by decide), B.gpr]
  · rw [T.other .esi (by decide), D.gpr, C.gpr, B.other .esp (by decide), A.other .esp (by decide), h.sp]
    rfl
  · rw [T.gpr, hd.argumentValue (by decide : 3 < 21)]
    rfl

end VG.Proof.RsaPkcs1Sig.X86.Sgn
