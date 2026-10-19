module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigest
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContext
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackWord
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Address the recovered digest and load its public encoding parameters -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (incoming stackAt lea em1Offset em2Offset)
open VG.Impl.RsaPkcs1Sig.X86.Recover

theorem Context.loadArgument {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) {j : Nat} (hj : j < 13) :
    readSrc s (.mem (incoming j)) = some (g.argument j) := by
  change s.load32 (addr (s.gpr .esp) (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) = _
  rw [State.load32, ite_eq_left (h.readArg hj), h.argumentValue hj]

theorem digestPtr_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block digestPtr) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.esi] s t ∧ t.gpr .esi = g.digest := by
  unfold digestPtr lea
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  have K : Keeps [.esi] s b := A.keeps.trans B.keeps
  have M := B.mem.trans A.mem
  have hb := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  refine wp_addS (hb.loadArgument (by decide : 3 < 13)) fun c C _ => ?_
  have hc := hb.after (by rw [C.mem]; exact Frame.refl _ _) C.keeps (C.other .esp (by decide))
  refine wp_subS (hc.loadArgument (by decide : 1 < 13)) fun t T _ => WP.block_nil ?_
  have kt := K.trans (C.keeps.trans T.keeps)
  have mt := T.mem.trans (C.mem.trans M)
  refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)), mt, kt, ?_⟩
  rw [T.gpr, C.gpr, B.gpr, A.gpr, h.sp]
  exact h.valid.digestPointer

theorem encArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block encArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.edi, .ecx, .edx, .ebp, .esi] s t ∧ t.gpr .edi = g.em2 ∧
      t.gpr .ecx = BitVec.ofNat 32 g.length ∧ t.gpr .edx = g.hash ∧
      t.gpr .ebp = BitVec.ofNat 32 g.outputLength ∧ t.gpr .esi = g.digest := by
  unfold encArgs lea
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => WP.block_nil ?_
  have K : Keeps [.edi] s b := A.keeps.trans B.keeps
  have M := B.mem.trans A.mem
  have hb := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  unfold incoming stackAt
  refine wp_ldm rfl (hb.readArg (by decide : 3 < 13)) fun c C => ?_
  have hc := hb.after (by rw [C.mem]; exact Frame.refl _ _) C.keeps (C.other .esp (by decide))
  refine wp_ldm rfl (hc.readArg (by decide : 6 < 13)) fun d D => ?_
  have hd := hc.after (by rw [D.mem]; exact Frame.refl _ _) D.keeps (D.other .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 1 < 13)) fun e E => WP.block_nil ?_
  have ke : Keeps [.edi, .ecx, .edx, .ebp, .esi] s e := (K.mono (by decide)).trans
    ((C.keeps.mono (by decide)).trans ((D.keeps.mono (by decide)).trans (E.keeps.mono (by decide))))
  have me := E.mem.trans (D.mem.trans (C.mem.trans M))
  have he := h.after (by rw [me]; exact Frame.refl _ _) ke (ke.1 .esp (by decide))
  refine WP.mono (digestPtr_ok he) ?_
  rintro t ⟨ht, Mt, Kt, ptr⟩
  refine ⟨ht, Mt.trans me, ke.trans (Kt.mono (by decide)), ?_, ?_, ?_, ?_, ptr⟩
  · rw [Kt.1 .edi (by decide), E.other .edi (by decide), D.other .edi (by decide), C.other .edi (by decide), B.gpr, A.gpr, h.sp]
    rfl
  · rw [Kt.1 .ecx (by decide), E.other .ecx (by decide), D.other .ecx (by decide), C.gpr, hb.argumentValue (by decide : 3 < 13)]
    rfl
  · rw [Kt.1 .edx (by decide), E.other .edx (by decide), D.gpr, hc.argumentValue (by decide : 6 < 13)]
    rfl
  · rw [Kt.1 .ebp (by decide), E.gpr, hd.argumentValue (by decide : 1 < 13)]
    rfl

end VG.Proof.RsaPkcs1Sig.X86.Rcv
