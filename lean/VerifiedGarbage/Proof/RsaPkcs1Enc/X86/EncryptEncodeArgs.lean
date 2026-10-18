module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptStackWord
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEncodingRegions

/-! # Load padding and message pointers without altering the encoding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.RsaPkcs1Sig.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

theorem start_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block start) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.edi, .esi, .ebp] s t ∧ t.gpr .edi = g.temporary ∧
      t.gpr .esi = g.sources 3 ∧ t.gpr .ebp = BitVec.ofNat 32 g.paddingLength := by
  unfold start incoming stackAt
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  have hb : Context g bs b := h.after (by rw [B.mem, A.mem]; exact Frame.refl _ _)
    (A.keeps.widen B.keeps (by decide)) (by rw [B.other .esp (by decide), A.other .esp (by decide)])
  refine wp_ldm rfl (hb.readArg (by decide : 8 < 14)) fun c C => ?_
  have hc : Context g bs c := hb.after (by rw [C.mem]; exact Frame.refl _ _) C.keeps (C.other .esp (by decide))
  refine wp_ldm rfl (hc.readArg (by decide : 9 < 14)) fun t T => WP.block_nil ?_
  have K : Keeps [.edi, .esi, .ebp] s t :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans
      ((C.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))
  have M : t.mem = s.mem := T.mem.trans (C.mem.trans (B.mem.trans A.mem))
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_, ?_, ?_⟩
  · rw [T.other .edi (by decide), C.other .edi (by decide), B.gpr, A.gpr, h.sp]
    rfl
  · rw [T.other .esi (by decide), C.gpr, hb.argumentValue (by decide : 8 < 14)]
    rfl
  · rw [T.gpr, hc.argumentValue (by decide : 9 < 14)]
    rfl

theorem messageArgs_ok {g : Geometry} {bs : Fin 5 → List Byte} {s0 s : State} {acc : List Byte}
    (h : Context g bs s0) (dst : s0.gpr .edi = g.temporary) (room : acc.length < g.length)
    (w : W s0 acc s) :
    WP isa (.block messageArgs) s fun t => W s0 (acc ++ [0]) t ∧
      t.gpr .esi = g.sources 2 ∧ t.gpr .ebp = BitVec.ofNat 32 g.messageLength ∧
      t.gpr .ebx = s.gpr .ebx := by
  unfold messageArgs VG.Impl.RsaPkcs1Enc.X86.separator incoming stackAt
  refine WP.block_append (WP.mono (putByte_ok (h.buffer dst) room 0 w) ?_)
  rintro a ⟨wa, ka⟩
  have ha := (h.afterEncoding dst (by simp; omega) wa).1
  refine wp_ldm rfl (ha.readArg (by decide : 6 < 14)) fun b B => ?_
  have hb : Context g bs b := ha.after (by rw [B.mem]; exact Frame.refl _ _) B.keeps (B.other .esp (by decide))
  refine wp_ldm rfl (hb.readArg (by decide : 7 < 14)) fun t T => WP.block_nil ?_
  have kt : Keeps [.esi, .ebp] a t := (B.keeps.mono (by decide)).trans (T.keeps.mono (by decide))
  refine ⟨wa.after kt (by decide) (T.mem.trans B.mem) (kt.1 .edi (by decide)), ?_, ?_, ?_⟩
  · rw [T.other .esi (by decide), B.gpr, ha.argumentValue (by decide : 6 < 14)]
    rfl
  · rw [T.gpr, hb.argumentValue (by decide : 7 < 14)]
    rfl
  · exact (kt.1 .ebx (by decide)).trans (ka.1 .ebx (by decide))

end VG.Proof.RsaPkcs1Enc.X86.Enc
