module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMessagePrefix

/-! # Encode the fixed or modulus-dependent public PRF bit length -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

theorem clLen_ok {g : Geometry} {bs : Fin 9 → List Byte} {s0 s : State} {label : List Byte} {i : Nat}
    (ptr : s0.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg) (labelLength : label.length = 6)
    (h : MessageWritten g bs s0 (prfMessage i label 256) 8 s) :
    WP isa (.block clLen) s (MessageWritten g bs s0 (prfMessage i label 256) 10) := by
  have high : (prfMessage i label 256).getD 8 0 = BitVec.ofNat 8 8 := by
    have raw := prfMessage_high i label 256
    simpa only [labelLength] using raw
  have low : (prfMessage i label 256).getD 9 0 = BitVec.ofNat 8 0 := by
    have raw := prfMessage_low i label 256
    simpa only [labelLength, show BitVec.ofNat 8 (8 * 256) = BitVec.ofNat 8 0 by decide] using raw
  unfold clLen
  rw [WP.block_append_iff]
  refine WP.mono (h.put ptr (by decide : 8 < 16) high) ?_
  intro a ha
  exact ha.put ptr (by decide : 9 < 16) low

theorem amLen_ok {g : Geometry} {bs : Fin 9 → List Byte} {s0 s : State} {label : List Byte} {i : Nat}
    (ptr : s0.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg) (labelLength : label.length = 7)
    (length : s0.gpr .edx = BitVec.ofNat 32 g.length)
    (h : MessageWritten g bs s0 (prfMessage i label g.length) 9 s) :
    WP isa (.block amLen) s (MessageWritten g bs s0 (prfMessage i label g.length) 11) := by
  have high : (prfMessage i label g.length).getD 9 0 = BitVec.ofNat 8 (8 * g.length / 256) := by
    simpa only [labelLength] using prfMessage_high i label g.length
  have low : (prfMessage i label g.length).getD 10 0 = BitVec.ofNat 8 (8 * g.length) := by
    simpa only [labelLength] using prfMessage_low i label g.length
  unfold amLen
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  refine wp_addS rfl fun c C _ => ?_
  refine wp_addS rfl fun d D _ => ?_
  refine wp_movS rfl fun e E _ => ?_
  refine wp_shr (by decide) fun f F _ => ?_
  have K : Keeps [.eax, .ecx] s f := (A.keeps.mono (by decide)).trans
    ((B.keeps.mono (by decide)).trans ((C.keeps.mono (by decide)).trans
      ((D.keeps.mono (by decide)).trans ((E.keeps.mono (by decide)).trans (F.keeps.mono (by decide))))))
  have M : f.mem = s.mem := F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem))))
  have hf := h.update K M
  have ax : f.gpr .eax = BitVec.ofNat 32 (8 * g.length) := by
    rw [F.other .eax (by decide), E.other .eax (by decide), D.gpr, C.gpr, B.gpr, A.gpr,
      h.keep.1 .edx (by decide), length]
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  have cx : f.gpr .ecx = BitVec.ofNat 32 (8 * g.length / 256) := by
    rw [F.gpr, E.gpr]
    have axd : d.gpr .eax = BitVec.ofNat 32 (8 * g.length) := by
      rw [← ax, F.other .eax (by decide), E.other .eax (by decide)]
    rw [axd, shr8 h.context.valid.maxLength]
  have code : ([.store8 ⟨.edi, 9⟩ .cl, .store8 ⟨.edi, 10⟩ .al] : List Instr) =
      [.store8 ⟨.edi, 9⟩ .cl] ++ [.store8 ⟨.edi, 10⟩ .al] := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono (messageStore_ok hf.context ((hf.keep.1 .edi (by decide)).trans ptr)
    (by decide : 9 < 16) .cl) ?_
  rintro t ⟨ht, Mt, Ft, Kt⟩
  have htW := hf.after_store (by decide : 9 < 16) ht (Kt.mono (by simp)) (by
    change t.mem = f.mem.writeW _ ((f.gpr .ecx).setWidth 8) at Mt
    rw [cx, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32), ← high] at Mt
    exact Mt) Ft
  exact htW.store ptr (by decide : 10 < 16) .al (by
    change (t.gpr .eax).setWidth 8 = _
    rw [Kt.1 .eax (by decide), ax, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32), low])

end VG.Proof.RsaPkcs1Enc.X86.Dec
