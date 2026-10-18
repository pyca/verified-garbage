module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEncoding
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptAfter
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Mask32

/-! # Correct precomputed encryption, including invalid random padding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

theorem Context.words_preserved {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (h : Context g bs s) (F : Frame (bodyWrites g) s.mem t.mem) :
    Spec.Rsa.wordsAt t.mem (byteAddr (g.sources 4)) g.preLength =
      Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength := by
  apply VG.Proof.Rsa.wordsAt_frame F ?_ (h.sourceSeparate 4)
  have fit := h.valid.sourceFits 4
  change (g.sources 4).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
  omega

theorem innerFrame_body {g : Geometry} {m m' : Mem}
    (F : Frame [g.innerRegion] m m') : Frame (bodyWrites g) m m' := by
  apply F.sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩

def BodyOut (g : Geometry) (bs : Fin 5 → List Byte) (s t : State) : Prop :=
  Spec.Rsa.publicPrecompute (bs 0) = some (Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength) →
    Spec.Rsa.written t.mem (byteAddr g.output) g.length (t.gpr .eax)
      (Spec.RsaPkcs1Enc.encrypt (bs 0) (bs 1) (bs 2) (bs 3))

theorem body_ok (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (body v.name v.code) s fun t => Context g bs t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t ∧
      BodyOut g bs s t := by
  unfold body
  refine WP.seq (WP.mono (start_ok h) ?_)
  rintro a ⟨ha, Ma, Ka, dst, src, count⟩
  refine WP.seq (WP.mono (encoding_ok ha dst src count) ?_)
  rintro b ⟨hb, Fb, Kb, encoded, flag⟩
  refine WP.seq (WP.mono (callArgs_ok hb) ?_)
  rintro c ⟨hc, args, Fc, Kc, saved⟩
  have tempSeparate : (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 44⟩ := by
    rw [Geometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 44 ≤ emOffset)
      (by have := h.valid.maxLength; simp only [emOffset]; omega)
  have encodedC : Spec.Rsa.bytesAt c.mem (byteAddr g.temporary) g.length = Spec.RsaPkcs1Enc.encode (bs 2) (bs 3) := by
    have same : Spec.Rsa.bytesAt c.mem (byteAddr g.temporary) g.length =
        Spec.Rsa.bytesAt b.mem (byteAddr g.temporary) g.length := VG.Proof.Rsa.rsa_bytes_frame Fc
      (by have := h.valid.maxLength; omega)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact tempSeparate)
    exact same.trans encoded
  have FbAll : Frame (bodyWrites g) a.mem b.mem := by
    apply Fb.sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], ha.temporarySub⟩
  have FcAll : Frame (bodyWrites g) b.mem c.mem := by
    apply innerFrame_body
    apply Fc.sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have Fac : Frame (bodyWrites g) s.mem c.mem := by
    rw [Ma] at FbAll
    exact FbAll.trans FcAll
  refine WP.seq (WP.mono (public_call v hc args) ?_)
  rintro d ⟨hd, Fd, Kd, publicOut⟩
  have flagD : savedFlag g d = BitVec.ofNat 32 (hasZero (bs 3)).toNat :=
    (savedFlag_publicFrame hc Fd).trans (saved.trans flag)
  have FdAll : Frame (bodyWrites g) c.mem d.mem := by
    apply Fd.sub
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact publicWrites_sub hc r hr
    · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  refine WP.mono (afterPub_ok hd) ?_
  rintro t ⟨ht, Ft, Kt, status, bytes, zero⟩
  have FtAll : Frame (bodyWrites g) d.mem t.mem := by
    apply Ft.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
    · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  have K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t :=
    (Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans
      ((Kd.mono (by decide)).trans (Kt.mono (by decide)))))
  refine ⟨ht, Fac.trans (FdAll.trans FtAll), K, ?_⟩
  intro cache
  have cacheC : Spec.Rsa.publicPrecompute (bs 0) = some (Spec.Rsa.wordsAt c.mem (byteAddr (g.sources 4)) g.preLength) := by
    rw [h.words_preserved Fac]
    exact cache
  have pub := publicOut cacheC
  rw [encodedC] at pub
  rw [flagD] at status bytes
  have masked := written_mask32 (hasZero (bs 3)) pub status bytes
  have definition : Spec.RsaPkcs1Enc.encrypt (bs 0) (bs 1) (bs 2) (bs 3) =
      if hasZero (bs 3) then none else Spec.Rsa.publicOpChecked (bs 0) (bs 1) (Spec.RsaPkcs1Enc.encode (bs 2) (bs 3)) := by
    have nl : (bs 0).length = g.length := (h.sources 0).length
    have ml : (bs 2).length = g.messageLength := (h.sources 2).length
    have pl : (bs 3).length = g.paddingLength := (h.sources 3).length
    unfold Spec.RsaPkcs1Enc.encrypt
    rw [nl, ml, pl, nonzero_padding]
    cases z : hasZero (bs 3) <;> simp [h.valid.messageFits, h.valid.padding]
  rw [definition]
  exact masked

end VG.Proof.RsaPkcs1Enc.X86.Enc
