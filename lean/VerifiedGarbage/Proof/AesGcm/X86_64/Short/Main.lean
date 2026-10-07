import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Cond

/-!
# AES-GCM's short path on x86-64: `seal` and `open`

Untrusted: everything here is checked by Lean. After the entry, `cond`
chooses the short path (`IsShort`) or the other instances' body: `seal`
leaves what `sealRun_ok` does either way (`sealShort_ok`), and `open`, for a
tag length it allows, what `openOk_ok` does (`openShort_ok`), so the rest of
`sealM_wp`'s and `openM_wp`'s proofs applies (`sealM_of`, `openM_of`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph gctr inc32)

/-- What `cond` reads, after the entry. -/
theorem condS_of {s₀ s₁ : State} {Ctx W SP A D : Addr} {nl al n : Nat} (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) : CondS W nl al n s₁ :=
  ⟨E.env.r15, E.env.perm.w, by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.len⟩

/-- `cond` after the entry: ZF clear iff the short path applies, and the
entry kept. -/
theorem condE_ok {k : Nat} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) :
    WP isa Impl.AesGcm.X86_64.Short.cond s₁ fun s₂ => s₂.zf = some (decide ¬IsShort nl al n) ∧
      OneEntry s₀ Ctx W SP A D n s₂ ∧ CondKeep s₁ s₂ := by
  have hlt := C.data.ok.lt
  refine WP.mono (cond_ok (condS_of E hnl hal) (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _)
    (by omega)) fun s₂ ⟨hz, K⟩ => ⟨hz, ?_, K⟩
  exact E.keep C.lay (fun r hr => K.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) K.rd K.wr (by rw [K.mem]; exact Frame.refl _ _)

/-- `seal` after the entry: `cond`, then the short path or the other
instances' body, which leave the same. -/
theorem sealMid_ok (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s s₁ : State}
    {Ctx W SP Np A D : Addr} {nl al n : Nat} (C : OneCtx s 4 Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s) (E : OneEntry s Ctx W SP A D n s₁)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = nl) (hal : (s.gpr .r9).toNat = al) :
    WP isa (.seq Impl.AesGcm.X86_64.Short.cond (.ite .e
        (.seq (oneAad v.callees) (.seq (oneBlocks B.enc) (.seq (oneCrypt v.callees) (oneTag v.callees 0))))
        Impl.AesGcm.X86_64.Short.sealShort)) s₁
      (SealRunPost s Ctx W SP Np A D nl al n) :=
  WP.seq (WP.mono (condE_ok C E hnl hal) fun _ ⟨hz, E₂, _⟩ =>
    WP.ite (decide ¬IsShort _ _ _) (eval_e hz) (fun _ => sealRun_ok v B C X E₂ hNp hnl hal) fun h => by
      have h' := Decidable.not_not.mp (of_decide_eq_false h)
      exact sealShort_ok hF C E₂ hNp hnl hal h'.1 h'.2.1 h'.2.2.1 h'.2.2.2)

/-- `vg_aes_gcm_seal` with the short path, for a key context of kind `M`. -/
theorem sealM_wp (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' :=
  sealM_of hp (sealMid_ok hF v B)

/-- `vg_aes_gcm_open` with the short path, for a key context of kind `M`. -/
theorem openM_wp (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  refine openM_of hp fun {Ctx W SP Np A D T nl al n t _ _} C X E hNp hnl hal _ hTa hTar hTr oT oA htl hok =>
    WP.seq (WP.mono (condE_ok C E hnl hal) fun s₂ ⟨hz, E₂, K⟩ => ?_)
  rw [← K.mem] at htl
  refine WP.ite (decide ¬IsShort _ _ _) (eval_e hz)
    (fun _ => openOk_ok v B C X E₂ hNp hnl hal hTa hTar hTr oT oA htl hok) fun h => ?_
  have h' := Decidable.not_not.mp (of_decide_eq_false h)
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  refine WP.mono (openShort_ok hF C E₂ hNp hnl hal h'.1 h'.2.1 h'.2.2.1 h'.2.2.2 htl hb.1 hb.2 hTa hTar hTr oT oA)
    fun s' ⟨he, hsv, f, hax, hD⟩ => ⟨he, hsv, ?_, ?_⟩
  · rw [ret_kept f fun r hr => ?_]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact C.rW
    · exact C.rD
    · exact Offset.base_disjoint_below _ (n := 24) (k := 8) (by decide)
  · obtain ⟨rfl, -⟩ := h'
    simp only [OpenRes, Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq,
      length_bytesAt]
    by_cases e : (VG.Spec.Gcm.toBytes (VG.Spec.Gcm.ghashFrom (ctxH s.mem Ctx) (VG.Spec.Gcm.ghash (ctxH s.mem Ctx)
        (VG.Spec.Gcm.blocks (Proof.Gcm.padded (bytesAt s.mem A al) (bytesAt s.mem D n))))
        [VG.Spec.Gcm.ofBytes (Proof.Gcm.lensBlock al n)] ^^^
        ctxCiph s.mem Ctx (s.gpr .rsi).toNat (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np 12)))).take t =
        bytesAt s.mem T t
    · simp only [e, ↓reduceIte] at hax hD ⊢
      exact ⟨hax, hD⟩
    · simp only [e, ↓reduceIte] at hax hD ⊢
      exact ⟨hax, hD⟩

end VG.Proof.AesGcm.X86_64.Short
