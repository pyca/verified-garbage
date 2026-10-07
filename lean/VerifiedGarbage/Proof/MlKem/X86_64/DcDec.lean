import VerifiedGarbage.Proof.MlKem.X86_64.DcBase

/-!
# ML-KEM on x86-64: decapsulation, K-PKE.Decrypt

`u'[i]` (`u_ok`), `ŝ[i]` (`s_ok`), and `m' = ByteEncode₁(Compress₁(v' -
NTT⁻¹(ŝ^⊺ ∘ NTT(u'))))` to `M`, the product in one call of
`vg_mlkem*_decrypt_mul` (`tail_ok`): `m' = K-PKE.Decrypt(dk_PKE, c)`. Between
the steps, `DR nu ns`: the first `nu` of `u'` and `ns` of `ŝ` are done. Each
with its constant time.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (decapsK L).pre (decapsK L).pub I

theorem dc_lrel {L : Kem} (W : DcWf L) {σ₁ σ₂ x y : State} (p₁ : (decapsK L).pre σ₁) (p₂ : (decapsK L).pre σ₂)
    (pub : (decapsK L).pub σ₁ σ₂) (h₁ : DC L σ₁ x) (h₂ : DC L σ₂ y) : LRel (dcR L) (dcW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.r14, .rsi) (by decide), h₂.top.regs (.r14, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]

/-- The steps of K-PKE.Decrypt. -/
structure DR (L : Kem) (nu ns : Nat) (σ s : State) : Prop where
  dc : DC L σ s
  r15 : s.gpr .r15 = 1
  u : ∀ i < nu, PolyIs s.mem (pa s (pS i)) (KPke.dcU L.p (dcC L σ) i)
  sh : ∀ i < ns, PolyIs s.mem (pa s (pS (L.k + i))) (dcS (KPke.dkPke L.p (dcDk L σ)) i)

theorem DR.keep {L : Kem} (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ) {nu ns : Nat} {s s' : State}
    (h : DR L nu ns σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : drChk L nu ns ws = true) :
    DR L nu ns σ s' := by
  simp only [drChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hdc, kU⟩, kS⟩ := hc
  have L₀ := h.dc.lay W hp
  exact ⟨h.dc.step W hp hP.b hdc, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun i hi => L₀.keepPoly hP.b (kU i hi) (h.u i hi), fun i hi => L₀.keepPoly hP.b (kS i hi) (h.sh i hi)⟩

theorem DR.zero {L : Kem} {σ s : State} (h : DC L σ s) (h15 : s.gpr .r15 = 1) : DR L 0 0 σ s :=
  ⟨h, h15, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- `32 d_u (i + 1) ≤ |c|`. -/
theorem uSlice_le (L : Kem) {i : Nat} (hi : i < L.k) : 32 * L.du * i + 32 * L.du ≤ L.ctLen := by
  have : 32 * L.du * (i + 1) ≤ 32 * L.du * L.k := Nat.mul_le_mul_left _ hi
  simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.k] at this ⊢
  rw [Nat.mul_succ] at this
  rw [Nat.mul_add, ← Nat.mul_assoc]
  omega

/-! ## `u'` -/

theorem u_ok {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) {σ : State}
    (hp : (decapsK L).pre σ) {i : Nat} (hi : i < L.k) {s : State} (h : DR L i 0 σ s) :
    WP isa (uHat L i) s (DR L (i + 1) 0 σ) := by
  have hc := W.u i hi
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨hdd, hrc⟩ := hc
  have L₀ := h.dc.lay W hp
  unfold uHat
  refine WP.mono (ddCall_okL K.dd L₀ (d := L.du) rbx_na hdd K.du.2) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  have hk := h.keep W hp hP₁ hrc
  refine ⟨hk.dc, hk.r15, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < i ∨ k = i) with hk' | rfl
  · exact hk.u k hk'
  · rw [← hP₁.pa rbx_cs, slice_of h.dc.c (uSlice_le L hi)] at hp₁
    exact hp₁

theorem u_tr {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) {i : Nat}
    (hi : i < L.k) : RelCT isa (R L (DR L i 0)) (uHat L i) fun _ _ => True := by
  have hc := W.u i hi
  simp only [uChk, Bool.and_eq_true] at hc
  exact rel2_of (ddCall_trL K.dd (d := L.du) rbx_na hc.1 K.du.2)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

/-! ## `ŝ` -/

theorem s_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ) {i : Nat} (hi : i < L.k) {s : State}
    (h : DR L L.k i σ s) : WP isa (sHat L A i) s (DR L L.k (i + 1) σ) := by
  have hc := W.s i hi
  simp only [sChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W hp
  refine WP.mono (dec12At_okL hA L₀ rbx_na hc.1) fun s' ⟨hP, hq⟩ => ?_
  have hk := h.keep W hp hP hc.2
  refine ⟨hk.dc, hk.r15, hk.u, fun k hk' => ?_⟩
  rcases (by omega : k < i ∨ k = i) with hk' | rfl
  · exact hk.sh k hk'
  · rw [hP.pa rbx_cs]
    rw [slice_of h.dc.dk (show 384 * k + 384 ≤ L.dkLen by simp only [Kem.dkLen, Params.dkLen, Kem.k] at hi ⊢; omega)]
      at hq
    rw [dcS, KPke.dkPke, slice_take _ (show 384 * k + 384 ≤ 384 * L.p.k by simp only [Kem.k] at hi; omega)]
    exact hq

theorem s_tr {A : Arith} (hA : ArithOk A) {L : Kem} (W : DcWf L) {i : Nat} (hi : i < L.k) :
    RelCT isa (R L (DR L L.k i)) (sHat L A i) fun _ _ => True := by
  have hc := W.s i hi
  simp only [sChk, Bool.and_eq_true] at hc
  exact rel2_of (dec12At_trL hA rbx_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

/-! ## `m'` -/

/-- After K-PKE.Decrypt: `m'` at `M`. -/
structure DM (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  r15 : s.gpr .r15 = 1
  m : bytesAt s.mem (pa s (sc oM)) 32 = KPke.decM L.p (dcDk L σ) (dcC L σ)

/-- The rest of `decrypt`. -/
abbrev tail (L : Kem) (A : Arith) : Prog isa :=
  .seq (L.decMulAt A (pS 15) (pS L.k) (pS 0) (pS (2 * L.k)))
    (.seq (L.ddAt (.r14, 32 * L.du * L.k) L.dv (pS 16)) (.seq (subAt A (pS 16) (pS 15)) (ceAt (pS 16) 1 (sc oM))))

theorem tail_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd)
    {σ : State} (hp : (decapsK L).pre σ) {s : State} (h : DR L L.k L.k σ s) : WP isa (tail L A) s (DM L σ) := by
  have hc := W.tail
  simp only [tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hdm, hdd⟩, hk15⟩, hac⟩, htw⟩, hkc⟩, hk₁⟩ := hc
  have L₀ := h.dc.lay W hp
  refine WP.seq (WP.mono (decMulAt_okL hA W.k34 L₀ rbx_na rbx_na rbx_na hdm
    (vecReduced_pS fun i hi => (h.sh i hi).1) (vecReduced_pS fun i hi => by rw [Nat.zero_add]; exact (h.u i hi).1))
    fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have e1 : vecAt s.mem (pa s (pS L.k)) L.k = (List.range L.k).map (dcS (KPke.dkPke L.p (dcDk L σ))) := by
    rw [vecAt_pS]; exact List.map_congr_left fun i hi => (h.sh i (List.mem_range.mp hi)).2
  have e2 : (vecAt s.mem (pa s (pS 0)) L.k).map ntt =
      (List.range L.k).map fun i => ntt (KPke.dcU L.p (dcC L σ) i) := by
    rw [vecAt_pS, List.map_map]
    exact List.map_congr_left fun i hi => by
      simp only [Function.comp, Nat.zero_add]; rw [(h.u i (List.mem_range.mp hi)).2]
  rw [e1, e2, KPke.dot_eq_dotK, ← hP₁.pa rbx_cs] at hp₁
  have L₁ := L₀.post hP₁.b (dcB_bases L)
  refine WP.seq (WP.mono (ddCall_okL K.dd L₁ (d := L.dv) rbx_na hdd K.dv.2) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b (dcB_bases L)
  have hc₂ : bytesAt s₁.mem (pa s₁ (.r14, 32 * L.du * L.k)) (32 * L.dv) =
      ((dcC L σ).drop (32 * L.du * L.k)).take (32 * L.dv) := by
    have k₁ := h.dc.step W hp hP₁.b hk₁
    exact slice_of k₁.c (by simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, ← Nat.mul_assoc])
  rw [hc₂, ← hP₂.pa rbx_cs] at hp₂
  have hq₂ := L₁.keepPoly hP₂.b hk15 hp₁
  refine WP.seq (WP.mono (subAt_ok hA L₂ rbx_na hac hp₂.1 hq₂.1) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b (dcB_bases L)
  rw [hp₂.2, hq₂.2, ← hP₃.pa rbx_cs] at hp₃
  refine WP.mono (ceCall_okL ceImpl L₃ (d := 1) rbx_na htw (by decide) hp₃.1) fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have hP := PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)
  refine ⟨h.dc.step W hp hP.b hkc, ?_, ?_⟩
  · rw [hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]
  · rw [hP₄.pa rbx_cs, hb₄, hp₃.2, KPke.decM, KPke.kpkeDecrypt_eq]
    rfl

theorem tail_tr {A : Arith} (hA : ArithOk A) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L (DR L L.k L.k)) (tail L A) fun _ _ => True := by
  have hc := W.tail
  simp only [tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hdm, hdd⟩, hk15⟩, hac⟩, htw⟩, _⟩, _⟩ := hc
  refine rel2_of (Q := fun x y => LRel (dcR L) (dcW L) x y ∧
      (VecReduced x.mem (pa x (pS L.k)) L.k ∧ VecReduced x.mem (pa x (pS 0)) L.k) ∧
      (VecReduced y.mem (pa y (pS L.k)) L.k ∧ VecReduced y.mem (pa y (pS 0)) L.k))
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) (dcB_bases L)
    (RelCT.mono (decMulAt_trL hA W.k34 rbx_na rbx_na rbx_na hdm) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (decMulAt_okL hA W.k34 Lx rbx_na rbx_na rbx_na hdm hx.1 hx.2)
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16)) ∧ Reduced x.mem (pa x (pS 15))) (dcB_bases L)
      (RelCT.mono (ddCall_trL K.dd (d := L.dv) rbx_na hdd K.dv.2) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddCall_okL K.dd Lx (d := L.dv) rbx_na hdd K.dv.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1, Lx.keepRed hP.b hk15 hx⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16))) (dcB_bases L) (subAt_tr hA rbx_na hac)
      (fun x Lx hx => WP.mono (subAt_ok hA Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL ceImpl (d := 1) rbx_na htw (by decide)))))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨dc_lrel W p₁ p₂ pub h₁.dc h₂.dc,
      ⟨vecReduced_pS fun i hi => (h₁.sh i hi).1, vecReduced_pS fun i hi => by rw [Nat.zero_add]; exact (h₁.u i hi).1⟩,
      ⟨vecReduced_pS fun i hi => (h₂.sh i hi).1, vecReduced_pS fun i hi => by rw [Nat.zero_add]; exact (h₂.u i hi).1⟩⟩

end Decaps

end VG.Proof.MlKem.X86_64
