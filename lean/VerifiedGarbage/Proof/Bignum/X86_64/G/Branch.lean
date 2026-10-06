import VerifiedGarbage.Proof.Bignum.X86_64.G.Comp
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaBranch

/-!
# RSA with AVX512_IFMA on x86-64, any size: the IFMA branch

`IfmaBranch` for `CrtIfmaG`: from the checks (`CrtReady`) of a modulus of
`2 W` words and primes of `W`, `pre`, `ifma` and `post` leave what `qPart`
and `pPart` leave (`PDone`), and MXCSR's bits 15:0.
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfmaG
open VG.Proof.Bignum.X86_64 (NSafe nsafe_word above_nsafe preRanges_nsafe APost exists_mont')

variable {l : VG.Impl.Rsa.X86_64.CrtIfmaG.Lay}

/-- After `pre` and `ifma`: `q`'s result `C^dq mod q` and `p`'s `C^dp R_p`. -/
structure IDone (l : VG.Impl.Rsa.X86_64.CrtIfmaG.Lay) (s t : State) (B : Addr) (Z w op oq a : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (dpp dqp qip : Addr) (pl ql : Nat) (dpb dqb : List Byte) (Mk : Bool) : Prop where
  good : VG.Proof.Bignum.X86_64.Good t B Z w minv
  nv : NVals t B w minv N
  msk : word t.mem B (8 * Public.sMask) = mask Mk
  im : IMem l t.mem B w op oq a minv mp mq (mask Mk) (if Mk then P else 3) (if Mk then Q else 3) dpp dqp pl ql
  qlt : wv t.mem (off B oq) (slot l.W Public.aY) l.W < if Mk then Q else 3
  qval : Mk = true → wv t.mem (off B oq) (slot l.W Public.aY) l.W = C ^ Spec.Rsa.os2ip dqb % Q
  plt : wv t.mem (off B op) (slot l.W Public.aY) l.W < if Mk then P else 3
  pval : Mk = true → wv t.mem (off B op) (slot l.W Public.aY) l.W % P = C ^ Spec.Rsa.os2ip dpb * 2 ^ (64 * l.W) % P
  qi : word t.mem B (8 * sQinv) = qip
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

theorem ifmaR_ge {op oq a : Nat} (hpq : op ≤ oq) (hqa : oq ≤ a) : ∀ r ∈ ifmaR l op oq a, op ≤ r.1 := by
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

/-- `ifma`, after `pre`. -/
theorem branchA2_ok (hl : LayOk l) {s t₀ s₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hZa : offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W + 2 * l.D + 8 ≤ Z)
    (hA : APost t₀ s₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) l.W minv mp mq
      (Spec.Rsa.os2ip nb) (if Mk then Spec.Rsa.os2ip pb else 3) (if Mk then Spec.Rsa.os2ip qb else 3)
      (Spec.Rsa.os2ip xb)) :
    WP isa (seqs (ifma l)) s₁ fun t =>
      IDone l s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
      t.mxcsr = s₁.mxcsr &&& 0xFFFF := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hEW : l.E = 8 * l.W := rfl
  have hpl' : pl ≤ l.E := by unfold wsWords at hpl; omega
  have hql' : ql ≤ l.E := by unfold wsWords at hql; omega
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + tabBytes l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  have hh₀ : ∀ i < 32, hFixed i = true → word t₀.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  obtain ⟨hg₁, hN₁, rp, rq, f₁, k₁, mk₁⟩ := hA
  have ns₁ := preRanges_nsafe (w := (k + 7) / 8) (wp := l.W) (wq := l.W) (le_refl (offP ((k + 7) / 8)))
    (show slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl by rw [hoq]; omega)
  have hz : slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hpr : ∀ r ∈ preRanges ((k + 7) / 8) (offP ((k + 7) / 8)) l.W (offQ ((k + 7) / 8) pl) l.W,
      r.1 + r.2 ≤ offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W := fun r hr => by
    simp only [preRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | rfl | rfl | rfl
    · have := (gRanges_lt _ r hr).2; rw [hoq]; omega
    · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); rw [hoq]; simp only; omega
    · simp only [xRange]; omega
    · simp only [xRange]; rw [hoq, hop]; omega
  have i₀₁ : InScr B Z t₀.mem s₁.mem := InScr.of_frm f₁ fun r hr => by have := hpr r hr; omega
  have hb₁ : ∀ i < 32, i ≠ Crt.sD → i ≠ Public.sCnt → word s₁.mem B (8 * i) = word t₀.mem B (8 * i) :=
    fun i hi h1 h2 => nsafe_word f₁ ns₁ hi h1 h2
  have hf₁ : ∀ i < 32, hFixed i = true → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hf => by
    have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
    have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
    rw [hb₁ i hi h1 h2, hh₀ i hi hf]
  have kk₁ := hr.keep.trans k₁
  have ip : IPre l s₁.mem B ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) minv mp mq (mask Mk)
      (if Mk then P else 3) (if Mk then Q else 3) dpp dqp dpb.length dqb.length :=
    ⟨hg₁.hdr, by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP,
      by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ, rp.ws, rq.ws, rp.x.n, rp.x.inv, rp.x.one,
      rq.x.n, rq.x.inv, rq.x.one, mk₁.trans hr.pmask, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDp,
      by rw [hf₁ _ (by decide) (by decide), h.dpl]; exact h.hPl, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDq,
      by rw [hf₁ _ (by decide) (by decide), h.dql]; exact h.hQl⟩
  -- `ifma`.
  refine WP.mono (ifma_ok hl (K := (if Mk then P else 3) ∣ N ∧ (if Mk then Q else 3) ∣ N) (wp := l.W) hg₁.scr hg₁.rdi
    ip (le_refl _) (by rw [hoq, hop]) rfl (by omega) rfl hP'.2 hQ'.2 rp.ylt rq.ylt rp.clt rq.clt
    (fun hK => rp.cv hK.1) (fun hK => rq.cv hK.2) (fun hK => rp.yv hK.1) (fun hK => rq.yv hK.2)
    (h.dp.congrK (hr.iscr.trans i₀₁) kk₁) (h.dq.congrK (hr.iscr.trans i₀₁) kk₁) (by rw [h.dpl]; exact hpl1)
    (by rw [h.dpl]; exact hpl') (by rw [h.dql]; exact hql1) (by rw [h.dql]; exact hql'))
    fun t ⟨m₂, qlt, qv, plt, pv, f₂, d₂, k₂, mx₂⟩ => ?_
  have hge : ∀ r ∈ [(offP ((k + 7) / 8) + 8 * sIfma, 8), (offQ ((k + 7) / 8) pl + 8 * sIfma, 8)] ++
      ifmaR l (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) (offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W),
      offP ((k + 7) / 8) ≤ r.1 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; omega
      · simp only; rw [hoq, hop]; omega
    · exact ifmaR_ge (by rw [hoq, hop]; omega) (by omega) r hr
  have hlZ : ∀ r ∈ [(offP ((k + 7) / 8) + 8 * sIfma, 8), (offQ ((k + 7) / 8) pl + 8 * sIfma, 8)] ++
      ifmaR l (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) (offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W),
      r.1 + r.2 ≤ Z := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hZa' := hZa
      rw [hoq] at hZa'
      rcases hr with rfl | rfl
      · simp only [sIfma, sFn]; rw [hop]; omega
      · simp only [sIfma, sFn]; rw [hoq]; omega
    · have := ifmaR_le (by rw [hoq, hop]) (le_refl _) r hr; omega
  have hb₂ : ∀ d, d + 8 ≤ offP ((k + 7) / 8) → word t.mem B d = word s₁.mem B d := fun d hd =>
    word_below_frm f₂ hge hd (by omega)
  have hMK : Mk = true → (if Mk then P else 3) ∣ N ∧ (if Mk then Q else 3) ∣ N := fun hm => by
    obtain ⟨_, hpq, _⟩ := hMk' hm
    simp only [hm, ↓reduceIte]
    exact ⟨⟨Q, hpq.symm⟩, ⟨P, by rw [← hpq, Nat.mul_comm]⟩⟩
  rw [h.dpl, h.dql] at m₂
  refine ⟨⟨⟨hg₁.scr.congr k₂.2.2, d₂, m₂.nh⟩, hN₁.of_nsafe f₂ (above_nsafe (le_refl _) hge) hz (by omega),
    by rw [hb₂ _ (by unfold Public.sMask sFn; omega), hb₁ _ (by decide) (by decide) (by decide)]; exact hr.msk,
    m₂, qlt, fun hm => ?_, plt, fun hm => ?_,
    by rw [hb₂ _ (by unfold sQinv sFn; omega), hf₁ _ (by decide) (by decide)]; exact h.hQi,
    fun i hi hf => by rw [hb₂ _ (by have := hdr_lt_slot ((k + 7) / 8) 8 hi; omega), hf₁ i hi hf],
    (hr.iscr.trans i₀₁).trans (InScr.of_frm f₂ hlZ), (kk₁.trans k₂).mono (by simp [mmRegs])⟩,
    mx₂⟩
  · have := qv (hMK hm); simp only [hm, ↓reduceIte] at this; exact this
  · have := pv (hMK hm); simp only [hm, ↓reduceIte] at this; exact this


/-- `pre` and `ifma`, from the checks. -/
theorem branchA_ok (hl : LayOk l) (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hZa : offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W + 2 * l.D + 8 ≤ Z)
    (hpre : (seqs (CrtIfmaG.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfmaG.pre M.mm ++ ifma l)) t₀ fun t =>
      IDone l s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
      t.mxcsr = t₀.mxcsr &&& 0xFFFF := by
  have hA2 := fun s₁ => branchA2_ok hl (s₁ := s₁) h hv hr hMk hw32 hpl hql hZa
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hr.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hT : tabBytes l.W = 128 * (l.W + 2) := by unfold tabBytes; omega
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨hDb1, hDb2⟩ := hl.D_bounds
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hEW : l.E = 8 * l.W := rfl
  have hpl' : pl ≤ l.E := by unfold wsWords at hpl; omega
  have hql' : ql ≤ l.E := by unfold wsWords at hql; omega
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot l.W 8 + tabBytes l.W := by
    unfold offQ; rw [hpl]
  rw [hql] at hZq
  have pws := hr.pws
  have pxv := hr.pxv
  have qws := hr.qws
  have qxv := hr.qxv
  rw [hpl] at pws pxv
  rw [hql] at qws qxv
  have hh₀ : ∀ i < 32, hFixed i = true → word t₀.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  -- `pre`.
  refine wp_seqs_append (by simp [CrtIfmaG.pre, CrtIfmaG.prep]) (by simp [ifma]) (WP.mono_mx hpre
    (pre_ok M (wp := l.W) hr.good (by omega) (le_refl _) (by rw [hoq]) (by omega) (by omega)
      (by omega) hr.wsP hr.wsQ pws qws hr.nv hr.xm pxv hP'.1 hP'.2 qxv hQ'.1 hQ'.2)
    fun s₁ hA mx₁ => WP.mono (hA2 s₁ hA) fun t ⟨hd, mx⟩ =>
      ⟨hd, by rw [mx, mx₁]⟩)

/-- `post`, after `pre` and `ifma`: what `pPart` leaves. -/
theorem branchB_ok (hl : LayOk l) (M : Mont) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hd : IDone l s t₁ B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot l.W 8 + tabBytes l.W) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 2 * l.W) (hpl : wsWords pl = l.W) (hql : wsWords ql = l.W)
    (hpost : (seqs (CrtIfmaG.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfmaG.post M.mm)) t₁ fun t => PDone s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk ∧
      t.mxcsr = t₁.mxcsr := by
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  have hk1 := h.k1
  have hpl1 := h.pl1
  have hql1 := h.ql1
  have hZq := h.z
  have hqil := h.qil
  generalize Spec.Rsa.os2ip nb = N at *
  generalize Spec.Rsa.os2ip xb = C at *
  generalize Spec.Rsa.os2ip pb = P at *
  generalize Spec.Rsa.os2ip qb = Q at *
  generalize hQIe : Spec.Rsa.os2ip qib = QI at *
  obtain ⟨hMk', hP', hQ'⟩ := mask_facts hMk hodd hPN hQN
  have hn := hd.good.scr.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain ⟨hW1, hW2⟩ := W_bounds hl
  have hEW : l.E = 8 * l.W := rfl
  have hpl' : pl ≤ l.E := by unfold wsWords at hpl; omega
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot (wsWords pl) 8 + tabBytes (wsWords pl) := rfl
  have hW8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega
  have hm := hd.im
  -- The multiplier of `R_p` in `p`'s `aY`: `C^dp` for a key that passed the checks.
  obtain ⟨x0, hx0⟩ := exists_mont' (VG.Proof.Bignum.coprime_pow2 hP'.2 (64 * wsWords pl)) hP'.1
    (wv t₁.mem (off B (offP ((k + 7) / 8))) (slot (wsWords pl) Public.aY) (wsWords pl))
  refine WP.mono_mx hpost (post_ok M (wx := wsWords pl) (op := offP ((k + 7) / 8))
    (oq := offQ ((k + 7) / 8) pl) (mx := mp) (mq := mq) (X := if Mk then P else 3)
    (m1 := if Mk then C ^ Spec.Rsa.os2ip dpb else x0) (c := Mk) (qib := qib) hd.good (by omega) hd.nv
    (by rw [hpl]; omega) hm.wsQ (by rw [hpl]; exact hm.qws) (by have := hZq; rw [hql] at this; rw [hpl]; exact this)
    (le_refl _) (by rw [hoq, hop]) (by rw [hpl]; omega) hm.wsP
    (by rw [hpl]; exact hm.pws) (by rw [hpl]; exact ⟨hm.pn, hm.pinv, hm.pone⟩) hP'.1 hP'.2
    (by rw [hpl]; exact hd.plt) (fun _ => ?_) hm.pmk
    (fun hm' => by obtain ⟨_, hpq, _⟩ := hMk' hm'; simp only [hm', ↓reduceIte]; exact ⟨Q, hpq.symm⟩) hd.qi
    (by rw [hqil]; exact hm.pl) (h.qi.congrK hd.iscr hd.keep) (by rw [hqil]; exact hpl1) (by rw [hqil]; omega)
    (by rw [hqil, hpl]; omega)
    (fun hm' => by obtain ⟨_, _, hqi⟩ := hMk' hm'; simp only [hm', ↓reduceIte, hQIe]; exact hqi))
    fun t ⟨hg', hws', hX', hlt', hh', f', k'⟩ mx' => ?_
  · by_cases hmk : Mk
    · simp only [hmk, ↓reduceIte]
      rw [hpl]
      exact hd.pval hmk
    · simp only [hmk, Bool.false_eq_true, ↓reduceIte] at hx0 ⊢
      exact hx0
  have hz : slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have ns : NSafe ((k + 7) / 8) (gRanges ((k + 7) / 8) ++
      [(slot ((k + 7) / 8) Public.aX, 8 * ((k + 7) / 8 + 2)), xRange (offP ((k + 7) / 8)) (wsWords pl)]) :=
    fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact .inl hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (by simp only [xRange]; omega))
  have hqZ : offQ ((k + 7) / 8) pl + slot l.W 8 ≤ 2 ^ 64 := by
    have := hZq; rw [hql] at this; omega
  have h16 := hdr_lt_slot l.W 8 (show 31 < 32 by decide)
  have hqk : ∀ d, offQ ((k + 7) / 8) pl ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem B d = word t₁.mem B d :=
    fun d hd' hd'' => f'.word_eq (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact .inr (by have := (gRanges_lt _ r hr).2; rw [hoq] at hd'; omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); simp only; rw [hoq] at hd'; omega
        · simp only [xRange]; rw [hoq] at hd'; omega) hd''
  have hqv : ∀ d n, d + 8 * n ≤ slot l.W 8 → wv t.mem (off B (offQ ((k + 7) / 8) pl)) d n =
      wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) d n := fun d n hdn => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hqk _ (by omega) (by omega)
  have hY8 := slot_le (w := l.W) (show Public.aY < 8 by decide)
  have hN8 := slot_le (w := l.W) (show Public.aN < 8 by decide)
  refine ⟨⟨hg', by rw [nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hd.msk,
    by rw [nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hm.wsP,
    by rw [nsafe_word f' ns (by decide) (by decide) (by decide)]; exact hm.wsQ, hws',
    (show WsAt t₁.mem B (offQ ((k + 7) / 8) pl) (wsWords ql) mq by rw [hql]; exact hm.qws).of_words fun i hi => by
      rw [word_off, word_off]; exact hqk _ (by omega) (by omega),
    by rw [hql, hqv _ _ (by omega)]; exact hm.qn, by rw [hql, hqv _ _ (by omega)]; exact hd.qlt,
    fun hmk => by rw [hql, hqv _ _ (by omega)]; exact hd.qval hmk, hlt', fun hmk => ?_,
    hd.hfix.trans fun i hi hf => by
      have h1 : i ≠ Crt.sD := by rintro rfl; revert hf; decide
      have h2 : i ≠ Public.sCnt := by rintro rfl; revert hf; decide
      exact nsafe_word f' ns hi h1 h2,
    hd.iscr.trans (InScr.of_frm f' fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · have := (gRanges_lt _ r hr).2; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); simp only; omega
        · simp only [xRange]; rw [hoq] at hZq; rw [hop]; omega),
    (hd.keep.trans k').mono (by simp [mmRegs])⟩, mx'⟩
  obtain ⟨a, b, ha, hb, hbP, hh⟩ := hh' hmk
  simp only [hmk, ↓reduceIte] at ha hb hbP hh
  rw [show wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) (slot (wsWords pl) Public.aY) (wsWords pl) =
    wv t₁.mem (off B (offQ ((k + 7) / 8) pl)) (slot l.W Public.aY) l.W by rw [hpl], hd.qval hmk] at hb
  exact ⟨a, b, ha, hb, hbP, by rw [hh, hQIe]⟩

end VG.Proof.Bignum.X86_64.G
