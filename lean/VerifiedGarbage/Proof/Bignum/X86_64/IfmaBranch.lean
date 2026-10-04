import VerifiedGarbage.Proof.Bignum.X86_64.IfmaPost
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import Mathlib.Data.Int.GCD

/-!
# RSA with AVX512_IFMA on x86-64: the IFMA branch

`ifmaBranch_ok`: from the checks (`CrtReady`) of a modulus of 32 words and
primes of 16, `pre`, `ifma` and `post` leave what `qPart` and `pPart` leave
(`PDone`), and MXCSR's bits 15:0.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (D sIfma)

/-- Ranges that keep `n`'s values and header but `aAcc`, `aTmp`, `aY`, `aX`,
`sD` and `sCnt`: those of `gRanges`, `aX`, and anything above `n`'s arrays. -/
def NSafe (w : Nat) (rs : List (Nat × Nat)) : Prop :=
  ∀ r ∈ rs, r ∈ gRanges w ∨ r = (slot w Public.aX, 8 * (w + 2)) ∨ slot w 8 ≤ r.1

theorem NSafe.append {w : Nat} {rs rs' : List (Nat × Nat)} (h : NSafe w rs) (h' : NSafe w rs') :
    NSafe w (rs ++ rs') := fun r hr => (List.mem_append.mp hr).elim (h r) (h' r)

theorem nsafe_wv {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : NSafe w rs) {j : Nat} (hj : j < 8) (h1 : j ≠ Public.aAcc) (h2 : j ≠ Public.aTmp) (h3 : j ≠ Public.aY)
    (h4 : j ≠ Public.aX) (hz : slot w 8 ≤ 2 ^ 64) : wv m' B (slot w j) w = wv m B (slot w j) w := by
  have := slot_le (w := w) hj
  refine hf.wv_eq (fun r hr' => ?_) (by omega)
  rcases hr r hr' with h | h | h
  · have := slot_sep (w := w) h1
    have := slot_sep (w := w) h2
    have := slot_sep (w := w) h3
    have := hdr_lt_slot w j (show Crt.sD < 32 by decide)
    have := hdr_lt_slot w j (show Public.sCnt < 32 by decide)
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp only [Crt.sD, Public.sCnt, sFn] at * <;> omega
  · subst h; have := slot_sep (w := w) h4; simp only; omega
  · exact .inl (by omega)

theorem nsafe_word {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : NSafe w rs) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD) (h2 : i ≠ Public.sCnt) :
    word m' B (8 * i) = word m B (8 * i) := by
  have := hdr_lt_slot w 8 hi
  refine hf.word_eq (fun r hr' => ?_) (by omega)
  rcases hr r hr' with h | h | h
  · have := hdr_lt_slot w Public.aAcc hi
    have := hdr_lt_slot w Public.aTmp hi
    have := hdr_lt_slot w Public.aY hi
    simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact .inl (by omega)
    · exact .inl (by omega)
    · exact .inl (by omega)
    · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
      unfold Crt.sD sFn at h1 ⊢; omega
    · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
      unfold Public.sCnt sFn at h2 ⊢; omega
  · subst h; have := hdr_lt_slot w Public.aX hi; exact .inl (by simp only; omega)
  · exact .inl (by omega)

theorem NVals.of_nsafe {s t : State} {B : Addr} {w : Nat} {minv : BitVec 64} {N : Nat} (h : NVals s B w minv N)
    {rs : List (Nat × Nat)} (hf : Frm B rs s.mem t.mem) (hr : NSafe w rs) (hz : slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) :
    NVals t B w minv N := by
  have lN := slot_le (w := w) (show Public.aN < 8 by decide)
  have hN0 := hdr_lt_slot w Public.aN (show 31 < 32 by decide)
  have e := fun {j} (hj : j < 8) h1 h2 h3 h4 => nsafe_wv (j := j) hf hr hj h1 h2 h3 h4 hz
  refine ⟨by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.n, ?_,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.r2,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.r2lt,
    by rw [e (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.one⟩
  have := (wv_mod64 t.mem B (slot w Public.aN) (n := w) hw).symm
  rw [this, e (by decide) (by decide) (by decide) (by decide) (by decide), wv_mod64 s.mem B (slot w Public.aN) hw]
  exact h.inv

/-- After `pre` and `ifma`: `q`'s result `C^dq mod q` and `p`'s `C^dp R_p`. -/
structure IDone (s t : State) (B : Addr) (Z w op oq a : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (dpp dqp qip : Addr) (pl ql : Nat) (dpb dqb : List Byte) (Mk : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xl : wv t.mem B (slot w Public.aX) w < N
  xv : wv t.mem B (slot w Public.aX) w % N = 2 ^ (64 * 16 * (nChunks w 16 + 1)) % N
  msk : word t.mem B (8 * Public.sMask) = mask Mk
  im : IMem t.mem B w op oq a minv mp mq (mask Mk) (if Mk then P else 3) (if Mk then Q else 3) dpp dqp pl ql
  qlt : wv t.mem (off B oq) (slot 16 Public.aY) 16 < if Mk then Q else 3
  qval : Mk = true → wv t.mem (off B oq) (slot 16 Public.aY) 16 = C ^ Spec.Rsa.os2ip dqb % Q
  plt : wv t.mem (off B op) (slot 16 Public.aY) 16 < if Mk then P else 3
  pval : Mk = true → wv t.mem (off B op) (slot 16 Public.aY) 16 % P = C ^ Spec.Rsa.os2ip dpb * 2 ^ (64 * 16) % P
  qi : word t.mem B (8 * sQinv) = qip
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

theorem preRanges_nsafe {w op wp oq wq : Nat} (hp : slot w 8 ≤ op) (hq : slot w 8 ≤ oq) :
    NSafe w (preRanges w op wp oq wq) := fun r hr => by
  simp only [preRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | rfl | rfl | rfl
  · exact .inl hr
  · exact .inr (.inl rfl)
  · exact .inr (.inr (by simp only [xRange]; omega))
  · exact .inr (.inr (by simp only [xRange]; omega))

theorem above_nsafe {w L : Nat} {rs : List (Nat × Nat)} (hL : slot w 8 ≤ L) (hr : ∀ r ∈ rs, L ≤ r.1) :
    NSafe w rs := fun r h => .inr (.inr (by have := hr r h; omega))

theorem ifmaR_ge {op oq a : Nat} (hpq : op ≤ oq) (hqa : oq ≤ a) : ∀ r ∈ ifmaR op oq a, op ≤ r.1 := by
  simp only [ifmaR, shiftRanges, k1Ranges, resRanges, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only <;> omega

/-- `pre` and `ifma`, from the checks. -/
theorem branchA_ok (M : Mont) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hw32 : (k + 7) / 8 = 32) (hpl : wsWords pl = 16) (hql : wsWords ql = 16)
    (hZa : offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16 + 2 * D + 8 ≤ Z)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (CrtIfma.pre M.mm ++ CrtIfma.ifma)) t₀ fun t =>
      IDone s t B Z ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl)
        (offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16) minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dpp dqp qip pl ql dpb dqb Mk ∧
      t.mxcsr = t₀.mxcsr &&& 0xFFFF := by
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
  have h16 := hdr_lt_slot 16 8 (show 31 < 32 by decide)
  have hT : tabBytes 16 = 2304 := rfl
  have hD : D = 3712 := rfl
  have hpl' : pl ≤ 128 := by unfold wsWords at hpl; omega
  have hql' : ql ≤ 128 := by unfold wsWords at hql; omega
  have hop : offP ((k + 7) / 8) = slot ((k + 7) / 8) 8 := rfl
  have hoq : offQ ((k + 7) / 8) pl = slot ((k + 7) / 8) 8 + slot 16 8 + tabBytes 16 := by
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
  refine wp_seqs_append (by simp [CrtIfma.pre, Crt.gPow]) (by simp [CrtIfma.ifma]) (WP.mono_mx hpre
    (pre_ok M (wp := 16) hr.good (by omega) (by omega) (le_refl _) (by rw [hoq]) (by omega) (by decide)
      (by omega) hr.wsP hr.wsQ pws qws hr.nv hodd hN1 hr.xm pxv hP'.1 hP'.2 qxv hQ'.1 hQ'.2)
    fun s₁ ⟨hg₁, hN₁, rp, rq, hXl, hXv, f₁, k₁, mk₁⟩ mx₁ => ?_)
  have ns₁ := preRanges_nsafe (w := (k + 7) / 8) (wp := 16) (wq := 16) (le_refl (offP ((k + 7) / 8)))
    (show slot ((k + 7) / 8) 8 ≤ offQ ((k + 7) / 8) pl by rw [hoq]; omega)
  have hz : slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hpr : ∀ r ∈ preRanges ((k + 7) / 8) (offP ((k + 7) / 8)) 16 (offQ ((k + 7) / 8) pl) 16,
      r.1 + r.2 ≤ offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16 := fun r hr => by
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
  have ip : IPre s₁.mem B ((k + 7) / 8) (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) minv mp mq (mask Mk)
      (if Mk then P else 3) (if Mk then Q else 3) dpp dqp dpb.length dqb.length :=
    ⟨hg₁.hdr, by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsP,
      by rw [hb₁ _ (by decide) (by decide) (by decide)]; exact hr.wsQ, rp.ws, rq.ws, rp.x.n, rp.x.inv, rp.x.one,
      rq.x.n, rq.x.inv, rq.x.one, mk₁.trans hr.pmask, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDp,
      by rw [hf₁ _ (by decide) (by decide), h.dpl]; exact h.hPl, by rw [hf₁ _ (by decide) (by decide)]; exact h.hDq,
      by rw [hf₁ _ (by decide) (by decide), h.dql]; exact h.hQl⟩
  -- `ifma`.
  refine WP.mono (ifma_ok (K := (if Mk then P else 3) ∣ N ∧ (if Mk then Q else 3) ∣ N) (wp := 16) hg₁.scr hg₁.rdi
    ip (le_refl _) (by rw [hoq, hop]) rfl (by omega) rfl hP'.2 hQ'.2 rp.ylt rq.ylt rp.clt rq.clt
    (fun hK => rp.cv hK.1) (fun hK => rq.cv hK.2) (fun hK => rp.yv hK.1) (fun hK => rq.yv hK.2)
    (h.dp.congrK (hr.iscr.trans i₀₁) kk₁) (h.dq.congrK (hr.iscr.trans i₀₁) kk₁) (by rw [h.dpl]; exact hpl1)
    (by rw [h.dpl]; exact hpl') (by rw [h.dql]; exact hql1) (by rw [h.dql]; exact hql'))
    fun t ⟨m₂, qlt, qv, plt, pv, f₂, d₂, k₂, mx₂⟩ => ?_
  have hge : ∀ r ∈ [(offP ((k + 7) / 8) + 8 * sIfma, 8), (offQ ((k + 7) / 8) pl + 8 * sIfma, 8)] ++
      ifmaR (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) (offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16),
      offP ((k + 7) / 8) ≤ r.1 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; omega
      · simp only; rw [hoq, hop]; omega
    · exact ifmaR_ge (by rw [hoq, hop]; omega) (by omega) r hr
  have hlZ : ∀ r ∈ [(offP ((k + 7) / 8) + 8 * sIfma, 8), (offQ ((k + 7) / 8) pl + 8 * sIfma, 8)] ++
      ifmaR (offP ((k + 7) / 8)) (offQ ((k + 7) / 8) pl) (offQ ((k + 7) / 8) pl + slot 16 8 + tabBytes 16),
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
    by rw [wv_below_frm f₂ hge (by have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); omega)
      (by omega)]; exact hXl,
    by rw [wv_below_frm f₂ hge (by have := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide); omega)
      (by omega)]; exact hXv,
    by rw [hb₂ _ (by unfold Public.sMask sFn; omega), hb₁ _ (by decide) (by decide) (by decide)]; exact hr.msk,
    m₂, qlt, fun hm => ?_, plt, fun hm => ?_,
    by rw [hb₂ _ (by unfold sQinv sFn; omega), hf₁ _ (by decide) (by decide)]; exact h.hQi,
    fun i hi hf => by rw [hb₂ _ (by have := hdr_lt_slot ((k + 7) / 8) 8 hi; omega), hf₁ i hi hf],
    (hr.iscr.trans i₀₁).trans (InScr.of_frm f₂ hlZ), (kk₁.trans k₂).mono (by simp [mmRegs])⟩,
    by rw [mx₂, mx₁]⟩
  · have := qv (hMK hm); simp only [hm, ↓reduceIte] at this; exact this
  · have := pv (hMK hm); simp only [hm, ↓reduceIte] at this; exact this

end VG.Proof.Bignum.X86_64
