import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseO

/-! Output packing depends on the signer layout, accepted response, challenge
bytes, and hints. It does not require canonical secret-transform storage. -/
namespace VG.Proof.MlDsa.AArch64.Sign.Output
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (D : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  k : St p D σ s
  z : Fam s (yBase p) p.ℓ (Zv p σ κ)
  h : HFam s 5 p.k (Hv p σ κ)
  sig : bytesAt s.mem (pa s (.x23, 0)) (cLen p + zLen p * r) = CTv p σ κ ++ zEnc p σ κ r
  x24 : s.gpr .x24 = 1

def ofam (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  stChk p ws && famChk (sgR p) (sgW p) ws (yBase p) p.ℓ && famChk (sgR p) (sgW p) ws 5 p.k

theorem OS.step {p : Params} {D : Nat} {σ s s' : State} {κ r : Nat} (h : OS p D σ κ r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : ofam p ws = true)
    (hs : keepB (sgR p) (sgW p) ws (.x23, 0) (cLen p + zLen p * r) = true) (h15 : s'.gpr .x24 = s.gpr .x24) :
    OS p D σ κ r s' := by
  simp only [ofam, Bool.and_eq_true] at hc
  have L := h.k.lay
  exact ⟨h.k.step hP hc.1.1, Fam.keep L hP hc.1.2 h.z, HFam.keep L hP hc.2 h.h, (L.keepBytes hP hs).trans h.sig,
    h15.trans h.x24⟩

/-- What the signature needs of the layout. -/
def oChk (p : Params) : Bool :=
  copyChk (sgR p) (sgW p) (.x23, 0) (sc oCT) (cLen p) && ofam p [((.x23, 0), cLen p)] &&
    (List.range p.ℓ).all (fun r => rwChk (sgR p) (sgW p) (yP p r) 1024 (.x23, sigZ p r) (zLen p) &&
      ofam p [((.x23, sigZ p r), zLen p)] && keepB (sgR p) (sgW p) [((.x23, sigZ p r), zLen p)] (.x23, 0) (cLen p + zLen p * r)) &&
    rwChk (sgR p) (sgW p) (hP 0) (256 * p.k * 4) (.x23, sigH p) (p.ω + p.k) &&
    decide ((p.ω, p.k) ∈ hintParams) && decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) &&
    decide (zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) && decide (p.sigLen = cLen p + zLen p * p.ℓ + (p.ω + p.k)) &&
    stChk p [((.x23, sigH p), p.ω + p.k)] &&
    keepB (sgR p) (sgW p) [((.x23, sigH p), p.ω + p.k)] (.x23, 0) (cLen p + zLen p * p.ℓ)

theorem oChk_ok {p : Params} (h : Ok3 p) : oChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (CTv p σ κ, (List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))

section
variable {P : Prims} {D : Nat} (hPO : PrimsOk P D) {p : Params} (hc : oChk p = true) {σ : State} {κ : Nat}
include hc

omit hPO in
theorem outCopy_ok {s : State} (hk : St p D σ s) (hct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ)
    (hz : Fam s (yBase p) p.ℓ (Zv p σ κ)) (hh : HFam s 5 p.k (Hv p σ κ)) (h15 : s.gpr .x24 = 1) :
    WP isa (copy (.x23, 0) (sc oCT) (cLen p)) s fun s1 =>
      OS p D σ κ 0 s1 ∧ ∀ f, HFam s 5 p.k f → HFam s1 5 p.k f := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, c0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.lay
  refine WP.mono (copy_ok L cc) fun s1 ⟨hP1, hcs1, hb1⟩ => ?_
  simp only [ofam, Bool.and_eq_true] at c0
  refine ⟨⟨hk.step hP1 c0.1.1, Fam.keep L hP1 c0.1.2 hz, HFam.keep L hP1 c0.2 hh, ?_,
    by rw [hcs1, h15]⟩, fun f h => HFam.keep L hP1 c0.2 h⟩
  rw [Nat.mul_zero, Nat.add_zero, hP1.pa (by decide), hb1, hct]
  simp [zEnc]

include hPO in
theorem packZ_ok {r : Nat} (hr : r < p.ℓ) {s : State} (h : OS p D σ κ r s) (hpass : PassV p σ κ) :
    WP isa (packZ P p r) s fun s' => OS p D σ κ (r + 1) s' ∧ ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, cz⟩, -⟩, -⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := cz r hr
  have Lh := h.k.lay
  have hzr := h.z r hr
  refine WP.mono (bpAt_ok hPO Lh hbp hzl c1 hzr.1 (inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)))
    fun s' ⟨hP', hcs', hb'⟩ => ?_
  have O' := h.step hP' c2 c3 (hcs')
  have c2' := c2
  simp only [ofam, Bool.and_eq_true] at c2'
  refine ⟨⟨O'.k, O'.z, O'.h, ?_, O'.x24⟩, fun f hf => HFam.keep Lh hP' c2'.2 hf⟩
  rw [Nat.mul_succ, ← Nat.add_assoc, VG.Proof.MlKem.bytesAt_add, O'.sig, pa_add, Nat.zero_add,
    hP'.pa (r14_bases _), hb', hzr.2, zEnc, zEnc, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.append_assoc]

omit hc in
theorem hones_ok {s : State} (h : OS p D σ κ p.ℓ s) (hpass : PassV p σ κ) :
    hintOnes (hintAt s.mem (pa s (Impl.MlDsa.AArch64.Sign.hP 0)) p.k) ≤ p.ω := by
  rw [hintAt_of (f := Hv p σ κ) fun i hi => by
      have := h.h i hi; rwa [pS_hint] at this,
    hintOnes_map]
  exact hpass.2.2.2

include hPO in
theorem hpack_ok {s : State} (h2 : OS p D σ κ p.ℓ s) (hpass : PassV p σ κ) :
    WP isa (hintBitPackAt P (Impl.MlDsa.AArch64.Sign.hP 0) (256 * p.k) p.ω (.x23, sigH p) (p.ω + p.k)) s fun s' =>
      St p D σ s' ∧ bytesAt s'.mem (pa s' (.x23, 0)) p.sigLen = sigV p σ κ ∧ s'.gpr .x24 = 1 := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, ch⟩, hhp⟩, -⟩, -⟩, hsl⟩, ci⟩, ck⟩ := hc
  have L2 := h2.k.lay
  refine WP.mono (hbpAt_ok hPO L2 hhp ch (hones_ok h2 hpass)) fun s3 ⟨hP3, hcs3, hb3⟩ =>
    ⟨h2.k.step hP3 ci, ?_, by rw [hcs3, h2.x24]⟩
  rw [hsl, VG.Proof.MlKem.bytesAt_add, L2.keepBytes hP3 ck, h2.sig, hP3.pa (by decide), pa_add, Nat.zero_add,
    show cLen p + zLen p * p.ℓ = sigH p from rfl, hb3, hintAt_of (f := Hv p σ κ) fun i hi => by
        have := h2.h i hi; rwa [pS_hint] at this]
  simp only [sigV, sigOf, sigEncode, zEnc, List.map_map, List.flatMap_map]
  rfl

include hPO in
theorem output_ok {s : State} (hk : St p D σ s) (hct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ)
    (hz : Fam s (yBase p) p.ℓ (Zv p σ κ)) (hh : HFam s 5 p.k (Hv p σ κ)) (hpass : PassV p σ κ)
    (h15 : s.gpr .x24 = 1) :
    WP isa (output P p) s fun s' => St p D σ s' ∧ bytesAt s'.mem (pa s' (.x23, 0)) p.sigLen = sigV p σ κ ∧
      s'.gpr .x24 = 1 := by
  unfold output
  refine WP.seq (WP.mono (outCopy_ok hc hk hct hz hh h15) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun r => OS p D σ κ r) p.ℓ 0
    (fun r _ hr s h => WP.mono (packZ_ok hPO hc (by omega) h hpass) fun _ h => h.1) s1 h1.1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact hpack_ok hPO hc h2 hpass

end

end VG.Proof.MlDsa.AArch64.Sign.Output
